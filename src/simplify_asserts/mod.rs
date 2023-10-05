use egg::{
    BackoffScheduler, CostFunction, EGraph, Extractor, Id, RecExpr, Rewrite, Runner,
    SimpleScheduler,
};
use itertools::Itertools;
use log::debug;
use smt2parser::concrete as ast;
use std::{
    collections::{hash_map::Entry, HashMap, HashSet},
    time::Duration,
};

mod language;
use language::EggSmt;

mod analysis;
use analysis::Eval;

mod cost;
use cost::EggSmtCostFn;

mod rewrite_rules;
use rewrite_rules::{expansion_rules, reduction_rules};

pub(crate) mod ast_to_recexpr;
use ast_to_recexpr::ast_to_recexpr;

pub(crate) mod recexpr_to_ast;
use recexpr_to_ast::recexpr_to_ast;

fn scan_variables(recexpr: &RecExpr<EggSmt>, variables: &mut HashSet<EggSmt>) {
    for node in recexpr.as_ref() {
        if let EggSmt::Symbol(_) = node {
            variables.insert(node.clone());
        }
    }
}

pub fn simplify_asserts(
    commands: Vec<ast::Command>,
    time_limit: f64,
    node_limit: usize,
    iters: usize,
) -> Vec<ast::Command> {
    let simple_assigns = simplify_assigns(&commands, time_limit * 0.5, node_limit, iters);
    let time_limit = time_limit * 0.5;

    // Get the E-Graph
    let mut egraph = EGraph::<EggSmt, Eval>::default();

    // Fill it with asserts
    let mut lookup: HashMap<&ast::Term, Id> = HashMap::default();
    let mut original_terms: HashMap<Id, ast::Term> = HashMap::default();
    let mut original_costs: HashMap<Id, usize> = HashMap::default();
    let mut original_recexprs: HashMap<Id, RecExpr<EggSmt>> = HashMap::default();
    let mut variables: HashSet<EggSmt> = HashSet::default();
    for command in &commands {
        if let ast::Command::Assert { term } = command {
            if simple_assigns.contains_key(term) {
                let (lhs, rhs) = simple_assigns.get(term).unwrap();
                scan_variables(lhs, &mut variables);
                scan_variables(rhs, &mut variables);
                let lhs_id = egraph.add_expr(lhs);
                let rhs_id = egraph.add_expr(rhs);
                if lhs_id != rhs_id {
                    egraph.union(lhs_id, rhs_id);
                }
                continue;
            }

            // Parse and add to EGraph
            let recexpr = ast_to_recexpr(term);
            scan_variables(&recexpr, &mut variables);
            let id = egraph.add_expr(&recexpr);

            // Add to lookup so we can easily pull out simplified version later
            lookup.insert(term, id);
            original_terms.insert(id, term.clone());
            original_costs.insert(id, EggSmtCostFn.cost_rec(&recexpr));
            original_recexprs.insert(id, recexpr.clone());
        }
    }

    // Run expansion + reduction
    let mut rules: Vec<Rewrite<EggSmt, Eval>> = vec![];
    rules.extend(expansion_rules());
    rules.extend(reduction_rules());
    let runner = Runner::default()
        .with_egraph(egraph)
        .with_iter_limit(iters)
        .with_node_limit(node_limit)
        .with_time_limit(Duration::from_secs_f64(time_limit * 0.5))
        .with_scheduler(BackoffScheduler::default())
        .run(&rules);
    let used_nodes = runner.egraph.total_size();
    let mut egraph = runner.egraph;

    // Run with only reduction rules and bcp
    let true_id = egraph.add(EggSmt::Boolean(true));
    let extractor = Extractor::new(&egraph, EggSmtCostFn);
    let not_propagated: HashMap<Id, RecExpr<EggSmt>> = lookup
        .values()
        .filter_map(|id| {
            let (_, best) = extractor.find_best(*id);
            let nodes = best.as_ref();
            if nodes[nodes.len() - 1] == EggSmt::Boolean(true) {
                None
            } else {
                Some((*id, best))
            }
        })
        .collect();
    let mut non_units: HashSet<Id> = not_propagated.keys().copied().collect();
    let runner = Runner::default()
        .with_egraph(egraph)
        .with_iter_limit(100)
        .with_node_limit(used_nodes + 1000)
        .with_time_limit(Duration::from_secs_f64(time_limit * 0.5))
        .with_scheduler(SimpleScheduler)
        .with_hook(move |runner| {
            let extractor = Extractor::new(&runner.egraph, EggSmtCostFn);
            let mut to_propagate = vec![];
            for id in non_units.iter() {
                let (_cost, best) = extractor.find_best(*id);
                let nodes = best.as_ref();
                if let EggSmt::Symbol(_) = nodes[nodes.len() - 1] {
                    debug!("BCP known true: {}", best);
                    debug!("BCP    original: {}", original_terms.get(id).unwrap());
                    to_propagate.push(*id);
                }
                if let EggSmt::Not([n]) = nodes[nodes.len() - 1] {
                    if let EggSmt::Symbol(_) = nodes[usize::from(n)] {
                        debug!("BCP known true: {}", best);
                        debug!("BCP    original: {}", original_terms.get(id).unwrap());
                        to_propagate.push(*id);
                    }
                }
            }
            let mut need_rebuild = false;
            for id in to_propagate.iter() {
                runner.egraph.union(*id, true_id);
                non_units.remove(id);
                need_rebuild = true;
            }
            if need_rebuild {
                runner.egraph.rebuild();
            }
            Ok(())
        })
        .run(&reduction_rules());
    let mut egraph = runner.egraph;

    // Check if we created a contradiction
    let cont = EggSmt::Contradiction(language::Contradiction {
        name: "Made by analysis.rs".to_string(),
    });
    let recexpr_cont = RecExpr::from(vec![cont]);
    let found_cont = egraph.lookup_expr(&recexpr_cont).is_some();

    // Early out, just copy over non-assert commands and put one assert false
    let false_ast = ast::Term::QualIdentifier(ast::QualIdentifier::Simple {
        identifier: ast::Identifier::Simple {
            symbol: ast::Symbol("false".to_string()),
        },
    });
    if found_cont {
        let mut new_commands: Vec<ast::Command> = vec![];
        let mut asserted_false = false;
        for command in commands {
            match command {
                ast::Command::Assert { term: _ } => {
                    if !asserted_false {
                        new_commands.push(ast::Command::Assert {
                            term: false_ast.clone(),
                        });
                        asserted_false = true;
                    }
                }
                other => new_commands.push(other),
            }
        }
        return new_commands;
    }

    // Figure out our variable renaming scheme
    //TODO: make this deterministic from run to
    let mut renaming: HashMap<EggSmt, EggSmt> = HashMap::default();
    let mut chosen_names: HashMap<Id, EggSmt> = HashMap::default();
    for variable in variables {
        let id = egraph.add(variable.clone());
        match chosen_names.entry(id) {
            Entry::Vacant(v) => {
                v.insert(variable);
            }
            Entry::Occupied(o) => {
                let chosen_name = o.get();
                if *chosen_name != variable {
                    renaming.insert(variable, chosen_name.clone());
                }
            }
        }
    }

    // Find the best version of each asserted term
    let extractor = Extractor::new(&egraph, EggSmtCostFn);
    let mut best_recexprs: HashMap<&ast::Term, RecExpr<EggSmt>> = HashMap::default();
    for (term, id) in lookup.iter() {
        let (cost, best) = extractor.find_best(*id);
        let best = if cost == *original_costs.get(id).unwrap() {
            original_recexprs.get(id).unwrap().clone()
        } else {
            best
        };
        let nodes = best.as_ref();
        let new_best = match nodes[nodes.len() - 1] {
            EggSmt::Boolean(true) => {
                if not_propagated.contains_key(id) {
                    not_propagated.get(id).unwrap().to_owned()
                } else {
                    best
                }
            }
            _ => best,
        };
        let new_best = rename_recexpr(&new_best, &renaming);
        best_recexprs.insert(term, new_best);
    }

    // Reconstruct the query

    let mut new_commands: Vec<ast::Command> = vec![];
    let mut equalities_injected = false;
    for command in &commands {
        let cmd = match command {
            ast::Command::Assert { term } => {
                // Once we see the first assert we can inject the variable equalities
                if !equalities_injected {
                    for (old, new) in renaming.iter() {
                        let will_swap = old.to_string() < new.to_string();
                        let (old, new) = if will_swap { (new, old) } else { (old, new) };
                        let nodes = vec![
                            old.clone(),
                            new.clone(),
                            EggSmt::Equal([egg::Id::from(0), egg::Id::from(1)]),
                        ];
                        let rec_eq = RecExpr::from(nodes);
                        let equality = ast::Command::Assert {
                            term: recexpr_to_ast(&rec_eq),
                        };
                        new_commands.push(equality);
                    }
                    // For booleans also add whether the value was true of false, if known
                    for (id, chosen_name) in chosen_names.iter() {
                        let (_, best) = extractor.find_best(*id);
                        let nodes = best.as_ref();
                        let last = nodes.last().unwrap();
                        if let EggSmt::Boolean(_) = last {
                            let nodes = vec![
                                chosen_name.clone(),
                                last.clone(),
                                EggSmt::Equal([egg::Id::from(0), egg::Id::from(1)]),
                            ];
                            let rec_eq = RecExpr::from(nodes);
                            let equality = ast::Command::Assert {
                                term: recexpr_to_ast(&rec_eq),
                            };
                            new_commands.push(equality);
                        }
                    }
                    equalities_injected = true;
                }

                let simple = if simple_assigns.contains_key(term) {
                    let (lhs, rhs) = simple_assigns.get(term).unwrap();
                    let will_swap = match (get_symbol(lhs), get_symbol(rhs)) {
                        (Some(l), Some(r)) => l < r,
                        (None, Some(_)) => true,
                        _ => false,
                    };
                    let (lhs, rhs) = if will_swap { (rhs, lhs) } else { (lhs, rhs) };
                    let lhs = rename_recexpr(lhs, &renaming);
                    let rhs = rename_recexpr(rhs, &renaming);
                    let lhs_term = recexpr_to_ast(&lhs);
                    let rhs_term = recexpr_to_ast(&rhs);

                    ast::Term::Application {
                        qual_identifier: ast::QualIdentifier::Simple {
                            identifier: ast::Identifier::Simple {
                                symbol: ast::Symbol("=".to_string()),
                            },
                        },
                        arguments: vec![lhs_term, rhs_term],
                    }
                } else {
                    let best = best_recexprs.get(term).unwrap();
                    let nodes = best.as_ref();
                    if let EggSmt::Boolean(b) = nodes[nodes.len() - 1] {
                        if b {
                            debug!("Rewritten to true: {}", term);
                            continue;
                        }
                    }
                    debug!("It was: {}", best);
                    recexpr_to_ast(best)
                };

                if *term == simple {
                    debug!("Remained the same: {}", simple);
                } else {
                    debug!("Replaced: {}", term);
                    debug!("With:     {}", simple);
                }

                ast::Command::Assert { term: simple }
            }
            other => other.clone(),
        };

        new_commands.push(cmd);
    }

    new_commands.into_iter().unique().collect()
}

fn simplify_assigns(
    commands: &Vec<ast::Command>,
    time_limit: f64,
    node_limit: usize,
    iters: usize,
) -> HashMap<ast::Term, (RecExpr<EggSmt>, RecExpr<EggSmt>)> {
    // Get the E-Graph
    let mut egraph = EGraph::<EggSmt, Eval>::default();

    // Fill it with asserts
    let mut assigns: HashMap<&ast::Term, (Id, Id)> = HashMap::default();
    let mut original_costs: HashMap<Id, usize> = HashMap::default();
    let mut original_recexprs: HashMap<Id, RecExpr<EggSmt>> = HashMap::default();
    for command in commands {
        if let smt2parser::concrete::Command::Assert { term } = command {
            // Catch commands of the form `(assert (= <thing> <other>))`
            if let ast::Term::Application {
                qual_identifier,
                arguments,
            } = term
            {
                if qual_identifier.to_string() == "=" {
                    if arguments.len() != 2 {
                        panic!("Bad assert: {}", &term);
                    }
                    let lhs_rec = ast_to_recexpr(&arguments[0]);
                    let rhs_rec = ast_to_recexpr(&arguments[1]);
                    let lhs_id = egraph.add_expr(&lhs_rec);
                    let rhs_id = egraph.add_expr(&rhs_rec);
                    assigns.insert(term, (lhs_id, rhs_id));
                    original_costs.insert(lhs_id, EggSmtCostFn.cost_rec(&lhs_rec));
                    original_costs.insert(rhs_id, EggSmtCostFn.cost_rec(&rhs_rec));
                    original_recexprs.insert(lhs_id, lhs_rec.clone());
                    original_recexprs.insert(rhs_id, rhs_rec.clone());
                }
            }
        }
    }

    // Run expansion + reduction
    let mut rules: Vec<Rewrite<EggSmt, Eval>> = vec![];
    rules.extend(expansion_rules());
    rules.extend(reduction_rules());
    let runner = Runner::default()
        .with_egraph(egraph)
        .with_iter_limit(iters)
        .with_node_limit(node_limit)
        .with_time_limit(Duration::from_secs_f64(time_limit * 0.75))
        .with_scheduler(BackoffScheduler::default())
        .run(&rules);
    let used_nodes = runner.egraph.total_size();
    let egraph = runner.egraph;

    // Run with only reduction
    let runner = Runner::default()
        .with_egraph(egraph)
        .with_iter_limit(100)
        .with_node_limit(used_nodes + 1_000)
        .with_time_limit(Duration::from_secs_f64(time_limit * 0.25))
        .with_scheduler(SimpleScheduler)
        .run(&reduction_rules());
    let egraph = runner.egraph;

    // Get the best version of the assignment asserts
    let mut simple_assigns: HashMap<ast::Term, (RecExpr<EggSmt>, RecExpr<EggSmt>)> =
        HashMap::default();
    let extractor = Extractor::new(&egraph, EggSmtCostFn);
    for term in assigns.keys() {
        let (lhs_id, rhs_id) = assigns.get(term).unwrap();
        let (cost, lhs) = extractor.find_best(*lhs_id);
        let lhs = if cost == *original_costs.get(lhs_id).unwrap() {
            original_recexprs.get(lhs_id).unwrap().clone()
        } else {
            lhs
        };
        let (cost, rhs) = extractor.find_best(*rhs_id);
        let rhs = if cost == *original_costs.get(rhs_id).unwrap() {
            original_recexprs.get(rhs_id).unwrap().clone()
        } else {
            rhs
        };
        simple_assigns.insert((*term).clone(), (lhs, rhs));
    }

    simple_assigns
}

fn get_symbol(recexpr: &RecExpr<EggSmt>) -> Option<String> {
    match recexpr.as_ref().last().unwrap() {
        EggSmt::Symbol(s) => Some(s.to_string()),
        _ => None,
    }
}

fn rename_recexpr(
    recexpr: &RecExpr<EggSmt>,
    renaming: &HashMap<EggSmt, EggSmt>,
) -> RecExpr<EggSmt> {
    let nodes: Vec<EggSmt> = recexpr
        .as_ref()
        .iter()
        .map(|e| match e {
            EggSmt::Symbol(_) => {
                if renaming.contains_key(e) {
                    renaming.get(e).unwrap().clone()
                } else {
                    e.clone()
                }
            }
            _ => e.clone(),
        })
        .collect();
    RecExpr::from(nodes)
}

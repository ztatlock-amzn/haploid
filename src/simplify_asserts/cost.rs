use super::language::EggSmt;
use egg::{Id, Language};
//use lazy_static::lazy_static;
//use regex::Regex;

pub struct EggSmtCostFn;
impl egg::CostFunction<EggSmt> for EggSmtCostFn {
    type Cost = usize;
    fn cost<C>(&mut self, enode: &EggSmt, mut costs: C) -> Self::Cost
    where
        C: FnMut(Id) -> Self::Cost,
    {
        let base_cost = 1;
        let op_cost = match enode {
            // Attributes get a free pass
            EggSmt::Attribute(_) => 0,

            // Contradictions need to always be extracted if present
            EggSmt::Contradiction(_) => 0,

            // Make symbols more expensive than constants
            EggSmt::Symbol(_) => 2 * base_cost,

            // We don't want these forms
            EggSmt::Forall(_) => 3 * base_cost,
            EggSmt::Let(_) => 3 * base_cost,
            EggSmt::Exists(_) => 3 * base_cost,

            // Everything else
            _ => base_cost,
        };
        enode.fold(op_cost, |sum, i| sum + costs(i))
    }
}

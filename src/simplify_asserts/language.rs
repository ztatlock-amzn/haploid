use egg::{define_language, Id, Symbol};
use lazy_static::lazy_static;
use regex::Regex;

// We never want to use the generated parser that comes with egg's `define_language!` macro
//   for parsing the actual query,
//   but we do want to use the generated types and the parser for the rewrite macro.
// The language parser would break anyway.
//
// Instead we use smt2parser to do the parsing,
//   then transform that ast to RecExpr's of the below
// language

// The following line is noted in documentation, if it is no longer line 16 please update
// documentation/adding_an_smt_function.md
define_language! {
    pub enum EggSmt {
        // Atoms
        Numeral(smt2parser::Numeral),
        Decimal(smt2parser::Decimal),
        Hexadecimal(WrappedHexadecimal),
        Binary(WrappedBinary),
        Boolean(bool),
        Symbol(Symbol),
        String(String),

        // Boolean Operators
        "and" = And([Id; 2]),
        "or" = Or([Id; 2]),
        "=>" = Implies([Id; 2]),
        "not" = Not([Id; 1]),
        "ite" = IfThenElse([Id; 3]),

        // String Operators
        "str.++" = StrConcat([Id; 2]),
        "str.contains" = StrContains([Id; 2]),
        "str.in_re" = StrInRe([Id; 2]),
        "str.len" = StrLen([Id; 1]),
        "str.prefixof" = StrPrefixof([Id; 2]),
        "str.substr" = StrSubstr([Id; 3]),
        "str.suffixof" = StrSuffixof([Id; 2]),
        "str.to_re" = StrToRe([Id; 1]),

        // Regex Operators
        "re.*" = ReStar([Id; 1]),
        "re.++" = ReConcat([Id; 2]),
        "re.union" = ReUnion([Id; 2]),

        // Math Operators
        "+" = Add([Id; 2]),
        "-" = Sub([Id; 2]),
        "*" = Mul([Id; 2]),
        "/" = Div([Id; 2]),
        "div" = IntDiv([Id; 2]),
        "-" = Neg([Id; 1]),

        // Comparators
        "=" = Equal([Id; 2]),
        "<" = LessThan([Id; 2]),
        "<=" = LessThanEqual([Id; 2]),
        ">" = GreaterThan([Id; 2]),
        ">=" = GreaterThanEqual([Id; 2]),

        // Binary Operators
        "bvand" = BinaryAnd([Id; 2]),

        // Weird forms that make auto parsing fail
        "!" = Attribute(Vec<Id>), // attribute is encoded as 1 id for the body, then 2*n pairs for the attributes
        AttributeValue(WrappedAttributeValue), // Just store the attribute values
        "forall" = Forall(Vec<Id>), // forall is encoded as 2*n Ids for the sym, type pairs and 1 id for the body
        "let" = Let(Vec<Id>), // let is similar to forall
        "exists" = Exists(Vec<Id>), // exists is similar to forall
        "_" = Identifier(Vec<Id>), // identifier is encoded as 1 Id for the symbol, then n Ids for the indices
        // Due to the parser requirements we can't just have a language element with just a Vec<Id>,
        //   so give it a name
        "identifierapplication" = IdentifierApplication(Vec<Id>),
        // application catches all normal application forms
        Application(Symbol, Vec<Id>),

        // This is a poison value used to indicate that a contradiction was found during simplification
        Contradiction(Contradiction),
    }
}

// +---------------------------------------------------------------------------------------------+
// | WrappedHexadecimal                                                                          |
// +---------------------------------------------------------------------------------------------+
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub struct WrappedHexadecimal {
    pub hex: smt2parser::Hexadecimal,
}

#[derive(Debug)]
pub struct ParseWrappedHexadecimalError(String);

impl std::fmt::Display for WrappedHexadecimal {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "#x")?;
        for digit in &self.hex {
            write!(f, "{:x}", digit)?;
        }
        Ok(())
    }
}

impl std::str::FromStr for WrappedHexadecimal {
    type Err = ParseWrappedHexadecimalError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        lazy_static! {
            static ref RE: Regex = Regex::new(r"^#[xX]([0-9a-fA-F]+)$").unwrap();
        }
        match RE.captures(s) {
            Some(cap) => Ok(WrappedHexadecimal {
                hex: cap
                    .get(1)
                    .unwrap()
                    .as_str()
                    .chars()
                    .map(|c| c.to_digit(16).unwrap() as u8)
                    .collect(),
            }),
            None => Err(ParseWrappedHexadecimalError(format!(
                "Invalid hex literal: '{}'",
                s
            ))),
        }
    }
}

// +---------------------------------------------------------------------------------------------+
// | WrappedBinary                                                                               |
// +---------------------------------------------------------------------------------------------+

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub struct WrappedBinary {
    pub bin: smt2parser::Binary,
}

#[derive(Debug)]
pub struct ParseWrappedBinaryError(String);

impl std::fmt::Display for WrappedBinary {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "#b")?;
        for digit in &self.bin {
            if *digit {
                write!(f, "1")?;
            } else {
                write!(f, "0")?;
            }
        }
        Ok(())
    }
}

impl std::str::FromStr for WrappedBinary {
    type Err = ParseWrappedBinaryError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        lazy_static! {
            static ref RE: Regex = Regex::new("^#[bB]([01]+)$").unwrap();
        }
        match RE.captures(s) {
            Some(cap) => Ok(WrappedBinary {
                bin: cap
                    .get(1)
                    .unwrap()
                    .as_str()
                    .chars()
                    .map(|c| match c {
                        '0' => false,
                        '1' => true,
                        _ => unreachable!(),
                    })
                    .collect(),
            }),
            None => Err(ParseWrappedBinaryError(format!(
                "Invalid binary literal: '{}'",
                s
            ))),
        }
    }
}

// +---------------------------------------------------------------------------------------------+
// | WrappedAttributeValue                                                                       |
// +---------------------------------------------------------------------------------------------+

#[derive(Debug, PartialEq, Eq, Hash, Clone)]
pub struct WrappedAttributeValue {
    pub val: smt2parser::concrete::AttributeValue,
}

#[derive(Debug)]
pub struct ParseWrappedAttributeValueError(String);

impl std::fmt::Display for WrappedAttributeValue {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.val)?;
        Ok(())
    }
}

impl std::str::FromStr for WrappedAttributeValue {
    type Err = ParseWrappedAttributeValueError;

    fn from_str(_: &str) -> Result<Self, Self::Err> {
        panic!("The auto-generated parser should not be used");
    }
}

impl PartialOrd for WrappedAttributeValue {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        self.val.to_string().partial_cmp(&other.val.to_string())
    }
}

impl Ord for WrappedAttributeValue {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.val.to_string().cmp(&other.val.to_string())
    }
}

// +---------------------------------------------------------------------------------------------+
// | Contradiction                                                                               |
// +---------------------------------------------------------------------------------------------+

#[derive(Debug, PartialEq, Eq, Hash, Clone)]
pub struct Contradiction {
    pub name: String,
}

#[derive(Debug)]
pub struct ParseContradictionError(String);

impl std::fmt::Display for Contradiction {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "::THE POISON VALUE 'CONTRADICTION' HAS BEEN GENERATED::")?;
        Ok(())
    }
}

impl std::str::FromStr for Contradiction {
    type Err = ParseContradictionError;

    fn from_str(_: &str) -> Result<Self, Self::Err> {
        panic!("The auto-generated parser should not be used");
    }
}

impl PartialOrd for Contradiction {
    fn partial_cmp(&self, _other: &Self) -> Option<std::cmp::Ordering> {
        None
    }
}

impl Ord for Contradiction {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        (&self).cmp(&other)
    }
}

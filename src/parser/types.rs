use std::{
    collections::{HashMap, VecDeque},
    fmt::Display,
};

use tabled::Tabled;

use crate::model::types::{NonTerminal, Symbol, Terminal};

#[derive(Debug, Clone)]
pub enum ParsingAction {
    Production(usize), // index of the production to apply
    #[allow(dead_code)]
    Error, // empty cell = parsing error
}

pub type LLParsingTable = HashMap<(NonTerminal, Terminal), Vec<ParsingAction>>;

#[derive(Debug, Clone)]
pub struct LRParsingTable {
    pub actions: HashMap<(usize, Symbol), Vec<LRAction>>,
}

#[derive(Debug, Clone)]
pub enum LRAction {
    /// Go to state at index N
    Shift(usize),

    /// Reduce using production at index N
    /// (LHS, RHS, production_index)
    Reduce(NonTerminal, Vec<Symbol>, usize),

    Accept,
}

impl Display for LRAction {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Shift(n) => write!(f, "s{}", n),
            Self::Reduce(lhs, rhs, _) => write!(
                f,
                "r({} -> {})",
                lhs,
                rhs.iter()
                    .map(|s| s.to_string())
                    .collect::<Vec<_>>()
                    .join("")
            ),
            Self::Accept => write!(f, "acc"),
        }
    }
}

#[derive(Debug)]
pub enum ParseResult {
    Accept,
    Reject(String),
}

impl Display for ParseResult {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Accept => write!(f, "Accepted"),
            Self::Reject(s) => write!(f, "{}", s),
        }
    }
}

#[derive(Debug, Clone)]
pub struct ParseStep {
    pub stack: Vec<String>,
    pub input: VecDeque<Terminal>,
    pub action: String,
}

#[derive(Tabled)]
pub struct TraceRow {
    #[tabled(rename = "Step")]
    pub step: usize,

    #[tabled(rename = "Stack")]
    pub stack: String,

    #[tabled(rename = "Input")]
    pub input: String,

    #[tabled(rename = "Action")]
    pub action: String,
}

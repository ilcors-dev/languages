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

pub type ParsingTable = HashMap<(NonTerminal, Terminal), Vec<ParsingAction>>;

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
    pub stack: Vec<Symbol>,
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

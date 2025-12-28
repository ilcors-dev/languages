use tabled::Table;

use crate::{model::types::Symbol, parser::types::LRParsingTable};

pub trait TableGenerator {
    /// Converts the internal automaton into a standard LR Parsing Table
    fn build_parsing_table(&self) -> Result<LRParsingTable, String>;

    fn to_printable_table(&self) -> Option<Table>;
}

pub trait LRItem {
    /// Advances the cursor (dot) position by one
    fn advance_cursor(&self) -> Self;

    /// Peeks the symbol after the cursor (dot) position
    fn symbol_after_cursor(&self) -> Option<&Symbol>;
}

use tabled::Table;

pub trait TableGenerator<TableType> {
    /// Converts the internal automaton into a standard LR Parsing Table
    fn build_parsing_table(&self) -> Result<TableType, String>;

    fn to_printable_table(&self) -> Option<Table>;
}

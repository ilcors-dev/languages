use crate::model::types::Symbol;

pub trait LRItem {
    /// Advances the cursor (dot) position by one
    fn advance_cursor(&self) -> Self;

    /// Peeks the symbol after the cursor (dot) position
    fn symbol_after_cursor(&self) -> Option<&Symbol>;
}

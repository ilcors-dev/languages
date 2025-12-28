use std::{
    collections::{HashMap, HashSet},
    fmt::Display,
};

use crate::model::{
    grammar::Grammar,
    types::{NonTerminal, Symbol},
};

trait LRItem {
    /// Advances the cursor (dot) position by one
    fn advance_cursor(&mut self);

    fn symbol_after_cursor(&self) -> Option<&Symbol>;
}

pub trait LRBuilder {
    /// Builds the LR parsing automaton (states and transitions)
    fn build(&mut self) -> Result<(), String>;

    ///
    /// For example:
    /// S -> AB
    /// A -> a | e
    /// B -> b
    ///
    /// CLOSURE(S -> • AB) will return the set of items
    /// S -> • AB
    /// A -> • a
    /// A -> • e
    fn closure(&self, item: LR0Item) -> HashSet<LR0Item>;

    /// The GOTO function for LR parsers computes the set of items reachable from a given set of
    /// items
    /// For example:
    /// S -> AB
    /// A -> a | e
    /// B -> b
    ///
    /// Given the current state
    /// S -> A • B
    ///
    /// GOTO(I, B) will return the set of items
    /// S -> A B •
    /// B -> • b
    fn goto(&self, items: HashSet<LR0Item>, symbol: &Symbol) -> HashSet<LR0Item>;
}

#[derive(Debug, Clone)]
struct LR0State {
    items: HashSet<LR0Item>,
}

#[derive(Debug, Clone, PartialEq, PartialOrd, Ord, Eq, Hash)]
struct LR0Item {
    lhs: NonTerminal,

    /// Production associated with the LR(0) item
    production: Vec<Symbol>,

    /// Position of the cursor (dot) in the production
    cursor_pos: usize,
}

impl Display for LR0Item {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut production_str = String::new();

        for (i, symbol) in self.production.iter().enumerate() {
            if i == self.cursor_pos {
                production_str.push_str("• ");
            }
            production_str.push_str(&format!("{} ", symbol));
        }

        if self.cursor_pos == self.production.len() {
            production_str.push_str("•");
        }

        write!(f, "{} -> {}", self.lhs, production_str.trim())
    }
}

impl LRItem for LR0Item {
    fn advance_cursor(&mut self) {
        if self.cursor_pos < self.production.len() {
            self.cursor_pos += 1;
        }
    }

    fn symbol_after_cursor(&self) -> Option<&Symbol> {
        if self.cursor_pos >= self.production.len() {
            return None;
        }

        self.production.iter().nth(self.cursor_pos)
    }
}

pub struct LR0Builder<'a> {
    grammar: &'a Grammar,
    states: HashMap<usize, LR0State>,
    transitions: HashMap<(usize, Symbol), usize>,
}

impl LR0Builder<'_> {
    pub fn new<'a>(grammar: &'a Grammar) -> LR0Builder<'a> {
        LR0Builder {
            grammar,
            states: HashMap::new(),
            transitions: HashMap::new(),
        }
    }
}

impl<'a> LRBuilder for LR0Builder<'a> {
    fn build(&mut self) -> Result<(), String> {
        let start = LR0Item {
            lhs: NonTerminal('Z'),
            production: vec![Symbol::NonTerminal(self.grammar.s)],
            cursor_pos: 0,
        };

        let items = self.closure(start);

        self.states.insert(0, LR0State { items });

        let mut worklist = self.states.keys().cloned().collect::<Vec<usize>>();

        while let Some(state_idx) = worklist.pop() {
            let current_state = self.states.get(&state_idx).unwrap().clone();

            for symbol_after_cursor in current_state
                .items
                .iter()
                .filter_map(|item| item.symbol_after_cursor())
            {
                let new_items = self.goto(current_state.items.clone(), symbol_after_cursor);

                if new_items.is_empty() {
                    continue;
                }

                let new_state_idx = if let Some((idx, _)) = self
                    .states
                    .iter()
                    .find(|(_, state)| state.items == new_items)
                {
                    *idx
                } else {
                    let new_idx = self.states.len();

                    self.states.insert(new_idx, LR0State { items: new_items });

                    worklist.push(new_idx);

                    new_idx
                };

                self.transitions
                    .insert((state_idx, *symbol_after_cursor), new_state_idx);
            }
        }

        Ok(())
    }

    fn goto(&self, items: HashSet<LR0Item>, symbol: &Symbol) -> HashSet<LR0Item> {
        let mut goto_set = HashSet::new();

        for item in items.iter() {
            if item.symbol_after_cursor() == Some(&symbol) {
                let mut advanced_item = item.clone();
                advanced_item.advance_cursor();

                for closure_item in self.closure(advanced_item).into_iter() {
                    goto_set.insert(closure_item);
                }
            }
        }

        goto_set
    }

    fn closure(&self, item: LR0Item) -> HashSet<LR0Item> {
        let mut closure_set = HashSet::new();
        closure_set.insert(item);

        let mut added = true;

        while added {
            added = false;

            let curr_items = closure_set.clone();

            for item in curr_items.iter() {
                if let Some(Symbol::NonTerminal(nt)) = item.symbol_after_cursor() {
                    let productions = self.grammar.productions.get(nt);

                    if productions.is_none() {
                        continue;
                    }

                    for production in productions.unwrap().alternatives.iter() {
                        let new_item = LR0Item {
                            lhs: *nt,
                            production: production.clone(),
                            cursor_pos: 0,
                        };

                        if !closure_set.contains(&new_item) {
                            closure_set.insert(new_item);
                            added = true;
                        }
                    }
                }
            }
        }

        closure_set
    }
}

impl Display for LR0Builder<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        writeln!(f, "LR(0) States:")?;

        for (state_idx, state) in self.states.iter() {
            writeln!(f, "State {}:", state_idx)?;

            for item in state.items.iter() {
                writeln!(f, "  {}", item)?;
            }

            writeln!(f)?;
        }

        writeln!(f, "LR(0) Transitions:")?;

        for ((from_state, symbol), to_state) in self.transitions.iter() {
            writeln!(
                f,
                "  From State {} --[{}]--> State {}",
                from_state, symbol, to_state
            )?;
        }

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use crate::model::types::Terminal;

    use super::*;

    #[test]
    fn lr0_item_should_advance_cursor_when_called() {
        // given
        let mut item = LR0Item {
            lhs: NonTerminal('S'),
            production: vec![
                Symbol::NonTerminal(NonTerminal('A')),
                Symbol::Terminal(Terminal::Char('a')),
            ],
            cursor_pos: 0,
        };

        // when / then
        item.advance_cursor();
        assert_eq!(
            item.symbol_after_cursor(),
            Some(&Symbol::Terminal(Terminal::Char('a')))
        );

        // when / then
        item.advance_cursor();
        assert_eq!(item.symbol_after_cursor(), None);
    }

    #[test]
    fn lr0_item_should_peek_next_item() {
        // given
        let item = LR0Item {
            lhs: NonTerminal('S'),
            production: vec![
                Symbol::NonTerminal(NonTerminal('A')),
                Symbol::Terminal(Terminal::Char('a')),
            ],
            cursor_pos: 0,
        };

        // when / then
        assert_eq!(
            item.symbol_after_cursor(),
            Some(&Symbol::NonTerminal(NonTerminal('A')))
        );
    }

    #[test]
    fn lr0_item_should_return_none_when_cursor_at_end() {
        // given
        let item = LR0Item {
            lhs: NonTerminal('S'),
            production: vec![
                Symbol::NonTerminal(NonTerminal('A')),
                Symbol::Terminal(Terminal::Char('a')),
            ],
            cursor_pos: 2,
        };

        // when / then
        assert_eq!(item.symbol_after_cursor(), None);
    }

    #[test]
    fn lr0_item_displays_cursor_at_proper_position() {
        // given
        let item = LR0Item {
            lhs: NonTerminal('S'),
            production: vec![
                Symbol::NonTerminal(NonTerminal('A')),
                Symbol::Terminal(Terminal::Char('a')),
            ],
            cursor_pos: 1,
        };

        // when
        let item_str = format!("{}", item);

        // then
        assert_eq!(item_str, "S -> A • a");
    }

    #[test]
    fn lr0_item_displays_cursor_at_end_properly() {
        // given
        let item = LR0Item {
            lhs: NonTerminal('S'),
            production: vec![
                Symbol::NonTerminal(NonTerminal('A')),
                Symbol::Terminal(Terminal::Char('a')),
            ],
            cursor_pos: 2,
        };

        // when
        let item_str = format!("{}", item);

        // then
        assert_eq!(item_str, "S -> A a •");
    }

    #[test]
    fn lr0_item_displays_cursor_at_start_properly() {
        // given
        let item = LR0Item {
            lhs: NonTerminal('S'),
            production: vec![
                Symbol::NonTerminal(NonTerminal('A')),
                Symbol::Terminal(Terminal::Char('a')),
            ],
            cursor_pos: 0,
        };

        // when
        let item_str = format!("{}", item);

        // then
        assert_eq!(item_str, "S -> • A a");
    }

    #[test]
    fn lr0_closure_computes_closure_correctly() {
        // given
        let template = "
            S->AB
            A->a|e
            B->b
        ";

        let grammar = Grammar::from_string(template.to_string()).unwrap();

        let lr0_builder = LR0Builder {
            grammar: &grammar,
            states: HashMap::new(),
            transitions: HashMap::new(),
        };

        let start_item = LR0Item {
            lhs: NonTerminal('S'),
            production: vec![
                Symbol::NonTerminal(NonTerminal('A')),
                Symbol::NonTerminal(NonTerminal('B')),
            ],
            cursor_pos: 0,
        };

        // when
        let closure_set = lr0_builder.closure(start_item);

        // then
        let expected_items: HashSet<LR0Item> = HashSet::from_iter(vec![
            LR0Item {
                lhs: NonTerminal('S'),
                production: vec![
                    Symbol::NonTerminal(NonTerminal('A')),
                    Symbol::NonTerminal(NonTerminal('B')),
                ],
                cursor_pos: 0,
            },
            LR0Item {
                lhs: NonTerminal('A'),
                production: vec![Symbol::Terminal(Terminal::Char('a'))],
                cursor_pos: 0,
            },
            LR0Item {
                lhs: NonTerminal('A'),
                production: vec![Symbol::Terminal(Terminal::Epsilon)],
                cursor_pos: 0,
            },
        ]);

        assert_eq!(closure_set, expected_items);
    }

    #[test]
    fn lr0_closure_returns_only_initial_item_when_no_non_terminal_after_cursor() {
        // given
        let template = "
            S->aB
            B->b
        ";

        let grammar = Grammar::from_string(template.to_string()).unwrap();

        let lr0_builder = LR0Builder {
            grammar: &grammar,
            states: HashMap::new(),
            transitions: HashMap::new(),
        };

        let start_item = LR0Item {
            lhs: NonTerminal('S'),
            production: vec![
                Symbol::Terminal(Terminal::Char('a')),
                Symbol::NonTerminal(NonTerminal('B')),
            ],
            cursor_pos: 0,
        };

        // when
        let closure_set = lr0_builder.closure(start_item.clone());

        // then
        let expected_items: HashSet<LR0Item> = HashSet::from_iter(vec![start_item]);

        assert_eq!(closure_set, expected_items);
    }

    #[test]
    fn lr0_goto_computes_goto_correctly() {
        // given
        let template = "
            S->AB
            A->a|e
            B->b
        ";

        let grammar = Grammar::from_string(template.to_string()).unwrap();

        let lr0_builder = LR0Builder {
            grammar: &grammar,
            states: HashMap::new(),
            transitions: HashMap::new(),
        };

        let start_item = LR0Item {
            lhs: NonTerminal('S'),
            production: vec![
                Symbol::NonTerminal(NonTerminal('A')),
                Symbol::NonTerminal(NonTerminal('B')),
            ],
            cursor_pos: 0,
        };

        let closure_set = lr0_builder.closure(start_item);

        // when
        let goto_set = lr0_builder.goto(closure_set, &Symbol::NonTerminal(NonTerminal('A')));

        // then
        let expected_items: HashSet<LR0Item> = HashSet::from_iter(vec![
            LR0Item {
                lhs: NonTerminal('S'),
                production: vec![
                    Symbol::NonTerminal(NonTerminal('A')),
                    Symbol::NonTerminal(NonTerminal('B')),
                ],
                cursor_pos: 1,
            },
            LR0Item {
                lhs: NonTerminal('B'),
                production: vec![Symbol::Terminal(Terminal::Char('b'))],
                cursor_pos: 0,
            },
        ]);

        assert_eq!(goto_set, expected_items);
    }

    #[test]
    fn lr0_goto_returns_empty_set_when_no_items_match() {
        // given
        let template = "
            S->AB
            A->a|e
            B->b
        ";

        let grammar = Grammar::from_string(template.to_string()).unwrap();

        let lr0_builder = LR0Builder {
            grammar: &grammar,
            states: HashMap::new(),
            transitions: HashMap::new(),
        };

        let start_item = LR0Item {
            lhs: NonTerminal('S'),
            production: vec![
                Symbol::NonTerminal(NonTerminal('A')),
                Symbol::NonTerminal(NonTerminal('B')),
            ],
            cursor_pos: 2,
        };

        let closure_set = lr0_builder.closure(start_item);

        // when
        let goto_set = lr0_builder.goto(closure_set, &Symbol::Terminal(Terminal::Char('a')));

        // then
        let expected_items: HashSet<LR0Item> = HashSet::new();

        assert_eq!(goto_set, expected_items);
    }

    #[test]
    fn lr0_builder_builds_states_and_transitions_correctly() {
        // given
        let template = "
            S->AB
            A->a
            B->b
        ";

        let grammar = Grammar::from_string(template.to_string()).unwrap();

        let mut lr0_builder = LR0Builder {
            grammar: &grammar,
            states: HashMap::new(),
            transitions: HashMap::new(),
        };

        // when
        lr0_builder.build().unwrap();

        // then
        assert_eq!(lr0_builder.states.len(), 6);
        assert_eq!(lr0_builder.transitions.len(), 5);
    }
}

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
    fn advance_cursor(&self) -> Self;

    /// Peeks the symbol after the cursor (dot) position
    fn symbol_after_cursor(&self) -> Option<&Symbol>;
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
    fn advance_cursor(&self) -> LR0Item {
        let mut new_item = self.clone();

        if new_item.cursor_pos < new_item.production.len() {
            new_item.cursor_pos += 1;
        }

        new_item
    }

    fn symbol_after_cursor(&self) -> Option<&Symbol> {
        if self.cursor_pos >= self.production.len() {
            return None;
        }

        self.production.iter().nth(self.cursor_pos)
    }
}

pub struct LR0Builder {
    states: HashMap<usize, LR0State>,
    transitions: HashMap<(usize, Symbol), usize>,
}

impl LR0Builder {
    pub fn new(grammar: &Grammar) -> LR0Builder {
        let mut states = HashMap::new();
        let mut transitions = HashMap::new();

        let start = LR0Item {
            lhs: NonTerminal('Z'),
            production: vec![Symbol::NonTerminal(grammar.s)],
            cursor_pos: 0,
        };

        let items = Self::closure(grammar, start);

        states.insert(0, LR0State { items });

        let mut worklist: Vec<usize> = states.keys().cloned().collect();

        while let Some(state_idx) = worklist.pop() {
            let items = if let Some(state) = states.get(&state_idx) {
                state.items.clone()
            } else {
                continue;
            };

            for symbol_after_cursor in items.iter().filter_map(|item| item.symbol_after_cursor()) {
                let new_items = Self::goto(grammar, items.clone(), symbol_after_cursor);

                if new_items.is_empty() {
                    continue;
                }

                let new_state_idx = if let Some((idx, _)) =
                    states.iter().find(|(_, state)| state.items == new_items)
                {
                    *idx
                } else {
                    let new_idx = states.len();

                    states.insert(new_idx, LR0State { items: new_items });

                    worklist.push(new_idx);

                    new_idx
                };

                transitions.insert((state_idx, *symbol_after_cursor), new_state_idx);
            }
        }

        LR0Builder {
            states,
            transitions,
        }
    }

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
    fn goto(grammar: &Grammar, items: HashSet<LR0Item>, symbol: &Symbol) -> HashSet<LR0Item> {
        let mut goto_set = HashSet::new();

        for item in items.iter() {
            if item.symbol_after_cursor() == Some(&symbol) {
                let advanced_item = item.advance_cursor();

                for closure_item in Self::closure(grammar, advanced_item).into_iter() {
                    goto_set.insert(closure_item);
                }
            }
        }

        goto_set
    }

    /// The CLOSURE function for LR parsers computes the production rules reachable from the item
    /// provided given its cursor position.
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
    fn closure(grammar: &Grammar, item: LR0Item) -> HashSet<LR0Item> {
        let mut closure_set = HashSet::new();
        closure_set.insert(item);

        let mut added = true;

        while added {
            added = false;

            let curr_items = closure_set.clone();

            for item in curr_items.iter() {
                if let Some(Symbol::NonTerminal(nt)) = item.symbol_after_cursor() {
                    let productions = grammar.productions.get(nt);

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

impl Display for LR0Builder {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        writeln!(f, "LR(0) States:")?;

        let mut states_sorted_by_key: Vec<(&usize, &LR0State)> =
            self.states.iter().collect::<Vec<(&usize, &LR0State)>>();

        states_sorted_by_key.sort_by_key(|(state_idx, _)| *state_idx);

        for (state_idx, state) in states_sorted_by_key.iter() {
            writeln!(f, "State {}:", state_idx)?;

            for item in state.items.iter() {
                writeln!(f, "  {}", item)?;
            }

            writeln!(f)?;
        }

        writeln!(f, "LR(0) Transitions:")?;

        let mut transitions_sorted: Vec<(&(usize, Symbol), &usize)> = self
            .transitions
            .iter()
            .collect::<Vec<(&(usize, Symbol), &usize)>>();

        transitions_sorted.sort_by_key(|((from_state, symbol), to_state)| {
            (*from_state, symbol.clone(), *to_state)
        });

        for ((from_state, symbol), to_state) in transitions_sorted.iter() {
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
            item.advance_cursor().symbol_after_cursor(),
            Some(&Symbol::Terminal(Terminal::Char('a')))
        );

        // when / then
        assert_eq!(
            item.advance_cursor().advance_cursor().symbol_after_cursor(),
            None
        );
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

        let start_item = LR0Item {
            lhs: NonTerminal('S'),
            production: vec![
                Symbol::NonTerminal(NonTerminal('A')),
                Symbol::NonTerminal(NonTerminal('B')),
            ],
            cursor_pos: 0,
        };

        // when
        let closure_set = LR0Builder::closure(&grammar, start_item);

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

        let start_item = LR0Item {
            lhs: NonTerminal('S'),
            production: vec![
                Symbol::Terminal(Terminal::Char('a')),
                Symbol::NonTerminal(NonTerminal('B')),
            ],
            cursor_pos: 0,
        };

        // when
        let closure_set = LR0Builder::closure(&grammar, start_item.clone());

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

        let start_item = LR0Item {
            lhs: NonTerminal('S'),
            production: vec![
                Symbol::NonTerminal(NonTerminal('A')),
                Symbol::NonTerminal(NonTerminal('B')),
            ],
            cursor_pos: 0,
        };

        let closure_set = LR0Builder::closure(&grammar, start_item);

        // when
        let goto_set = LR0Builder::goto(
            &grammar,
            closure_set,
            &Symbol::NonTerminal(NonTerminal('A')),
        );

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

        let start_item = LR0Item {
            lhs: NonTerminal('S'),
            production: vec![
                Symbol::NonTerminal(NonTerminal('A')),
                Symbol::NonTerminal(NonTerminal('B')),
            ],
            cursor_pos: 2,
        };

        let closure_set = LR0Builder::closure(&grammar, start_item);

        // when
        let goto_set = LR0Builder::goto(
            &grammar,
            closure_set,
            &Symbol::Terminal(Terminal::Char('a')),
        );

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

        // when
        let lr0 = LR0Builder::new(&grammar);

        // then
        assert_eq!(lr0.states.len(), 6);
        assert_eq!(lr0.transitions.len(), 5);
    }
}


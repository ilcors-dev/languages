use std::{
    collections::{BTreeSet, HashMap, HashSet},
    fmt::Display,
};

use crate::{
    builder::{
        common::{calculate_all_first_sets, FirstSetTable},
        lr::{lr0::LR0Item, types::LRItem},
        types::TableGenerator,
    },
    model::{
        grammar::Grammar,
        types::{NonTerminal, Symbol, Terminal},
    },
    parser::types::{LRAction, LRParsingTable},
};

#[derive(Debug, Clone)]
pub struct LR1State {
    pub items: HashSet<LR1Item>,
}

#[derive(Debug, Clone, Eq, PartialEq, Hash)]
pub struct LR1Item {
    /// The LR0 item is the same as in LR(0)
    pub lr0_item: LR0Item,

    pub lookahead: BTreeSet<Terminal>,
}

impl LRItem for LR1Item {
    fn advance_cursor(&self) -> Self {
        LR1Item {
            lr0_item: self.lr0_item.advance_cursor(),
            lookahead: self.lookahead.clone(),
        }
    }

    fn symbol_after_cursor(&self) -> Option<&Symbol> {
        self.lr0_item.symbol_after_cursor()
    }
}

impl Display for LR1Item {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut production_str = String::new();

        for (i, symbol) in self.lr0_item.production.iter().enumerate() {
            if i == self.lr0_item.cursor_pos {
                production_str.push_str("• ");
            }
            production_str.push_str(&format!("{} ", symbol));
        }

        if self.lr0_item.cursor_pos == self.lr0_item.production.len() {
            production_str.push_str("•");
        }

        write!(
            f,
            "{} -> {}, [{}]",
            self.lr0_item.lhs,
            production_str.trim(),
            self.lookahead
                .iter()
                .map(|t| t.to_string())
                .collect::<Vec<String>>()
                .join(","),
        )
    }
}

pub struct LR1Builder<'a> {
    grammar: &'a Grammar,
    states: HashMap<usize, LR1State>,
    transitions: HashMap<(usize, Symbol), usize>,
}

impl LR1Builder<'_> {
    pub fn new(grammar: &Grammar) -> LR1Builder<'_> {
        let first_sets = calculate_all_first_sets(grammar);
        let mut states = HashMap::new();
        let mut transitions = HashMap::new();

        let start = LR1Item {
            lr0_item: LR0Item {
                lhs: NonTerminal('Z'),
                production: vec![Symbol::NonTerminal(grammar.s)],
                cursor_pos: 0,
            },
            lookahead: BTreeSet::from([Terminal::EOF]),
        };

        let items = Self::closure(grammar, &first_sets, start);

        states.insert(0, LR1State { items });

        let mut worklist: Vec<usize> = states.keys().cloned().collect();

        while let Some(state_idx) = worklist.pop() {
            let items = if let Some(state) = states.get(&state_idx) {
                state.items.clone()
            } else {
                continue;
            };

            for symbol_after_cursor in items.iter().filter_map(|item| item.symbol_after_cursor()) {
                if *symbol_after_cursor == Symbol::Terminal(crate::model::types::Terminal::EOF) {
                    continue;
                }

                let new_items =
                    Self::goto(grammar, &first_sets, items.clone(), symbol_after_cursor);

                if new_items.is_empty() {
                    continue;
                }

                let new_state_idx = if let Some((idx, _)) =
                    states.iter().find(|(_, state)| state.items == new_items)
                {
                    *idx
                } else {
                    let new_idx = states.len();

                    states.insert(new_idx, LR1State { items: new_items });

                    worklist.push(new_idx);

                    new_idx
                };

                transitions.insert((state_idx, *symbol_after_cursor), new_state_idx);
            }
        }

        LR1Builder {
            grammar,
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
    fn goto(
        grammar: &Grammar,
        first_sets: &FirstSetTable,
        items: HashSet<LR1Item>,
        symbol: &Symbol,
    ) -> HashSet<LR1Item> {
        let mut goto_set = HashSet::new();

        for item in items.iter() {
            if item.lr0_item.symbol_after_cursor() == Some(&symbol) {
                let advanced_item = item.lr0_item.advance_cursor();

                let advanced_lr1_item = LR1Item {
                    lr0_item: advanced_item,
                    lookahead: item.lookahead.clone(),
                };

                for closure_item in
                    Self::closure(grammar, first_sets, advanced_lr1_item).into_iter()
                {
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
    fn closure(grammar: &Grammar, first_sets: &FirstSetTable, item: LR1Item) -> HashSet<LR1Item> {
        let mut closure_set = HashSet::new();
        closure_set.insert(item);

        let mut added = true;

        while added {
            added = false;

            let curr_items = closure_set.clone();

            for item in curr_items.iter() {
                if let Some(Symbol::NonTerminal(nt)) = item.symbol_after_cursor() {
                    let lookaheads = Self::lookaheads_of_item(
                        item.lr0_item.cursor_pos,
                        &item.lr0_item.production,
                        &item.lookahead,
                        first_sets,
                    );

                    for production in grammar.productions.get(nt).unwrap().alternatives.iter() {
                        let new_item = LR1Item {
                            lr0_item: LR0Item {
                                lhs: *nt,
                                production: production.clone(),
                                cursor_pos: 0,
                            },
                            lookahead: lookaheads.clone(),
                        };

                        if closure_set.insert(new_item) {
                            added = true;
                        }
                    }
                }
            }
        }

        closure_set
    }

    /// If the symbol after the cursor is a nonterminal B, compute the lookahead set for new items as FIRST(βa), where β is the suffix after B and a is the item's current lookahead.
    /// Add new LR1Items for each production of B with these propagated lookaheads.
    /// If βa can derive epsilon, include EOF in the lookahead.
    fn lookaheads_of_item(
        cursor_pos: usize,
        production: &Vec<Symbol>,
        lookahead: &BTreeSet<Terminal>,
        first_sets: &FirstSetTable,
    ) -> BTreeSet<Terminal> {
        let mut lookaheads = BTreeSet::new();

        let beta_a = &production[cursor_pos + 1..];

        let mut first_of_beta_a: HashSet<Terminal> = HashSet::new();

        if beta_a.is_empty() {
            first_of_beta_a.extend(lookahead.iter().cloned());
        } else {
            let mut contains_epsilon = true;

            for symbol in beta_a {
                let as_non_terminal = NonTerminal::try_from(*symbol)
                    .expect("Expected symbol to be terminal in lookahead calculation");
                let symbol_first_set = first_sets.get(&as_non_terminal).unwrap();

                first_of_beta_a.extend(
                    symbol_first_set
                        .0
                        .iter()
                        .filter(|t| **t != Terminal::Epsilon)
                        .cloned(),
                );

                if !symbol_first_set.0.contains(&Terminal::Epsilon) {
                    contains_epsilon = false;

                    break;
                }
            }

            if contains_epsilon {
                first_of_beta_a.extend(lookahead.iter().cloned());
            }
        }

        lookaheads.extend(first_of_beta_a);

        lookaheads
    }
}

impl TableGenerator<LRParsingTable> for LR1Builder<'_> {
    fn build_parsing_table(&self) -> Result<LRParsingTable, String> {
        let mut actions: HashMap<(usize, Symbol), Vec<LRAction>> = HashMap::new();

        let mut terminals: HashSet<Symbol> = self.grammar.v_terminal.clone();
        terminals.insert(Symbol::Terminal(crate::model::types::Terminal::EOF));
        terminals.remove(&Symbol::Terminal(crate::model::types::Terminal::Epsilon));

        for ((state_idx, symbol), to_state_idx) in self.transitions.iter() {
            actions
                .entry((*state_idx, symbol.clone()))
                .or_insert_with(Vec::new)
                .push(LRAction::Shift(*to_state_idx));
        }

        for (state_idx, state) in self.states.iter() {
            for item in state.items.iter() {
                if item.symbol_after_cursor().is_some() {
                    continue;
                }

                // reduction or accept?
                if item.lr0_item.lhs == NonTerminal('Z')
                    && item.lr0_item.production == vec![Symbol::NonTerminal(self.grammar.s)]
                {
                    // accept
                    actions
                        .entry((
                            *state_idx,
                            Symbol::Terminal(crate::model::types::Terminal::EOF),
                        ))
                        .or_insert_with(Vec::new)
                        .push(LRAction::Accept);
                } else {
                    // reduction
                    let production = self
                        .grammar
                        .productions
                        .get(&item.lr0_item.lhs)
                        .ok_or_else(|| {
                            format!(
                                "Production for non-terminal '{}' not found in grammar.",
                                item.lr0_item.lhs
                            )
                        })?;

                    let production_index = production
                        .alternatives
                        .iter()
                        .position(|alt| *alt == item.lr0_item.production)
                        .ok_or_else(|| {
                            format!(
                                "Alternative '{:?}' for production '{}' not found in grammar.",
                                item.lr0_item.production, item.lr0_item.lhs
                            )
                        })?;

                    for lookahead in item.lookahead.iter() {
                        actions
                            .entry((*state_idx, Symbol::Terminal(*lookahead)))
                            .or_insert_with(Vec::new)
                            .push(LRAction::Reduce(
                                item.lr0_item.lhs,
                                item.lr0_item.production.clone(),
                                production_index,
                            ));
                    }
                }
            }
        }

        Ok(LRParsingTable { actions })
    }

    fn to_printable_table(&self) -> Option<tabled::Table> {
        let table = self.build_parsing_table();

        if table.is_err() {
            return None;
        }

        let mut builder = tabled::builder::Builder::default();

        let mut header = vec!["PARSING TABLE (State / Symbols)".to_string()];

        let mut symbols: Vec<Symbol> = self.grammar.v_terminal.iter().cloned().collect();

        symbols.push(Symbol::Terminal(crate::model::types::Terminal::EOF));
        symbols.sort_by(|a, b| a.to_string().cmp(&b.to_string()));
        for symbol in symbols.iter() {
            header.push(symbol.to_string());
        }

        builder.push_record(header);
        let parsing_table = table.unwrap();

        let mut state_indices: Vec<usize> = self.states.keys().cloned().collect();
        state_indices.sort();

        for state_idx in state_indices.iter() {
            let mut row = vec![format!("State {}", state_idx)];

            let mut symbols: Vec<Symbol> = self.grammar.v_terminal.iter().cloned().collect();
            symbols.push(Symbol::Terminal(crate::model::types::Terminal::EOF));
            symbols.sort_by(|a, b| a.to_string().cmp(&b.to_string()));

            for symbol in symbols.iter() {
                let actions = parsing_table.actions.get(&(*state_idx, symbol.clone()));

                if let Some(actions) = actions {
                    let action_str = actions
                        .iter()
                        .map(|a| {
                            if actions.len() > 1 {
                                format!("⚠️ {}", a)
                            } else {
                                format!("{}", a)
                            }
                        })
                        .collect::<Vec<String>>()
                        .join("\n");

                    row.push(action_str);
                } else {
                    row.push("-".to_string());
                }
            }

            builder.push_record(row);
        }

        Some(builder.build())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::{BTreeSet, HashSet};

    #[test]
    fn lr1_item_should_advance_cursor_when_called() {
        // given
        let item = LR1Item {
            lr0_item: LR0Item {
                lhs: NonTerminal('S'),
                production: vec![
                    Symbol::NonTerminal(NonTerminal('A')),
                    Symbol::Terminal(Terminal::Char('a')),
                ],
                cursor_pos: 0,
            },
            lookahead: BTreeSet::from([Terminal::Char('b')]),
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
    fn lr1_item_should_peek_next_item() {
        // given
        let item = LR1Item {
            lr0_item: LR0Item {
                lhs: NonTerminal('S'),
                production: vec![
                    Symbol::NonTerminal(NonTerminal('A')),
                    Symbol::Terminal(Terminal::Char('a')),
                ],
                cursor_pos: 0,
            },
            lookahead: BTreeSet::from([Terminal::EOF]),
        };

        // when / then
        assert_eq!(
            item.symbol_after_cursor(),
            Some(&Symbol::NonTerminal(NonTerminal('A')))
        );
    }

    #[test]
    fn lr1_item_should_return_none_when_cursor_at_end() {
        // given
        let item = LR1Item {
            lr0_item: LR0Item {
                lhs: NonTerminal('S'),
                production: vec![
                    Symbol::NonTerminal(NonTerminal('A')),
                    Symbol::Terminal(Terminal::Char('a')),
                ],
                cursor_pos: 2,
            },
            lookahead: BTreeSet::new(),
        };

        // when / then
        assert_eq!(item.symbol_after_cursor(), None);
    }

    #[test]
    fn lr1_item_displays_cursor_at_proper_position() {
        // given
        let item = LR1Item {
            lr0_item: LR0Item {
                lhs: NonTerminal('S'),
                production: vec![
                    Symbol::NonTerminal(NonTerminal('A')),
                    Symbol::Terminal(Terminal::Char('a')),
                ],
                cursor_pos: 1,
            },
            lookahead: BTreeSet::from([Terminal::Char('b'), Terminal::EOF]),
        };

        // when
        let item_str = format!("{}", item);

        // then
        assert_eq!(item_str, "S -> A • a, [b,$]");
    }

    #[test]
    fn lr1_item_displays_cursor_at_end_properly() {
        // given
        let item = LR1Item {
            lr0_item: LR0Item {
                lhs: NonTerminal('S'),
                production: vec![
                    Symbol::NonTerminal(NonTerminal('A')),
                    Symbol::Terminal(Terminal::Char('a')),
                ],
                cursor_pos: 2,
            },
            lookahead: BTreeSet::from([Terminal::EOF]),
        };

        // when
        let item_str = format!("{}", item);

        // then
        assert_eq!(item_str, "S -> A a •, [$]");
    }

    #[test]
    fn lr1_item_displays_cursor_at_start_properly() {
        // given
        let item = LR1Item {
            lr0_item: LR0Item {
                lhs: NonTerminal('S'),
                production: vec![
                    Symbol::NonTerminal(NonTerminal('A')),
                    Symbol::Terminal(Terminal::Char('a')),
                ],
                cursor_pos: 0,
            },
            lookahead: BTreeSet::from([Terminal::Char('a')]),
        };

        // when
        let item_str = format!("{}", item);

        // then
        assert_eq!(item_str, "S -> • A a, [a]");
    }

    #[test]
    fn lr1_closure_computes_closure_correctly() {
        // given
        let template = "
            S->AB
            A->a|e
            B->b
        ";

        let grammar = Grammar::from_string(template.to_string()).unwrap();
        let first_sets = crate::builder::common::calculate_all_first_sets(&grammar);

        let start_item = LR1Item {
            lr0_item: LR0Item {
                lhs: NonTerminal('S'),
                production: vec![
                    Symbol::NonTerminal(NonTerminal('A')),
                    Symbol::NonTerminal(NonTerminal('B')),
                ],
                cursor_pos: 0,
            },
            lookahead: BTreeSet::from([Terminal::EOF]),
        };

        // when
        let closure_set = LR1Builder::closure(&grammar, &first_sets, start_item);

        // then
        let expected_items: HashSet<LR1Item> = HashSet::from_iter(vec![
            LR1Item {
                lr0_item: LR0Item {
                    lhs: NonTerminal('S'),
                    production: vec![
                        Symbol::NonTerminal(NonTerminal('A')),
                        Symbol::NonTerminal(NonTerminal('B')),
                    ],
                    cursor_pos: 0,
                },
                lookahead: BTreeSet::from([Terminal::EOF]),
            },
            LR1Item {
                lr0_item: LR0Item {
                    lhs: NonTerminal('A'),
                    production: vec![Symbol::Terminal(Terminal::Char('a'))],
                    cursor_pos: 0,
                },
                lookahead: BTreeSet::from([Terminal::Char('b')]), // FIRST(B) = {b}
            },
            LR1Item {
                lr0_item: LR0Item {
                    lhs: NonTerminal('A'),
                    production: vec![Symbol::Terminal(Terminal::Epsilon)],
                    cursor_pos: 0,
                },
                lookahead: BTreeSet::from([Terminal::Char('b')]),
            },
        ]);

        assert_eq!(closure_set, expected_items);
    }

    #[test]
    fn lr1_closure_returns_only_initial_item_when_no_non_terminal_after_cursor() {
        // given
        let template = "
            S->aB
            B->b
        ";

        let grammar = Grammar::from_string(template.to_string()).unwrap();
        let first_sets = crate::builder::common::calculate_all_first_sets(&grammar);

        let start_item = LR1Item {
            lr0_item: LR0Item {
                lhs: NonTerminal('S'),
                production: vec![
                    Symbol::Terminal(Terminal::Char('a')),
                    Symbol::NonTerminal(NonTerminal('B')),
                ],
                cursor_pos: 0,
            },
            lookahead: BTreeSet::from([Terminal::EOF]),
        };

        // when
        let closure_set = LR1Builder::closure(&grammar, &first_sets, start_item.clone());

        // then
        let expected_items: HashSet<LR1Item> = HashSet::from_iter(vec![start_item]);

        assert_eq!(closure_set, expected_items);
    }

    #[test]
    fn lr1_goto_computes_goto_correctly() {
        // given
        let template = "
            S->AB
            A->a|e
            B->b
        ";

        let grammar = Grammar::from_string(template.to_string()).unwrap();
        let first_sets = crate::builder::common::calculate_all_first_sets(&grammar);

        let start_item = LR1Item {
            lr0_item: LR0Item {
                lhs: NonTerminal('S'),
                production: vec![
                    Symbol::NonTerminal(NonTerminal('A')),
                    Symbol::NonTerminal(NonTerminal('B')),
                ],
                cursor_pos: 0,
            },
            lookahead: BTreeSet::from([Terminal::EOF]),
        };

        let closure_set = LR1Builder::closure(&grammar, &first_sets, start_item);

        // when
        let goto_set = LR1Builder::goto(
            &grammar,
            &first_sets,
            closure_set,
            &Symbol::NonTerminal(NonTerminal('A')),
        );

        // then
        let expected_items: HashSet<LR1Item> = HashSet::from_iter(vec![
            LR1Item {
                lr0_item: LR0Item {
                    lhs: NonTerminal('S'),
                    production: vec![
                        Symbol::NonTerminal(NonTerminal('A')),
                        Symbol::NonTerminal(NonTerminal('B')),
                    ],
                    cursor_pos: 1,
                },
                lookahead: BTreeSet::from([Terminal::EOF]),
            },
            LR1Item {
                lr0_item: LR0Item {
                    lhs: NonTerminal('B'),
                    production: vec![Symbol::Terminal(Terminal::Char('b'))],
                    cursor_pos: 0,
                },
                lookahead: BTreeSet::from([Terminal::EOF]), // FIRST(ε + EOF) = {EOF}
            },
        ]);

        assert_eq!(goto_set, expected_items);
    }

    #[test]
    fn lr1_goto_returns_empty_set_when_no_items_match() {
        // given
        let template = "
            S->AB
            A->a|e
            B->b
        ";

        let grammar = Grammar::from_string(template.to_string()).unwrap();
        let first_sets = crate::builder::common::calculate_all_first_sets(&grammar);

        let start_item = LR1Item {
            lr0_item: LR0Item {
                lhs: NonTerminal('S'),
                production: vec![
                    Symbol::NonTerminal(NonTerminal('A')),
                    Symbol::NonTerminal(NonTerminal('B')),
                ],
                cursor_pos: 2,
            },
            lookahead: BTreeSet::from([Terminal::EOF]),
        };

        let closure_set = LR1Builder::closure(&grammar, &first_sets, start_item);

        // when
        let goto_set = LR1Builder::goto(
            &grammar,
            &first_sets,
            closure_set,
            &Symbol::Terminal(Terminal::Char('a')),
        );

        // then
        let expected_items: HashSet<LR1Item> = HashSet::new();

        assert_eq!(goto_set, expected_items);
    }

    #[test]
    fn lr1_builder_builds_states_and_transitions_correctly() {
        // given
        let template = "
            S->AB
            A->a
            B->b
        ";

        let grammar = Grammar::from_string(template.to_string()).unwrap();

        // when
        let lr1 = LR1Builder::new(&grammar);

        // then
        assert!(lr1.states.len() > 0);
        assert!(lr1.transitions.len() > 0);
    }

    #[test]
    fn lr1_builder_augments_grammar_with_start_production() {
        // given
        let template = "
            S->AB
            A->a
            B->b
        ";

        let grammar = Grammar::from_string(template.to_string()).unwrap();

        // when
        let lr1 = LR1Builder::new(&grammar);

        // then
        let start_state = lr1.states.get(&0).unwrap();

        let expected_start_item = LR1Item {
            lr0_item: LR0Item {
                lhs: NonTerminal('Z'),
                production: vec![Symbol::NonTerminal(NonTerminal('S'))],
                cursor_pos: 0,
            },
            lookahead: BTreeSet::from([Terminal::EOF]),
        };

        assert!(start_state.items.contains(&expected_start_item));
    }

    #[test]
    fn lr1_builder_ignores_eof_in_goto_transitions() {
        // given
        let template = "
            S->AB
            A->a
            B->b
        ";

        let grammar = Grammar::from_string(template.to_string()).unwrap();

        // when
        let lr1 = LR1Builder::new(&grammar);

        // then
        for ((_, symbol), _) in lr1.transitions.iter() {
            assert_ne!(*symbol, Symbol::Terminal(Terminal::EOF));
        }
    }

    #[test]
    fn lr1_build_parsing_table_contains_reductions_only_on_lookaheads() {
        // given
        let template = "
            S->a
        ";
        let grammar = Grammar::from_string(template.to_string()).unwrap();
        let lr1 = LR1Builder::new(&grammar);

        // when
        let table = lr1.build_parsing_table().unwrap();

        // then
        // state with S -> a . should have reduction only for EOF (since start item has EOF lookahead)
        let reduction_state_idx = lr1
            .states
            .iter()
            .find(|(_, state)| {
                state.items.contains(&LR1Item {
                    lr0_item: LR0Item {
                        lhs: NonTerminal('S'),
                        production: vec![Symbol::Terminal(Terminal::Char('a'))],
                        cursor_pos: 1,
                    },
                    lookahead: BTreeSet::from([Terminal::EOF]), // propagated from start
                })
            })
            .map(|(idx, _)| *idx)
            .unwrap();

        let actions_for_eof = table
            .actions
            .get(&(reduction_state_idx, Symbol::Terminal(Terminal::EOF)))
            .unwrap();

        assert!(actions_for_eof
            .iter()
            .any(|a| matches!(a, LRAction::Reduce(_, _, _))));

        // Should NOT have reduction for 'a'
        let actions_for_a = table
            .actions
            .get(&(reduction_state_idx, Symbol::Terminal(Terminal::Char('a'))));

        assert!(actions_for_a.is_none());
    }

    #[test]
    fn lr1_builds_valid_parsing_table() {
        // given
        let template = "
            S->PH|QA
            P->a
            Q->h
            A->PH|P
            H->QA|Q
        ";

        let grammar = Grammar::from_string(template.to_string()).unwrap();

        // when
        let lr1 = LR1Builder::new(&grammar);
        let table = lr1.build_parsing_table();

        // then
        assert!(table.is_ok());
        assert!(!table.unwrap().actions.is_empty());
    }

    #[test]
    fn lr1_table_contains_shift_actions() {
        // given
        let template = "
            S->PH|QA
            P->a
            Q->h
            A->PH|P
            H->QA|Q
        ";

        let grammar = Grammar::from_string(template.to_string()).unwrap();
        let lr1 = LR1Builder::new(&grammar);
        let table = lr1.build_parsing_table().unwrap();

        // when
        let mut shift_count = 0;
        for actions in table.actions.values() {
            for action in actions {
                if matches!(action, LRAction::Shift(_)) {
                    shift_count += 1;
                }
            }
        }

        // then
        assert!(shift_count > 0);
    }

    #[test]
    fn lr1_table_contains_accept_action() {
        // given
        let template = "
            S->PH|QA
            P->a
            Q->h
            A->PH|P
            H->QA|Q
        ";

        let grammar = Grammar::from_string(template.to_string()).unwrap();
        let lr1 = LR1Builder::new(&grammar);
        let table = lr1.build_parsing_table().unwrap();

        let accept_state_idx = lr1
            .states
            .iter()
            .find(|(_, state)| {
                state.items.contains(&LR1Item {
                    lr0_item: LR0Item {
                        lhs: NonTerminal('Z'),
                        production: vec![Symbol::NonTerminal(NonTerminal('S'))],
                        cursor_pos: 1,
                    },
                    lookahead: BTreeSet::from([Terminal::EOF]),
                })
            })
            .map(|(idx, _)| *idx)
            .expect("Should find state with Z -> S .");

        // when
        let actions = table
            .actions
            .get(&(accept_state_idx, Symbol::Terminal(Terminal::EOF)))
            .expect("Should have actions on EOF");

        // then
        assert!(
            actions.iter().any(|a| matches!(a, LRAction::Accept)),
            "Should have Accept action on EOF in state with Z -> S ."
        );
    }

    #[test]
    fn lr1_lookaheads_of_item_handles_empty_suffix() {
        // given
        let template = "
            S->A
            A->a
        ";
        let grammar = Grammar::from_string(template.to_string()).unwrap();
        let first_sets = crate::builder::common::calculate_all_first_sets(&grammar);

        let production = vec![Symbol::NonTerminal(NonTerminal('A'))];
        let lookahead = BTreeSet::from([Terminal::EOF]);

        // when
        let result = LR1Builder::lookaheads_of_item(0, &production, &lookahead, &first_sets);

        // then
        assert_eq!(result, BTreeSet::from([Terminal::EOF]));
    }

    #[test]
    fn lr1_lookaheads_of_item_handles_epsilon_in_suffix() {
        // given
        let template = "
            S->AB
            A->a|e
            B->b
        ";
        let grammar = Grammar::from_string(template.to_string()).unwrap();
        let first_sets = crate::builder::common::calculate_all_first_sets(&grammar);

        let production = vec![
            Symbol::NonTerminal(NonTerminal('A')),
            Symbol::NonTerminal(NonTerminal('B')),
        ];
        let lookahead = BTreeSet::from([Terminal::EOF]);

        // when (cursor at A, suffix is B)
        let result = LR1Builder::lookaheads_of_item(0, &production, &lookahead, &first_sets);

        // then (FIRST(B) includes b, not epsilon)
        assert_eq!(result, BTreeSet::from([Terminal::Char('b')]));
    }

    #[test]
    fn lr1_to_printable_table_returns_valid_table() {
        // given
        let template = "
            S->PH|QA
            P->a
            Q->h
            A->PH|P
            H->QA|Q
        ";

        let grammar = Grammar::from_string(template.to_string()).unwrap();
        let lr1 = LR1Builder::new(&grammar);

        // when
        let table = lr1.to_printable_table();

        // then
        assert!(table.is_some());
    }
}

use std::collections::{HashMap, HashSet};

use crate::{
    builder::{
        common::{calculate_all_first_sets, calculate_all_follow_sets},
        lr::{lr0::LR0Builder, types::LRItem},
        types::TableGenerator,
    },
    model::{
        grammar::Grammar,
        types::{NonTerminal, Symbol, Terminal},
    },
    parser::types::{LRAction, LRParsingTable},
};

/// SLR(1) Builder is a "smarter" LR(0) Builder that uses follow sets to better resolve reduce
/// actions instead of reducing regardless of the lookahead symbol.
pub struct SLR1Builder<'a> {
    lr0: LR0Builder<'a>,
    follow_sets: HashMap<NonTerminal, HashSet<Terminal>>,
}

impl SLR1Builder<'_> {
    pub fn new(grammar: &Grammar) -> SLR1Builder<'_> {
        SLR1Builder {
            lr0: LR0Builder::new(grammar),
            follow_sets: calculate_all_follow_sets(&grammar, &calculate_all_first_sets(&grammar)),
        }
    }
}

impl TableGenerator<LRParsingTable> for SLR1Builder<'_> {
    fn build_parsing_table(&self) -> Result<LRParsingTable, String> {
        let mut actions: HashMap<(usize, Symbol), Vec<LRAction>> = HashMap::new();

        let mut terminals: HashSet<Symbol> = self.lr0.grammar().v_terminal.clone();
        terminals.insert(Symbol::Terminal(crate::model::types::Terminal::EOF));
        terminals.remove(&Symbol::Terminal(crate::model::types::Terminal::Epsilon));

        for ((state_idx, symbol), to_state_idx) in self.lr0.transitions().iter() {
            actions
                .entry((*state_idx, symbol.clone()))
                .or_insert_with(Vec::new)
                .push(LRAction::Shift(*to_state_idx));
        }

        for (state_idx, state) in self.lr0.states().iter() {
            for item in state.items.iter() {
                if item.symbol_after_cursor().is_some() {
                    continue;
                }

                // reduction or accept?
                if item.lhs == NonTerminal('Z')
                    && item.production == vec![Symbol::NonTerminal(self.lr0.grammar().s)]
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
                    let production =
                        self.lr0
                            .grammar()
                            .productions
                            .get(&item.lhs)
                            .ok_or_else(|| {
                                format!(
                                    "Production for non-terminal '{}' not found in grammar.",
                                    item.lhs
                                )
                            })?;

                    let production_index = production
                        .alternatives
                        .iter()
                        .position(|alt| *alt == item.production)
                        .ok_or_else(|| {
                            format!(
                                "Alternative '{:?}' for production '{}' not found in grammar.",
                                item.production, item.lhs
                            )
                        })?;

                    let follow_set = self.follow_sets.get(&item.lhs).ok_or_else(|| {
                        format!(
                            "Follow set for non-terminal '{}' not found in grammar.",
                            item.lhs
                        )
                    })?;

                    for terminal in follow_set.iter() {
                        actions
                            .entry((*state_idx, Symbol::Terminal(*terminal)))
                            .or_insert_with(Vec::new)
                            .push(LRAction::Reduce(
                                item.lhs,
                                item.production.clone(),
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

        let mut symbols: Vec<Symbol> = self.lr0.grammar().v_terminal.iter().cloned().collect();

        symbols.push(Symbol::Terminal(crate::model::types::Terminal::EOF));
        symbols.sort_by(|a, b| a.to_string().cmp(&b.to_string()));
        for symbol in symbols.iter() {
            header.push(symbol.to_string());
        }

        builder.push_record(header);
        let parsing_table = table.unwrap();

        let mut state_indices: Vec<usize> = self.lr0.states().keys().cloned().collect();
        state_indices.sort();

        for state_idx in state_indices.iter() {
            let mut row = vec![format!("State {}", state_idx)];

            let mut symbols: Vec<Symbol> = self.lr0.grammar().v_terminal.iter().cloned().collect();
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
    use crate::{
        builder::{
            lr::{lr0::LR0Item, slr1::SLR1Builder},
            types::TableGenerator,
        },
        model::{
            grammar::Grammar,
            types::{NonTerminal, Symbol, Terminal},
        },
        parser::types::LRAction,
    };
    use std::collections::HashSet;

    #[test]
    fn slr1_builder_constructs_successfully() {
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
        let slr1 = SLR1Builder::new(&grammar);

        // then
        assert!(!slr1.lr0.states().is_empty());
        assert!(!slr1.lr0.transitions().is_empty());
    }

    #[test]
    fn slr1_builder_has_correct_number_of_states_and_transitions() {
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
        let slr1 = SLR1Builder::new(&grammar);

        // then
        assert_eq!(slr1.lr0.states().len(), 12);
        assert_eq!(slr1.lr0.transitions().len(), 17);
    }

    #[test]
    fn slr1_reductions_only_on_follow_set_not_all_terminals() {
        // given
        let template = "
            S->PH|QA
            P->a
            Q->h
            A->PH|P
            H->QA|Q
        ";

        let grammar = Grammar::from_string(template.to_string()).unwrap();
        let slr1 = SLR1Builder::new(&grammar);
        let table = slr1.build_parsing_table().unwrap();

        let p_state_idx = slr1
            .lr0
            .states()
            .iter()
            .find(|(_, state)| {
                state.items.contains(&LR0Item {
                    lhs: NonTerminal('P'),
                    production: vec![Symbol::Terminal(Terminal::Char('a'))],
                    cursor_pos: 1,
                })
            })
            .map(|(idx, _)| *idx)
            .expect("Should find state with P -> a .");

        let expected_follow_p: HashSet<Terminal> =
            HashSet::from_iter(vec![Terminal::Char('h'), Terminal::EOF]);

        // when / then
        for terminal in &[Terminal::Char('a'), Terminal::Char('h'), Terminal::EOF] {
            let actions = table
                .actions
                .get(&(p_state_idx, Symbol::Terminal(*terminal)));

            if expected_follow_p.contains(terminal) {
                assert!(
                    actions.is_some(),
                    "Should have action for terminal {:?} which is in FOLLOW(P)",
                    terminal
                );
                assert!(
                    actions
                        .unwrap()
                        .iter()
                        .any(|a| matches!(a, LRAction::Reduce(NonTerminal('P'), _, _))),
                    "Should have Reduce(P) action for terminal {:?} which is in FOLLOW(P)",
                    terminal
                );
            } else {
                assert!(
                    actions.is_none()
                        || !actions
                            .unwrap()
                            .iter()
                            .any(|a| matches!(a, LRAction::Reduce(NonTerminal('P'), _, _))),
                    "Should NOT have Reduce(P) action for terminal {:?} which is NOT in FOLLOW(P)",
                    terminal
                );
            }
        }
    }

    #[test]
    fn slr1_builds_valid_parsing_table() {
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
        let slr1 = SLR1Builder::new(&grammar);
        let table = slr1.build_parsing_table();

        // then
        assert!(table.is_ok());
        assert!(!table.unwrap().actions.is_empty());
    }

    #[test]
    fn slr1_table_contains_shift_actions() {
        // given
        let template = "
            S->PH|QA
            P->a
            Q->h
            A->PH|P
            H->QA|Q
        ";

        let grammar = Grammar::from_string(template.to_string()).unwrap();
        let slr1 = SLR1Builder::new(&grammar);
        let table = slr1.build_parsing_table().unwrap();

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
        assert_eq!(shift_count, 17);
    }

    #[test]
    fn slr1_table_contains_accept_action() {
        // given
        let template = "
            S->PH|QA
            P->a
            Q->h
            A->PH|P
            H->QA|Q
        ";

        let grammar = Grammar::from_string(template.to_string()).unwrap();
        let slr1 = SLR1Builder::new(&grammar);
        let table = slr1.build_parsing_table().unwrap();

        let accept_state_idx = slr1
            .lr0
            .states()
            .iter()
            .find(|(_, state)| {
                state.items.contains(&LR0Item {
                    lhs: NonTerminal('Z'),
                    production: vec![Symbol::NonTerminal(NonTerminal('S'))],
                    cursor_pos: 1,
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
    fn slr1_has_no_reduce_reduce_conflicts() {
        // given
        let template = "
            S->PH|QA
            P->a
            Q->h
            A->PH|P
            H->QA|Q
        ";

        let grammar = Grammar::from_string(template.to_string()).unwrap();
        let slr1 = SLR1Builder::new(&grammar);
        let table = slr1.build_parsing_table().unwrap();

        // when / then
        for actions in table.actions.values() {
            let reduce_count = actions
                .iter()
                .filter(|a| matches!(a, LRAction::Reduce(_, _, _)))
                .count();

            assert!(
                reduce_count <= 1,
                "Found reduce-reduce conflict: {} reduce actions in state",
                reduce_count
            );
        }
    }

    #[test]
    fn slr1_no_shift_reduce_conflicts_on_test_grammar() {
        // given
        let template = "
            S->PH|QA
            P->a
            Q->h
            A->PH|P
            H->QA|Q
        ";

        let grammar = Grammar::from_string(template.to_string()).unwrap();
        let slr1 = SLR1Builder::new(&grammar);
        let table = slr1.build_parsing_table().unwrap();

        // when / then
        for ((state_idx, symbol), actions) in &table.actions {
            let has_shift = actions.iter().any(|a| matches!(a, LRAction::Shift(_)));
            let has_reduce = actions
                .iter()
                .any(|a| matches!(a, LRAction::Reduce(_, _, _) | LRAction::Accept));

            assert!(
                !(has_shift && has_reduce),
                "Found shift-reduce conflict in state {} on symbol {:?}",
                state_idx,
                symbol
            );
        }
    }

    #[test]
    fn slr1_to_printable_table_returns_valid_table() {
        // given
        let template = "
            S->PH|QA
            P->a
            Q->h
            A->PH|P
            H->QA|Q
        ";

        let grammar = Grammar::from_string(template.to_string()).unwrap();
        let slr1 = SLR1Builder::new(&grammar);

        // when
        let table = slr1.to_printable_table();

        // then
        assert!(table.is_some());
    }
}

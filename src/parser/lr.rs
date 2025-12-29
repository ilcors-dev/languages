use std::collections::VecDeque;

use tabled::Table;

use crate::{
    model::types::{Symbol, Terminal},
    parser::types::{LRAction, LRParsingTable, ParseResult, ParseStep, TraceRow},
};

pub struct LRParser {
    table: LRParsingTable,
    stack: Vec<usize>,
}

impl LRParser {
    pub fn new(table: LRParsingTable) -> Self {
        LRParser {
            table,
            stack: vec![0],
        }
    }

    pub fn parse(&mut self, input: &Vec<Terminal>) -> (ParseResult, Vec<ParseStep>) {
        let mut trace: Vec<ParseStep> = vec![];

        let mut queue: VecDeque<Terminal> = input.iter().copied().collect();
        queue.push_back(Terminal::EOF);

        loop {
            let stack_snapshot: Vec<String> = self.stack.iter().map(|s| s.to_string()).collect();
            let input_snapshot = queue.clone();

            let curr_state = match self.stack.last() {
                Some(s) => *s,
                None => {
                    let msg = "Parsing stack is empty.".to_string();
                    trace.push(ParseStep {
                        stack: stack_snapshot,
                        input: input_snapshot,
                        action: msg.clone(),
                    });
                    return (ParseResult::Reject(msg), trace);
                }
            };

            let next_symbol = match queue.front() {
                Some(t) => Symbol::Terminal(*t),
                None => {
                    let msg = "Input queue is empty.".to_string();
                    trace.push(ParseStep {
                        stack: stack_snapshot,
                        input: input_snapshot,
                        action: msg.clone(),
                    });
                    return (ParseResult::Reject(msg), trace);
                }
            };

            let action = match self.table.actions.get(&(curr_state, next_symbol)) {
                Some(actions) => {
                    if actions.len() > 1 {
                        let msg = format!(
                            "Grammar has conflicts: multiple actions found for state {} and symbol {}.",
                            curr_state, next_symbol
                        );
                        trace.push(ParseStep {
                            stack: stack_snapshot,
                            input: input_snapshot,
                            action: msg.clone(),
                        });
                        return (ParseResult::Reject(msg), trace);
                    }
                    actions.first().unwrap().clone()
                }
                None => {
                    let msg = format!(
                        "No action found for state {} and symbol {}.",
                        curr_state, next_symbol
                    );
                    trace.push(ParseStep {
                        stack: stack_snapshot,
                        input: input_snapshot,
                        action: msg.clone(),
                    });
                    return (ParseResult::Reject(msg), trace);
                }
            };

            let action_desc = action.to_string();

            trace.push(ParseStep {
                stack: stack_snapshot.clone(),
                input: input_snapshot.clone(),
                action: action_desc.clone(),
            });

            match action {
                LRAction::Shift(next_state) => {
                    self.stack.push(next_state);
                    queue.pop_front();
                }
                LRAction::Reduce(t, ref symbols, _) => {
                    for _ in symbols {
                        self.stack.pop();
                    }

                    let top_state = match self.stack.last() {
                        Some(s) => *s,
                        None => {
                            return (
                                ParseResult::Reject(
                                    "Parsing stack is empty after reduction.".to_string(),
                                ),
                                trace,
                            );
                        }
                    };

                    let goto_action = match self
                        .table
                        .actions
                        .get(&(top_state, Symbol::NonTerminal(t)))
                    {
                        Some(actions) => {
                            if actions.len() > 1 {
                                return (
                                    ParseResult::Reject(format!(
                                        "Grammar has conflicts: multiple goto actions found for state {} and non-terminal {}.",
                                        top_state, t
                                    )),
                                    trace,
                                );
                            }
                            actions.first().unwrap().clone()
                        }
                        None => {
                            return (
                                ParseResult::Reject(format!(
                                    "No goto action found for state {} and non-terminal {}.",
                                    top_state, t
                                )),
                                trace,
                            )
                        }
                    };

                    match goto_action {
                        LRAction::Shift(goto_state) => {
                            self.stack.push(goto_state);
                        }
                        _ => {
                            return (
                                ParseResult::Reject(format!(
                                    "Invalid goto action for state {} and non-terminal {}.",
                                    top_state, t
                                )),
                                trace,
                            )
                        }
                    }
                }
                LRAction::Accept => {
                    return (ParseResult::Accept, trace);
                }
            }
        }
    }

    pub fn trace_as_table(&self, trace: &[ParseStep]) -> Table {
        let rows: Vec<TraceRow> = trace
            .iter()
            .enumerate()
            .map(|(i, step)| {
                let stack_str = step.stack.join(" ");

                let input_str = step.input.iter().map(|s| s.to_string()).collect::<String>();

                TraceRow {
                    step: i + 1,
                    stack: stack_str,
                    input: input_str,
                    action: step.action.clone(),
                }
            })
            .collect();

        Table::new(rows)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::model::types::NonTerminal;
    use std::collections::HashMap;

    fn build_simple_table() -> LRParsingTable {
        // Grammar: S -> a
        // State 0:
        //   'a' -> Shift 1
        //   'S' -> Shift 2 (GOTO)
        // State 1:
        //   EOF -> Reduce (S -> a)
        // State 2:
        //   EOF -> Accept

        let mut actions = HashMap::new();

        actions.insert(
            (0, Symbol::Terminal(Terminal::Char('a'))),
            vec![LRAction::Shift(1)],
        );
        actions.insert(
            (0, Symbol::NonTerminal(NonTerminal('S'))),
            vec![LRAction::Shift(2)],
        );

        actions.insert(
            (1, Symbol::Terminal(Terminal::EOF)),
            vec![LRAction::Reduce(
                NonTerminal('S'),
                vec![Symbol::Terminal(Terminal::Char('a'))],
                0,
            )],
        );

        actions.insert((2, Symbol::Terminal(Terminal::EOF)), vec![LRAction::Accept]);

        LRParsingTable { actions }
    }

    #[test]
    fn given_valid_grammar_and_input_when_parsing_then_accepts_successfully() {
        // given
        let table = build_simple_table();
        let mut parser = LRParser::new(table);
        let input = vec![Terminal::Char('a')];

        // when
        let (result, trace) = parser.parse(&input);

        // then
        assert!(matches!(result, ParseResult::Accept));

        // verify trace steps
        // 1. initial State -> shift 1
        // 2. state 1 -> aeduce S->a
        // 3. state 2 -> accept
        assert_eq!(trace.len(), 3);
        assert_eq!(trace[0].action, "s1");
        assert!(trace[1].action.starts_with("r(S -> a)"));
        assert_eq!(trace[2].action, "acc");
    }

    #[test]
    fn given_valid_grammar_when_parsing_invalid_input_then_rejects_with_error() {
        // given
        let table = build_simple_table();
        let mut parser = LRParser::new(table);
        let input = vec![Terminal::Char('b')];

        // when
        let (result, trace) = parser.parse(&input);

        // then
        match result {
            ParseResult::Reject(msg) => {
                assert!(msg.contains("No action found"));
                assert!(msg.contains("state 0"));
                assert!(msg.contains("symbol b"));
            }
            _ => panic!("Expected Rejection, got {:?}", result),
        }

        // trace should contain the failed step
        assert_eq!(trace.len(), 1);
        assert!(trace[0].action.contains("No action found"));
    }

    #[test]
    fn given_valid_grammar_when_parsing_empty_input_then_rejects() {
        // given
        let table = build_simple_table();
        let mut parser = LRParser::new(table);
        let input = vec![]; // empty input means just EOF

        // when
        let (result, _) = parser.parse(&input);

        // then
        assert!(matches!(result, ParseResult::Reject(_)));
    }
}


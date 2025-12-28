use tabled::Table;

use crate::parser::types::{ParsingAction, TraceRow};
use std::collections::VecDeque;

use crate::{
    builder,
    model::{
        grammar::Grammar,
        types::{Symbol, Terminal},
    },
    parser::types::{LLParsingTable, ParseResult, ParseStep},
};

pub struct LL1Parser<'a> {
    grammar: &'a Grammar,
    parsing_table: LLParsingTable,
}

impl<'a> LL1Parser<'a> {
    pub fn new(grammar: &'a Grammar) -> Option<Self> {
        if !builder::ll1::is_ll1(grammar) {
            println!("The provided grammar is not LL(1) parseable!");
            return None;
        }

        let parsing_table = match builder::ll1::build_parsing_table(grammar) {
            Some(t) => t,
            _ => {
                println!("Could not build parsing table for the grammar");
                return None;
            }
        };

        Some(LL1Parser {
            grammar,
            parsing_table,
        })
    }

    /// Parses the given input of terminal characters to determine if they are accepted for the
    /// grammar.
    ///
    /// Keeps track of the steps done returning the "trace" to the caller.
    pub fn parse(&self, input: &[Terminal]) -> (ParseResult, Vec<ParseStep>) {
        let mut stack = vec![
            Symbol::Terminal(Terminal::EOF),
            Symbol::NonTerminal(self.grammar.s),
        ];

        let mut queue: VecDeque<Terminal> = input.iter().copied().collect();
        queue.push_back(Terminal::EOF);

        let mut tracee: Vec<ParseStep> = vec![];

        loop {
            // at each step, copy the last state of the parser and push it to the trace
            tracee.push(ParseStep {
                stack: stack.clone(),
                input: queue.clone(),
                action: String::new(),
            });

            // get the top of the stack
            let top = match stack.last() {
                Some(s) => *s,
                None => {
                    tracee.last_mut().unwrap().action = "Empty stack.".to_string();
                    return (ParseResult::Reject("Empty stack.".to_string()), tracee);
                }
            };

            // get the next token in the input
            let curr_input = match queue.front() {
                Some(t) => *t,
                None => {
                    tracee.last_mut().unwrap().action = "No more input tokens found".to_string();
                    return (
                        ParseResult::Reject("No more input tokens found".to_string()),
                        tracee,
                    );
                }
            };

            // case 1: top element is a terminal
            if let Symbol::Terminal(term) = top {
                if term == curr_input {
                    if term == Terminal::EOF {
                        tracee.last_mut().unwrap().action = "Accept.".to_string();
                        return (ParseResult::Accept, tracee);
                    }

                    stack.pop();
                    queue.pop_front();
                    tracee.last_mut().unwrap().action =
                        format!("Match '{}' (pop stack, next input).", term);
                } else {
                    let msg = format!("Expected '{}' but found '{}'.", term, curr_input);

                    tracee.last_mut().unwrap().action = msg.clone();
                    return (ParseResult::Reject(msg), tracee);
                }
            }
            // case 2: top element is a non-terminal, we need to check the parsing table to see what to do next
            else if let Symbol::NonTerminal(nt) = top {
                match self.parsing_table.get(&(nt, curr_input)) {
                    Some(actions) if !actions.is_empty() => {
                        if actions.len() > 1 {
                            let msg = format!("Conflict found for ({}, {}).", nt, curr_input);

                            tracee.last_mut().unwrap().action = msg.clone();
                            return (ParseResult::Reject(msg), tracee);
                        }

                        // if no conflicts, we can apply the production evenutally
                        match &actions[0] {
                            ParsingAction::Production(index) => {
                                let production = &self.grammar.productions[&nt];
                                let alternative = &production.alternatives[*index];

                                let prod_str = alternative
                                    .iter()
                                    .map(|s| s.to_string())
                                    .collect::<String>();
                                tracee.last_mut().unwrap().action =
                                    format!("{} -> {}", nt, prod_str);

                                // consume the top of the stack to apply its production instead
                                stack.pop();

                                for symbol in alternative.iter().rev() {
                                    if *symbol == Symbol::Terminal(Terminal::Epsilon) {
                                        continue;
                                    }

                                    stack.push(*symbol);
                                }
                            }
                            _ => {}
                        }
                    }
                    _ => {
                        let expected: Vec<Terminal> = self
                            .parsing_table
                            .iter()
                            .filter_map(|((non_terminal, terminal), actions)| {
                                if *non_terminal == nt && !actions.is_empty() {
                                    Some(*terminal)
                                } else {
                                    None
                                }
                            })
                            .collect();

                        let expected_str = if expected.is_empty() {
                            "nothing (production not found in parsing table)".to_string()
                        } else {
                            let terms: Vec<String> =
                                expected.iter().map(|t| t.to_string()).collect();
                            format!("one {}", terms.join(", "))
                        };

                        let msg = format!(
                            "Expected {}; but found '{}' instead.",
                            expected_str, curr_input
                        );

                        tracee.last_mut().unwrap().action = msg.clone();
                        return (ParseResult::Reject(msg), tracee);
                    }
                }
            }
        }
    }

    pub fn trace_as_table(trace: &[ParseStep]) -> Table {
        let rows: Vec<TraceRow> = trace
            .iter()
            .enumerate()
            .map(|(i, step)| {
                let stack_str = step
                    .stack
                    .iter()
                    .rev()
                    .map(|s| s.to_string())
                    .collect::<String>();

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
pub mod tests {
    use super::*;
    use crate::model::types::Terminal;

    #[test]
    fn ll1_parser_recognizes_grammar_successfully() {
        let grammar = Grammar::from_string(
            "
                S->AC
                A->a|e
                B->b
                C->B|e
            "
            .to_string(),
        )
        .unwrap();

        let parser = LL1Parser::new(&grammar).unwrap();

        // test: "ab"
        let (result, _) = parser.parse(&[Terminal::Char('a'), Terminal::Char('b')]);
        assert!(matches!(result, ParseResult::Accept));
    }
}

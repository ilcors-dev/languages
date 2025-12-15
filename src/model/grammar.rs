use std::collections::HashSet;
use std::{collections::HashMap, fs};

use tabled::{builder, Table};

use crate::model::types::{Alternative, NonTerminal, Production, Symbol, Terminal};

#[derive(Debug)]
pub struct Grammar {
    pub v_non_terminal: HashSet<Symbol>,
    pub v_terminal: HashSet<Symbol>,
    pub s: NonTerminal,
    pub productions: HashMap<NonTerminal, Production>,
    pub has_e_rules: bool,
}

/// Defines the common operations regarding grammars, that are used for all type of grammars (LL(1), LR(0), LR(1))
impl Grammar {
    /// Builds the grammar by reading its definition from a file identified by the path
    pub fn from_file(path: &str) -> Result<Self, String> {
        let file = fs::read_to_string(path);

        let contents: String = match file {
            Ok(s) => s,
            Err(e) => panic!("{}", e),
        };

        return Grammar::from_string(contents);
    }

    /// Builds the grammar from a given input string, which:
    /// - MUST have well-formatted productions of this form "LEFT_NON_TERMINAL->PRODUCTION_SYMBOLS"
    ///   where the left-hand side must be present, there must be no space between symbols, there
    ///   must be at least one production on the right-hand side
    pub fn from_string(s: String) -> Result<Self, String> {
        let mut grammar = Grammar {
            v_non_terminal: HashSet::new(),
            v_terminal: HashSet::new(),
            s: NonTerminal('S'),
            productions: HashMap::new(),
            has_e_rules: false,
        };

        for l in s.lines() {
            let line = l.trim();

            if line.is_empty() {
                continue;
            }

            let parts: Vec<&str> = l.split("->").collect();

            if parts.len() != 2 {
                return Err(format!("Syntax error in the Production: {}", line));
            }

            let mut production = Production {
                lhs: NonTerminal::from_str(parts[0]).expect("Could not parse Starter symbol."),
                alternatives: vec![],
            };

            grammar
                .v_non_terminal
                .insert(Symbol::NonTerminal(production.lhs));

            let rhs = parts[1];

            // parse the Production alternatives separated by "|" of the right-hand side of the
            // Production
            for alt_str in rhs.split('|') {
                if alt_str.trim().is_empty() {
                    return Err(format!("Empty alternative is not allowed. Use an explicit epsilon symbol or char 'e' instead."));
                }

                let mut current_alternative: Alternative = vec![];

                for token in alt_str.chars() {
                    match Symbol::from_str(token.to_string().as_str()) {
                        Ok(symbol) => {
                            current_alternative.push(symbol);

                            if symbol.is_terminal() {
                                grammar.v_terminal.insert(symbol);

                                if symbol == Symbol::Terminal(Terminal::Epsilon) {
                                    grammar.has_e_rules = true;
                                }
                            } else {
                                grammar.v_non_terminal.insert(symbol);
                            }
                        }
                        Err(e) => {
                            return Err(format!(
                                "Error parsing symbol '{}' in line '{}': {}",
                                token, line, e
                            ))
                        }
                    }
                }

                production.alternatives.push(current_alternative);
            }

            grammar.productions.insert(production.lhs, production);
        }

        return Ok(grammar);
    }

    fn display_non_terminals(&self) -> String {
        if self.v_non_terminal.is_empty() {
            "None".to_string()
        } else {
            let mut list: Vec<_> = self.v_non_terminal.iter().map(|s| s.to_string()).collect();
            list.sort();
            list.join(", ")
        }
    }

    fn display_terminals(&self) -> String {
        if self.v_terminal.is_empty() {
            "None".to_string()
        } else {
            let mut list: Vec<_> = self.v_terminal.iter().map(|s| s.to_string()).collect();
            list.sort();
            list.join(", ")
        }
    }

    pub fn to_vertical_table(&self) -> Table {
        let mut builder = builder::Builder::default();

        let headers = ["Start Symbol", "Has ε-Rules", "Non-Terminals", "Terminals"];
        let headers_values = [
            self.s.to_string(),
            self.has_e_rules.to_string(),
            self.display_non_terminals(),
            self.display_terminals(),
        ];

        for (header, value) in headers.iter().zip(headers_values.iter()) {
            builder.push_record([header.to_string(), value.to_string()]);
        }

        let mut productions_lines: Vec<(String, String)> = self
            .productions
            .iter()
            .map(|(lhs, _)| format!("Production for {}", lhs))
            .zip(self.productions.values().map(|p| p.to_string()))
            .collect();
productions_lines.sort();

        for (key, value) in productions_lines {
            builder.push_record([key, value]);
        }

        builder.build()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::fs;
    use std::path::PathBuf;
    use std::time::{SystemTime, UNIX_EPOCH};

    #[test]
    fn parses_grammar_from_well_written_string() {
        let template = "
            S->AB|B
            A->aA|d
            B->bB|c
        ";

        let grammar = Grammar::from_string(template.to_string()).unwrap();

        assert!(!grammar.has_e_rules);

        assert_eq!(
            grammar.v_terminal,
            HashSet::from_iter(vec![
                Symbol::Terminal(Terminal::Char('a')),
                Symbol::Terminal(Terminal::Char('b')),
                Symbol::Terminal(Terminal::Char('c')),
                Symbol::Terminal(Terminal::Char('d')),
            ])
        );

        assert_eq!(
            grammar.v_non_terminal,
            HashSet::from_iter(vec![
                Symbol::NonTerminal(NonTerminal('S')),
                Symbol::NonTerminal(NonTerminal('A')),
                Symbol::NonTerminal(NonTerminal('B')),
            ])
        );

        assert_eq!(grammar.s, NonTerminal('S'));

        let s_alts = &grammar
            .productions
            .get(&NonTerminal('S'))
            .expect("missing production for S")
            .alternatives;

        assert_eq!(
            s_alts,
            &vec![
                vec![
                    Symbol::NonTerminal(NonTerminal('A')),
                    Symbol::NonTerminal(NonTerminal('B'))
                ],
                vec![Symbol::NonTerminal(NonTerminal('B'))]
            ]
        );
    }

    #[test]
    fn successfully_parses_grammar_from_file() {
        let template = "
            S->AB|B
            A->aA|d
            B->bB|c
        ";

        let mut path = PathBuf::from(std::env::temp_dir());
        let stamp = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap()
            .as_millis();
        path.push(format!("grammar_test_{}.txt", stamp));

        fs::write(&path, template).expect("failed writing temp grammar file");
        let grammar = Grammar::from_file(&path.to_string_lossy()).unwrap();
        let _ = fs::remove_file(&path);

        assert_eq!(grammar.s, NonTerminal('S'));
        assert!(grammar.productions.contains_key(&NonTerminal('S')));
        assert!(grammar.productions.contains_key(&NonTerminal('A')));
        assert!(grammar.productions.contains_key(&NonTerminal('B')));

        assert_eq!(
            grammar.v_terminal,
            HashSet::from_iter(vec![
                Symbol::Terminal(Terminal::Char('a')),
                Symbol::Terminal(Terminal::Char('b')),
                Symbol::Terminal(Terminal::Char('c')),
                Symbol::Terminal(Terminal::Char('d')),
            ])
        );
    }

    #[test]
    fn rejects_trailing_empty_alternative_requires_explicit_epsilon() {
        let template = "
            S->AC
            A->a|
            B->b
            C->B|
        ";

        let result = Grammar::from_string(template.to_string());

        assert!(result.is_err());
    }

    #[test]
    fn vertical_table_contains_expected_rows() {
        let template = "
            S->AC
            A->a|e
            B->b
            C->B|e
        ";
        let grammar = Grammar::from_string(template.to_string()).unwrap();
        let table_str = grammar.to_vertical_table().to_string();

        assert!(table_str.contains("Start Symbol"));
        assert!(table_str.contains("S"));
        assert!(table_str.contains("Has ε-Rules"));
        assert!(table_str.contains("Non-Terminals"));
        assert!(table_str.contains("Terminals"));

        assert!(table_str.contains("Production for A"));
        assert!(table_str.contains("Production for B"));
        assert!(table_str.contains("Production for C"));
        assert!(table_str.contains("Production for S"));
    }
}

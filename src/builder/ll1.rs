use std::collections::{HashMap, HashSet};

use tabled::Table;

use crate::{
    builder::common::{
        calculate_all_first_sets, calculate_all_follow_sets, calculate_first_of_sequence,
    },
    model::{
        grammar::Grammar,
        types::{NonTerminal, Terminal},
    },
    parser::types::{LLParsingTable, ParsingAction},
};

/// By definition, a grammar is LL(1) if:
/// - in absence of e-rules, the Starter Symbols are disjoint
/// - in presence of e-rules, the Director Symbols are disjoint
/// Since the Starter Symbols are just a subset of the Director Symbols in absence of e-rules,
/// we can just use the Director Symbols and check if they are disjoint.
pub fn is_ll1(grammar: &Grammar) -> bool {
    if grammar.productions.is_empty() {
        return false;
    }

    let all_first_sets = calculate_all_first_sets(grammar);
    let all_follow_sets = calculate_all_follow_sets(grammar, &all_first_sets);

    for lhs in grammar.productions.keys() {
        let dss_per_alternative =
            match calculate_dss(grammar, lhs, &all_first_sets, &all_follow_sets) {
                Some(dss) if !dss.is_empty() => dss,
                _ => continue,
            };

        for i in 0..dss_per_alternative.len() {
            for j in (i + 1)..dss_per_alternative.len() {
                if !dss_per_alternative[i].is_disjoint(&dss_per_alternative[j]) {
                    return false;
                }
            }
        }
    }

    true
}

pub fn build_parsing_table(grammar: &Grammar) -> Option<LLParsingTable> {
    let mut table: LLParsingTable = HashMap::new();
    let all_first_sets = calculate_all_first_sets(grammar);
    let all_follow_sets = calculate_all_follow_sets(grammar, &all_first_sets);

    for (non_terminal, _) in &grammar.productions {
        let dss = match calculate_dss(grammar, non_terminal, &all_first_sets, &all_follow_sets) {
            Some(set) => set,
            None => continue,
        };

        for (alternative_index, set) in dss.iter().enumerate() {
            for terminal in set {
                let key = (*non_terminal, *terminal);

                if let Some(record) = table.get_mut(&key) {
                    record.push(ParsingAction::Production(alternative_index));
                } else {
                    table.insert(key, vec![ParsingAction::Production(alternative_index)]);
                }
            }
        }
    }

    Some(table)
}

pub fn to_printable_table(grammar: &Grammar) -> Option<Table> {
    let table = build_parsing_table(grammar)?;

    let mut builder = tabled::builder::Builder::default();

    let mut header = vec!["PARSING TABLE (NT/T)".to_string()];
    let mut terminals: Vec<Terminal> = grammar
        .v_terminal
        .iter()
        .filter_map(|s| Terminal::try_from(*s).ok())
        .collect();
    terminals.sort();
    terminals.push(Terminal::EOF);

    for t in &terminals {
        header.push(format!("{}", t));
    }
    builder.push_record(header);

    let mut non_terminals: Vec<NonTerminal> = grammar
        .v_non_terminal
        .iter()
        .filter_map(|s| NonTerminal::try_from(*s).ok())
        .collect();
    non_terminals.sort();

    for nt in &non_terminals {
        let mut row = vec![format!("{}", nt)];

        for t in &terminals {
            let actions = match table.get(&(*nt, *t)) {
                Some(a) => a,
                _ => {
                    row.push("-".to_string());
                    continue;
                }
            };

            if actions.is_empty() {
                row.push("-".to_string());
                continue;
            }

            let cell = match table.get(&(*nt, *t)) {
                Some(actions) if !actions.is_empty() => {
                    let productions: Vec<String> = actions
                        .iter()
                        .filter_map(|action| match action {
                            ParsingAction::Production(index) => {
                                grammar.productions.get(nt).map(|prod| {
                                    prod.alternatives[*index]
                                        .iter()
                                        .map(|s| s.to_string())
                                        .collect::<String>()
                                })
                            }
                            _ => Some("error".to_string()),
                        })
                        .collect();

                    productions
                        .iter()
                        .map(|prod| {
                            if productions.len() == 1 {
                                format!("{} → {}", nt, prod)
                            } else {
                                format!("⚠️ {} → {}", nt, prod)
                            }
                        })
                        .collect::<Vec<_>>()
                        .join("\n")
                }
                _ => "-".to_string(),
            };

            row.push(cell);
        }

        builder.push_record(row);
    }

    Some(builder.build())
}

fn calculate_dss(
    grammar: &Grammar,
    alpha: &NonTerminal,
    all_first_sets: &HashMap<NonTerminal, (HashSet<Terminal>, bool)>,
    all_follow_sets: &HashMap<NonTerminal, HashSet<Terminal>>,
) -> Option<Vec<HashSet<Terminal>>> {
    let production = match grammar.productions.get(alpha) {
        Some(p) => p,
        None => return None,
    };

    let mut sets: Vec<HashSet<Terminal>> = vec![];

    for alternative in &production.alternatives {
        let (mut first_alpha, is_nullable) =
            calculate_first_of_sequence(alternative, &all_first_sets);

        first_alpha.remove(&Terminal::Epsilon);

        if is_nullable {
            if let Some(follow_a) = all_follow_sets.get(alpha) {
                first_alpha.extend(follow_a.iter())
            }
        }

        sets.push(first_alpha);
    }

    Some(sets)
}

#[cfg(test)]
pub mod tests {
    use super::*;

    #[test]
    fn correctly_detects_a_ll1_grammar_with_disjoint_sets() {
        let template = "
            S->AC
            A->a|e
            B->b
            C->B|e
        ";

        let grammar = Grammar::from_string(template.to_string()).unwrap();

        assert!(is_ll1(&grammar));
    }

    #[test]
    fn correctly_detects_a_non_ll1_grammar_with_non_disjoint_sets() {
        let template = "
            S->AB
            A->BC|DF
            B->bB|d
            C->cC|f
            D->dD|e
            F->fF|e
        ";
        let grammar = Grammar::from_string(template.to_string()).unwrap();

        assert!(!is_ll1(&grammar));
    }
}

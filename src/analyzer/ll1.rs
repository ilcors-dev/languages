use std::collections::{HashMap, HashSet};

use tabled::Table;

use crate::{
    model::{
        grammar::Grammar,
        types::{NonTerminal, Symbol, Terminal},
    },
    parser::types::{ParsingAction, ParsingTable},
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

pub fn build_parsing_table(grammar: &Grammar) -> Option<ParsingTable> {
    let mut table: ParsingTable = HashMap::new();
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

pub fn to_parsing_table(grammar: &Grammar) -> Option<Table> {
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

fn calculate_all_first_sets(grammar: &Grammar) -> HashMap<NonTerminal, (HashSet<Terminal>, bool)> {
    let mut first_sets: HashMap<NonTerminal, (HashSet<Terminal>, bool)> = HashMap::new();

    for nt in &grammar.v_non_terminal {
        first_sets.insert(
            NonTerminal::try_from(*nt).expect("Expected a non-terminal."),
            (HashSet::new(), false),
        );
    }

    let mut changed = true;

    while changed {
        changed = false;

        for nt in grammar
            .v_non_terminal
            .iter()
            .filter_map(|s| NonTerminal::try_from(*s).ok())
        {
            let production = grammar
                .productions
                .get(&nt)
                .expect(format!("Production for {} not found", nt).as_str());

            let (current_set, is_nullable) = first_sets.get(&nt).unwrap();
            let old_size = current_set.len();
            let old_nullable = *is_nullable;

            let mut new_first_sets = current_set.clone();
            let mut new_is_nullable = old_nullable;

            for alternative in &production.alternatives {
                if alternative.is_empty() {
                    new_first_sets.insert(Terminal::Epsilon);
                    new_is_nullable = true;
                    continue;
                }

                let (first_of_alternative, is_first_of_alternative_nullable) =
                    calculate_first_of_sequence(&alternative, &first_sets);

                new_first_sets.extend(first_of_alternative);

                if is_first_of_alternative_nullable {
                    new_is_nullable = true;
                }
            }

            if new_first_sets.len() > old_size || new_is_nullable != old_nullable {
                changed = true;
                *first_sets.get_mut(&nt).unwrap() = (new_first_sets, new_is_nullable);
            }
        }
    }

    first_sets
}

fn calculate_first_of_sequence(
    sequence: &[Symbol],
    current_first_sets: &HashMap<NonTerminal, (HashSet<Terminal>, bool)>,
) -> (HashSet<Terminal>, bool) {
    let mut terminals: HashSet<Terminal> = HashSet::new();
    let mut is_sequence_nullable = true;

    for x_i in sequence {
        match x_i {
            Symbol::Terminal(terminal) => {
                terminals.insert(*terminal);
                if *terminal != Terminal::Epsilon {
                    is_sequence_nullable = false;
                    break;
                }
            }
            Symbol::NonTerminal(non_terminal) => {
                if let Some((first_xi, is_nullable)) = current_first_sets.get(non_terminal) {
                    terminals.extend(first_xi.iter().filter(|t| **t != Terminal::Epsilon));
                    if !is_nullable {
                        is_sequence_nullable = false;
                        break;
                    }
                } else {
                    is_sequence_nullable = false;
                    break;
                }
            }
        }
    }

    if is_sequence_nullable {
        terminals.insert(Terminal::Epsilon);
    }

    (terminals, is_sequence_nullable)
}

fn calculate_all_follow_sets(
    grammar: &Grammar,
    all_first_sets: &HashMap<NonTerminal, (HashSet<Terminal>, bool)>,
) -> HashMap<NonTerminal, HashSet<Terminal>> {
    let mut follow_sets: HashMap<NonTerminal, HashSet<Terminal>> = HashMap::new();

    for nt in &grammar.v_non_terminal {
        follow_sets.insert(
            NonTerminal::try_from(*nt).expect("Expected a non-terminal."),
            HashSet::new(),
        );
    }

    follow_sets
        .entry(grammar.s)
        .or_insert_with(HashSet::new)
        .insert(Terminal::EOF);

    let mut changed = true;

    while changed {
        changed = false;

        for (b, production) in &grammar.productions {
            for alpha_i in &production.alternatives {
                for (i, symbol_a) in alpha_i.iter().enumerate() {
                    if let Symbol::NonTerminal(a) = symbol_a {
                        let mut new_symbols_to_add: HashSet<Terminal> = HashSet::new();
                        let beta = &alpha_i[i + 1..];

                        if !beta.is_empty() {
                            let (first_beta, beta_nullable) =
                                calculate_first_of_sequence(beta, &all_first_sets);

                            new_symbols_to_add
                                .extend(first_beta.iter().filter(|t| **t != Terminal::Epsilon));

                            if beta_nullable {
                                if let Some(follow_b) = follow_sets.get(b) {
                                    new_symbols_to_add.extend(follow_b);
                                }
                            }
                        } else {
                            if let Some(follow_b) = follow_sets.get(b) {
                                new_symbols_to_add.extend(follow_b);
                            }
                        }
                        let follow_a = follow_sets.entry(*a).or_insert_with(HashSet::new);
                        let initial_size = follow_a.len();

                        follow_a.extend(new_symbols_to_add);

                        if follow_a.len() > initial_size {
                            changed = true;
                        }
                    }
                }
            }
        }
    }

    follow_sets
}

pub fn to_first_set_table(grammar: &Grammar) -> Table {
    let first_set = calculate_all_first_sets(grammar);

    let mut builder = tabled::builder::Builder::default();
    let header = vec!["FIRST SET OF", "NT"];
    builder.push_record(header);

    let mut sorted_first_set: Vec<_> = first_set.iter().collect();
    sorted_first_set.sort_by_key(|(nt, _)| *nt);

    for (nt, set) in sorted_first_set {
        let mut terminals = set.0.iter().map(|t| t.to_string()).collect::<Vec<_>>();
        terminals.sort();
        builder.push_record(vec![
            format!("FIRST({})", nt),
            format!(
                "{} (is_nullable: {})",
                terminals.join(" "),
                set.1.to_string()
            ),
        ]);
    }

    builder.build()
}

pub fn to_follow_set_table(grammar: &Grammar) -> Table {
    let all_first_sets = calculate_all_first_sets(grammar);
    let follow_set = calculate_all_follow_sets(grammar, &all_first_sets);

    let mut builder = tabled::builder::Builder::default();
    let header = vec!["FOLLOW SET OF", "T"];
    builder.push_record(header);

    let mut sorted_follow_set: Vec<_> = follow_set.iter().collect();
    sorted_follow_set.sort_by_key(|(nt, _)| *nt);

    for (nt, set) in sorted_follow_set {
        let mut terminals = set.iter().collect::<Vec<_>>();
        terminals.sort();
        builder.push_record(vec![
            format!("FOLLOW({})", nt),
            format!(
                "{}",
                terminals
                    .iter()
                    .map(|t| t.to_string())
                    .collect::<Vec<String>>()
                    .join(" ")
            ),
        ]);
    }

    builder.build()
}

#[cfg(test)]
pub mod tests {
    use super::*;
    use crate::model::{
        grammar::Grammar,
        types::{NonTerminal, Terminal},
    };
    use std::collections::HashSet;

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

    #[test]
    fn calculates_first_set_with_no_epsilon() {
        let template = "
            S->AC
            A->aC|B
            B->b
            C->b
        ";

        let grammar = Grammar::from_string(template.to_string()).unwrap();

        let first_sets = calculate_all_first_sets(&grammar);
        let (first_set, is_nullable) = first_sets.get(&NonTerminal('S')).unwrap();

        assert_eq!(
            *first_set,
            HashSet::from_iter(vec![Terminal::Char('a'), Terminal::Char('b')])
        );
        assert!(!is_nullable);
    }

    #[test]
    fn calculates_empty_first_set_on_missing_production() {
        let template = "
            S->AC
            A->aC|B
            B->b
            C->b
        ";

        let grammar = Grammar::from_string(template.to_string()).unwrap();

        let first_sets = calculate_all_first_sets(&grammar);
        let result = first_sets.get(&NonTerminal('D'));

        assert!(result.is_none());
    }

    #[test]
    fn calculates_first_set_and_nullability_with_explicit_epsilon() {
        let template = "
            S->AC
            A->a|e
            B->b
            C->B|e
        ";

        let grammar = Grammar::from_string(template.to_string()).unwrap();
        let first_sets = calculate_all_first_sets(&grammar);

        let (a_first, a_nullable) = first_sets.get(&NonTerminal('A')).expect("FIRST(A) missing");
        assert_eq!(
            *a_first,
            HashSet::from_iter(vec![Terminal::Char('a'), Terminal::Epsilon])
        );
        assert!(*a_nullable);

        let (b_first, b_nullable) = first_sets.get(&NonTerminal('B')).expect("FIRST(B) missing");
        assert_eq!(*b_first, HashSet::from_iter(vec![Terminal::Char('b')]));
        assert!(!*b_nullable);

        let (c_first, c_nullable) = first_sets.get(&NonTerminal('C')).expect("FIRST(C) missing");
        assert_eq!(
            *c_first,
            HashSet::from_iter(vec![Terminal::Char('b'), Terminal::Epsilon])
        );
        assert!(*c_nullable);
    }

    #[test]
    fn calculates_follow_sets_with_explicit_epsilon() {
        let template = "
            S->AC
            A->a|e
            B->b
            C->B|e
        ";

        let grammar = Grammar::from_string(template.to_string()).unwrap();
        let first_sets = calculate_all_first_sets(&grammar);
        let follow = calculate_all_follow_sets(&grammar, &first_sets);

        assert_eq!(
            follow.get(&NonTerminal('S')).cloned().unwrap_or_default(),
            HashSet::from_iter(vec![Terminal::EOF])
        );

        assert_eq!(
            follow.get(&NonTerminal('A')).cloned().unwrap_or_default(),
            HashSet::from_iter(vec![Terminal::Char('b'), Terminal::EOF])
        );

        assert_eq!(
            follow.get(&NonTerminal('C')).cloned().unwrap_or_default(),
            HashSet::from_iter(vec![Terminal::EOF])
        );

        assert_eq!(
            follow.get(&NonTerminal('B')).cloned().unwrap_or_default(),
            HashSet::from_iter(vec![Terminal::EOF])
        );
    }
}


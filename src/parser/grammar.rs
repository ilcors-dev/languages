use std::collections::HashSet;
use std::{cell::OnceCell, collections::HashMap, fs};

use tabled::{builder, Table};

use crate::model::types::{Alternative, NonTerminal, Production, Symbol, Terminal};

#[derive(Debug)]
pub struct Grammar {
    pub v_non_terminal: HashSet<Symbol>,
    pub v_terminal: HashSet<Symbol>,
    pub s: NonTerminal,
    pub productions: HashMap<NonTerminal, Production>,
    pub has_e_rules: bool,

    first_cache: OnceCell<HashMap<NonTerminal, (HashSet<Terminal>, bool)>>,
    follow_cache: OnceCell<HashMap<NonTerminal, HashSet<Terminal>>>,
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
            s: NonTerminal::S,
            productions: HashMap::new(),
            has_e_rules: false,

            first_cache: OnceCell::new(),
            follow_cache: OnceCell::new(),
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
            for alt_str in rhs.split("|") {
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

    /// Calculates the Director Symbol Set for each production in the Grammar
    /// The Director Symbol Set is defined as follows:
    ///
    /// \[
    /// DS(A\rightarrow\alpha) =
    /// \begin{cases}
    /// SS(\alpha), \mathrm{if }\alpha\mathrm{ does not generate }\epsilon\\
    /// SS(\alpha)\cup FOLLOW(A), \mathrm{if }\alpha\mathrm{ generates }\epsilon\\
    /// \end{cases}
    /// \]
    ///
    /// or
    ///
    /// \[
    /// DS\(A\rightarrow\alpha\)=trunc_1(FIRST(\alpha)\cdot FOLLOW(A))
    /// \]
    ///
    /// Where \( FOLLOW \) is:
    ///
    /// \[
    /// FOLLOW(A)=\{a\in V_T|S\overset{*}{\Rightarrow}\gamma Aa\beta\}, \gamma,\beta\in V^*
    /// \]
    pub fn all_dss(&self) -> Option<HashMap<NonTerminal, Vec<HashSet<Terminal>>>> {
        if self.productions.is_empty() {
            return None;
        }

        let mut dss: HashMap<NonTerminal, Vec<HashSet<Terminal>>> = HashMap::new();

        for k in self.productions.keys() {
            if let Some(r) = self.calculate_dss(k) {
                if !r.is_empty() {
                    dss.insert(*k, r);
                }
            }
        }

        Some(dss)
    }

    /// Calculates the Director Symbols Set for a non-terminal, returning a vector of sets.
    ///
    /// The DSS is defined by:
    ///
    /// \[
    /// DS(A\rightarrow\alpha)=
    /// \begin{case}
    /// SS(\alpha), \mathrm{if }\alpha\mathrm{ does not generate }\epsilon\\
    /// SS(\alpha)\cup FOLLOW(A), \mathrm{if }\alpha\mathrm{ generates }\epsilon\\
    /// \end{case}
    /// \]
    ///
    /// where \(FOLLOW\) contains the symbols that can "follow" the "sentence" generated by the
    /// meta-symbol \(A\)
    ///
    /// \[
    /// FOLLOW(A)=\{a\in V_T|S\overset{*}{\Rightarrow}\gamma Aa\beta\}, \gamma,\beta\in V^*
    /// \]
    pub fn calculate_dss(&self, alpha: &NonTerminal) -> Option<Vec<HashSet<Terminal>>> {
        let production = match self.productions.get(alpha) {
            Some(p) => p,
            None => return None,
        };

        let all_first_sets = self.get_first_sets();
        let all_follow_sets = self.get_follow_sets();

        let mut sets: Vec<HashSet<Terminal>> = vec![];

        for alternative in &production.alternatives {
            let (mut first_alpha, is_nullable) =
                self.calculate_first_of_sequence(alternative, &all_first_sets);

            // \( FIRST(\alpha)\setminus\epsilon \)
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

    pub fn get_first_sets(&self) -> &HashMap<NonTerminal, (HashSet<Terminal>, bool)> {
        self.first_cache
            .get_or_init(|| self._calculate_all_first_sets())
    }

    pub fn get_follow_sets(&self) -> &HashMap<NonTerminal, HashSet<Terminal>> {
        self.follow_cache
            .get_or_init(|| self._calculate_all_follow_sets())
    }

    /// Calculates the FIRST set of the grammar.
    ///
    /// The FIRST set are the defined initials of a sentential form \(\alpha\) that are derived by
    /// applying one or more productions
    ///
    /// Formally:
    ///
    /// \[
    /// FIRST(\alpha)=trunc_1(\{x\in V^*_T|\alpha\overset{*}{\Rightarrow} \alpha\in x\}), \alpha\in V^*
    /// \]
    fn _calculate_all_first_sets(&self) -> HashMap<NonTerminal, (HashSet<Terminal>, bool)> {
        let mut first_sets: HashMap<NonTerminal, (HashSet<Terminal>, bool)> = HashMap::new();

        for nt in &self.v_non_terminal {
            first_sets.insert(
                NonTerminal::try_from(*nt).expect("Expected a non-terminal."),
                (HashSet::new(), false),
            );
        }

        let mut changed = true;

        while changed {
            changed = false;

            for nt in self
                .v_non_terminal
                .iter()
                .filter_map(|s| NonTerminal::try_from(*s).ok())
            {
                let production = self
                    .productions
                    .get(&nt)
                    .expect(format!("Production for {} not found", nt).as_str());

                let old_size = first_sets
                    .get(&nt)
                    .expect(format!("FIRST set for {} not found", nt).as_str())
                    .0
                    .len();
                let old_nullable = first_sets
                    .get(&nt)
                    .expect(format!("FIRST set for {} not found", nt).as_str())
                    .1;

                let mut new_first_sets = first_sets
                    .get(&nt)
                    .expect(format!("FIRST set for {} not found", nt).as_str())
                    .0
                    .clone();
                let mut new_is_nullable = first_sets
                    .get(&nt)
                    .expect(format!("FIRST set for {} not found", nt).as_str())
                    .1
                    .clone();

                for alternative in &production.alternatives {
                    if alternative.is_empty() {
                        new_first_sets.insert(Terminal::Epsilon);
                        new_is_nullable = true;
                        continue;
                    }

                    let (first_of_alternative, is_first_of_alternative_nullable) =
                        self.calculate_first_of_sequence(&alternative, &first_sets);

                    new_first_sets.extend(first_of_alternative);

                    if is_first_of_alternative_nullable {
                        new_is_nullable = true;
                    }
                }

                // is something changed?
                if new_first_sets.len() > old_size || new_is_nullable != old_nullable {
                    changed = true;
                    *first_sets
                        .get_mut(&nt)
                        .expect(format!("FIRST set for {} not found", nt).as_str()) =
                        (new_first_sets, new_is_nullable);
                }
            }
        }

        first_sets
    }

    /// Calculates, for the given sequence, the FIRST defined as:
    ///
    /// FIRST(\alpha)=trunc_1(\{x\in V^*_T|\alpha\overset{*}{\Rightarrow} \alpha\in x\}), \alpha\in V^*
    ///
    /// Explaination, we have these cases to cover:
    /// 1. The first item in the sequence is a terminal. In this case we are done, no need to
    ///    expand the other non-terminal symbols
    /// 2. The items in the sequence are non-terminals. In this case we need to continue to expand
    ///    until we find a terminal symbol, or we end up consuming the whole sequence
    fn calculate_first_of_sequence(
        &self,
        sequence: &[Symbol],
        current_first_sets: &HashMap<NonTerminal, (HashSet<Terminal>, bool)>,
    ) -> (HashSet<Terminal>, bool) {
        let mut terminals: HashSet<Terminal> = HashSet::new();

        // does the production contain an e-symbol? does
        // it lead to e-rules?
        let mut is_sequence_nullable = true;

        for x_i in sequence {
            match x_i {
                // CASE 1: first element is a terminal symbol \( X_1=a\in V_T \)
                // CASE 1a: is it not an EPSILON? if so we should return immediately
                Symbol::Terminal(terminal) => {
                    terminals.insert(*terminal);

                    // if we don't encounter an e-symbol, it means that the sequence is not
                    // nullable, therefore we should not then include the e-rule in the
                    // FIRST set
                    if *terminal != Terminal::Epsilon {
                        is_sequence_nullable = false;

                        break;
                    }
                }
                // CASE 3: \( \alpha=X_1\cdot X_2\cdot..X_n \)
                // here we evaluate the components of the production, until we either
                // (1) consume them all, that is, we only find non-terminals
                // (2) we encounter a terminal element
                Symbol::NonTerminal(non_terminal) => {
                    if let Some((first_xi, is_nullable)) = current_first_sets.get(non_terminal) {
                        terminals.extend(first_xi);
                        terminals.remove(&Terminal::Epsilon);

                        // if X_i does not lead to an e-symbol (therefore is nullable), we can end it
                        // here
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

    /// Calculates every follow set for each production.
    ///
    /// The FOLLOW set is defined by:
    ///
    /// \[
    /// FOLLOW(A)=\{a\in V_T|S\overset{*}{\Rightarrow}\gamma Aa\beta\}, \gamma,\beta\in V^*
    /// \]
    ///
    /// Which means we need to find, given \( FOLLOW(A) \), the set of terminals of a given
    /// non-terminal \( A \) (including the end-of-input marker $ or end-of-file EOF) that can appear
    /// immediately after \( A \) in any valid derivation starting from the grammar's start symbol.
    /// This excluded non-terminals and the empty string epsilon, focusing only on concrete symbols
    /// the parser can match in the input stream.
    ///
    /// Why this matters?
    /// Because it allows the top-down parsers to have precise lookahead information (like LL(1)
    /// parsers) helping them decide when to apply e-rules or recover from errors without
    /// ambiguity.
    /// For example, if \( FOLLOW(A)=\{;,$\} \), the parser expects a semicolon or EOF right after
    /// reducing \( A \), directly tying to derivation paths like
    /// \( S\overset{*}{\Rightarrow}\gamma A;\beta \)
    fn _calculate_all_follow_sets(&self) -> HashMap<NonTerminal, HashSet<Terminal>> {
        let all_first_sets = self.get_first_sets();
        let mut follow_sets: HashMap<NonTerminal, HashSet<Terminal>> = HashMap::new();

        for nt in &self.v_non_terminal {
            follow_sets.insert(
                NonTerminal::try_from(*nt).expect("Expected a non-terminal."),
                HashSet::new(),
            );
        }

        follow_sets
            .entry(self.s)
            .or_insert_with(HashSet::new)
            .insert(Terminal::EOF);

        let mut changed = true;

        while changed {
            changed = false;

            for (b, production) in &self.productions {
                for alpha_i in &production.alternatives {
                    for (i, symbol_a) in alpha_i.iter().enumerate() {
                        if let Symbol::NonTerminal(a) = symbol_a {
                            let mut new_symbols_to_add: HashSet<Terminal> = HashSet::new();
                            let beta = &alpha_i[i + 1..];

                            // if there are symbols after the given alpha, we expand them.
                            // we can do this by evaluating the FIRST set and add it minus the
                            // e-symbol if present, because we want to keep only concrete terminals
                            // (not epsilon)
                            //
                            // if there are NO symbols after the given alpha or the FIRST set is
                            // nullable (aka beta can lead to an e-symbol), it means that beta disappears,
                            // allowing terminals to immediately follow A.
                            //
                            // this handles indirect followers where \( \beta\overset{*}{\Rightarrow}\epsilon) \)
                            // allowing the algorithm to capture terminals \( a \) that appear
                            // after \( A \) via chained derivations like
                            // \[
                            // S\overset{*}{\Rightarrow}\gamma A\beta ..\overset{*}{\Rightarrow}\gamma A\epsilon a\beta
                            // \]
                            // where \( a \) originally follows B, but now immediately follows A.
                            //
                            // Example grammar:
                            // \[
                            // S\rightarrow AC \mathrm{start: S; non-terminals A,B,C; terminals a,b,$}\\
                            // A\rightarrow a|\epsilon \mathrm{A nullable}\\
                            // B\rightarrow b
                            // C\rightarrow B|\epsilon \mathrm{C nullable, derives to B or \epsilon}
                            // \]
                            //
                            // Deriving the grammar:
                            //
                            // \[
                            // S\Rightarrow AC\Rightarrow aC \mathrm{direct: a follows nothing new}\\
                            // S\Rightarrow AC\Rightarrow \epsilon C\Rightarrow C \mathrm{A derives epsilon, so C follows A}
                            // S\Rightarrow\epsilon C\Rightarrow\epsilon B \mathrm{C\Rightarrow B, so b follows A indirectly}
                            // \]
                            if !beta.is_empty() {
                                let (first_beta, beta_nullable) =
                                    self.calculate_first_of_sequence(beta, &all_first_sets);

                                // first rule: Add \( FIRST(\beta) \setminus {\epsilon} \)
                                new_symbols_to_add
                                    .extend(first_beta.iter().filter(|t| **t != Terminal::Epsilon));

                                // second rule: if \( \beta \) is nullable, we need to add it
                                if beta_nullable {
                                    if let Some(follow_b) = follow_sets.get(b) {
                                        new_symbols_to_add.extend(follow_b);
                                    }
                                }
                            } else {
                                // second rule: if \( \beta \) is empty
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

    pub fn to_first_set_table(&self) -> Table {
        let first_set = self.get_first_sets();

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

    pub fn to_follow_set_table(&self) -> Table {
        let follow_set = self.get_follow_sets();

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
                Symbol::Terminal(Terminal::AChar),
                Symbol::Terminal(Terminal::BChar),
                Symbol::Terminal(Terminal::CChar),
                Symbol::Terminal(Terminal::DChar),
            ])
        );

        assert_eq!(
            grammar.v_non_terminal,
            HashSet::from_iter(vec![
                Symbol::NonTerminal(NonTerminal::S),
                Symbol::NonTerminal(NonTerminal::A),
                Symbol::NonTerminal(NonTerminal::B),
            ])
        );

        assert_eq!(grammar.s, NonTerminal::S);

        let s_alts = &grammar
            .productions
            .get(&NonTerminal::S)
            .expect("missing production for S")
            .alternatives;

        assert_eq!(
            s_alts,
            &vec![
                vec![
                    Symbol::NonTerminal(NonTerminal::A),
                    Symbol::NonTerminal(NonTerminal::B)
                ],
                vec![Symbol::NonTerminal(NonTerminal::B)]
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

        assert_eq!(grammar.s, NonTerminal::S);
        assert!(grammar.productions.contains_key(&NonTerminal::S));
        assert!(grammar.productions.contains_key(&NonTerminal::A));
        assert!(grammar.productions.contains_key(&NonTerminal::B));

        assert_eq!(
            grammar.v_terminal,
            HashSet::from_iter(vec![
                Symbol::Terminal(Terminal::AChar),
                Symbol::Terminal(Terminal::BChar),
                Symbol::Terminal(Terminal::CChar),
                Symbol::Terminal(Terminal::DChar),
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
    fn calculates_first_set_with_no_epsilon() {
        let template = "
            S->AC
            A->aC|B
            B->b
            C->b
        ";

        let grammar = Grammar::from_string(template.to_string()).unwrap();

        let first_sets = grammar.get_first_sets();
        let (first_set, is_nullable) = first_sets.get(&NonTerminal::S).unwrap();

        assert_eq!(
            *first_set,
            HashSet::from_iter(vec![Terminal::AChar, Terminal::BChar])
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

        let first_sets = grammar.get_first_sets();
        let result = first_sets.get(&NonTerminal::D);

        assert!(result.is_none());
    }

    #[test]
    fn calculates_first_set_and_nullability_with_explicit_epsilon() {
        // Explicit ε:
        // S -> A C
        // A -> a | ε
        // B -> b
        // C -> B | ε
        let template = "
            S->AC
            A->a|e
            B->b
            C->B|e
        ";

        let grammar = Grammar::from_string(template.to_string()).unwrap();
        let first_sets = grammar.get_first_sets();

        // FIRST(A) = { a, ε }, nullable
        let (a_first, a_nullable) = first_sets.get(&NonTerminal::A).expect("FIRST(A) missing");
        assert_eq!(
            *a_first,
            HashSet::from_iter(vec![Terminal::AChar, Terminal::Epsilon])
        );
        assert!(a_nullable);

        // FIRST(B) = { b }, not nullable
        let (b_first, b_nullable) = first_sets.get(&NonTerminal::B).expect("FIRST(B) missing");
        assert_eq!(*b_first, HashSet::from_iter(vec![Terminal::BChar]));
        assert!(!b_nullable);

        // FIRST(C) = FIRST(B) ∪ {ε} = { b, ε }, nullable
        let (c_first, c_nullable) = first_sets.get(&NonTerminal::C).expect("FIRST(C) missing");
        assert_eq!(
            *c_first,
            HashSet::from_iter(vec![Terminal::BChar, Terminal::Epsilon])
        );
        assert!(c_nullable);
    }

    #[test]
    fn calculates_follow_sets_with_explicit_epsilon() {
        // Same explicit-ε grammar:
        // S -> A C
        // A -> a | ε
        // B -> b
        // C -> B | ε
        //
        // FOLLOW(S) = { EOF }
        // FOLLOW(A) = FIRST(C)\{ε} ∪ FOLLOW(S) (since C nullable) = { b } ∪ { EOF } = { b, EOF }
        // FOLLOW(C) = FOLLOW(S) (C at end of S->AC) = { EOF }
        // FOLLOW(B) = FOLLOW(C) (B at end of C->B) = { EOF }
        let template = "
            S->AC
            A->a|e
            B->b
            C->B|e
        ";

        let grammar = Grammar::from_string(template.to_string()).unwrap();
        let follow = grammar.get_follow_sets();

        assert_eq!(
            follow.get(&NonTerminal::S).cloned().unwrap_or_default(),
            HashSet::from_iter(vec![Terminal::EOF])
        );

        assert_eq!(
            follow.get(&NonTerminal::A).cloned().unwrap_or_default(),
            HashSet::from_iter(vec![Terminal::BChar, Terminal::EOF])
        );

        assert_eq!(
            follow.get(&NonTerminal::C).cloned().unwrap_or_default(),
            HashSet::from_iter(vec![Terminal::EOF])
        );

        assert_eq!(
            follow.get(&NonTerminal::B).cloned().unwrap_or_default(),
            HashSet::from_iter(vec![Terminal::EOF])
        );
    }

    #[test]
    fn calculates_empty_dss_on_missing_production() {
        let template = "
            S->AC
            A->aC|B
            B->b
            C->b
        ";

        let grammar = Grammar::from_string(template.to_string()).unwrap();

        let result = grammar.calculate_dss(&NonTerminal::D);

        assert!(result.is_none());
    }

    #[test]
    fn does_not_include_follow_sets_without_epsilon_in_grammar() {
        let template = "
            S->AC
            A->aC|B
            B->b
            C->b
        ";

        let grammar = Grammar::from_string(template.to_string()).unwrap();

        let dss_a = grammar.calculate_dss(&NonTerminal::A).unwrap();

        assert_eq!(dss_a.len(), 2);
        assert_eq!(dss_a[0], HashSet::from_iter(vec![Terminal::AChar]));
        assert_eq!(dss_a[1], HashSet::from_iter(vec![Terminal::BChar]));
    }

    #[test]
    fn calculates_dss_for_nullable_and_nonnullable_with_explicit_epsilon() {
        // With explicit ε:
        // A -> a | ε
        // For A->a (non-nullable), DS = FIRST(a) = { a }
        // For A->ε (nullable), DS = FIRST(ε)\{ε} ∪ FOLLOW(A) = ∅ ∪ { b, EOF } = { b, EOF }
        let template = "
            S->AC
            A->a|e
            B->b
            C->B|e
        ";

        let grammar = Grammar::from_string(template.to_string()).unwrap();
        let dss_a = grammar
            .calculate_dss(&NonTerminal::A)
            .expect("DSS(A) missing");

        assert_eq!(dss_a.len(), 2);
        assert_eq!(dss_a[0], HashSet::from_iter(vec![Terminal::AChar]));
        assert_eq!(
            dss_a[1],
            HashSet::from_iter(vec![Terminal::BChar, Terminal::EOF])
        );

        let all = grammar.all_dss().expect("all DSS missing");
        assert!(all.contains_key(&NonTerminal::A));
        assert!(all.contains_key(&NonTerminal::S));
        assert!(all.contains_key(&NonTerminal::C));
        assert!(all.contains_key(&NonTerminal::B));
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

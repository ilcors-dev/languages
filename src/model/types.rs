use std::fmt::Display;

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum Terminal {
    Char(char),
    Epsilon,
    EOF,
}

impl Display for Terminal {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Terminal::Char(c) => write!(f, "{}", c),
            Terminal::Epsilon => write!(f, "ε"),
            Terminal::EOF => write!(f, "$"),
        }
    }
}

impl TryFrom<Symbol> for Terminal {
    type Error = String;

    fn try_from(value: Symbol) -> Result<Self, Self::Error> {
        match value {
            Symbol::Terminal(t) => Ok(t),
            Symbol::NonTerminal(nt) => {
                Err(format!("Cannot convert NonTerminal {:?} to Terminal", nt))
            }
        }
    }
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct NonTerminal(pub char);

impl NonTerminal {
    pub fn from_str(s: &str) -> Result<Self, String> {
        let trimmed = s.trim();
        if trimmed.chars().count() == 1 {
            let c = trimmed.chars().next().unwrap();
            if c.is_ascii_uppercase() {
                Ok(NonTerminal(c))
            } else {
                Err(format!("NonTerminal must be an uppercase character: {}", s))
            }
        } else {
            Err(format!("NonTerminal must be a single character: {}", s))
        }
    }
}

impl Display for NonTerminal {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0)
    }
}

impl TryFrom<Symbol> for NonTerminal {
    type Error = String;

    fn try_from(value: Symbol) -> Result<Self, Self::Error> {
        match value {
            Symbol::NonTerminal(nt) => Ok(nt),
            Symbol::Terminal(t) => Err(format!("Cannot convert Terminal {:?} to NonTerminal", t)),
        }
    }
}

#[derive(Debug, Eq, Hash, PartialEq, Copy, Clone, PartialOrd, Ord)]
pub enum Symbol {
    Terminal(Terminal),
    NonTerminal(NonTerminal),
}

impl Symbol {
    pub fn from_str(s: &str) -> Result<Self, String> {
        let trimmed = s.trim();
        if trimmed.chars().count() != 1 {
            return Err(format!("Symbol must be a single character: '{}'", s));
        }
        let c = trimmed.chars().next().unwrap();

        if c.is_ascii_uppercase() {
            Ok(Symbol::NonTerminal(NonTerminal(c)))
        } else if c.is_ascii_lowercase() {
            if c == 'e' {
                Ok(Symbol::Terminal(Terminal::Epsilon))
            } else {
                Ok(Symbol::Terminal(Terminal::Char(c)))
            }
        } else if c.is_ascii_digit() {
            Ok(Symbol::Terminal(Terminal::Char(c)))
        } else {
            match c {
                'ε' => Ok(Symbol::Terminal(Terminal::Epsilon)),
                '$' => Ok(Symbol::Terminal(Terminal::EOF)),
                _ => Ok(Symbol::Terminal(Terminal::Char(c))),
            }
        }
    }

    pub fn is_terminal(&self) -> bool {
        matches!(self, Symbol::Terminal(_))
    }
}

impl Display for Symbol {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Symbol::Terminal(t) => write!(f, "{}", t),
            Symbol::NonTerminal(nt) => write!(f, "{}", nt),
        }
    }
}

pub type Alternative = Vec<Symbol>;

#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct Production {
    pub lhs: NonTerminal,
    pub alternatives: Vec<Alternative>,
}

impl Display for Production {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let alts_str: Vec<String> = self
            .alternatives
            .iter()
            .map(|alt| {
                if alt.is_empty() {
                    "ε".to_string()
                } else {
                    alt.iter()
                        .map(|sym| sym.to_string())
                        .collect::<Vec<_>>()
                        .join(" ")
                }
            })
            .collect();

        let rhs = if alts_str.is_empty() {
            "ε"
        } else {
            &alts_str.join(" | ")
        };

        write!(f, "{} -> {}", self.lhs, rhs)
    }
}

use std::fmt::Display;

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub enum Terminal {
    AChar,
    BChar,
    CChar,
    DChar,
    FChar,
    GChar,
    PChar,
    QChar,
    XChar,
    YChar,
    ZChar,

    ZeroChar,
    OneChar,
    TwoChar,
    ThreeChar,
    FourChar,
    FiveChar,
    SixChar,
    SevenChar,
    EightChar,
    NineChar,

    Epsilon,
    EOF,
}

impl Terminal {
    fn to_order(&self) -> u8 {
        match self {
            Terminal::AChar => 0,
            Terminal::BChar => 1,
            Terminal::CChar => 2,
            Terminal::DChar => 3,
            Terminal::FChar => 4,
            Terminal::GChar => 5,
            Terminal::PChar => 6,
            Terminal::QChar => 7,
            Terminal::XChar => 8,
            Terminal::YChar => 9,
            Terminal::ZChar => 10,

            Terminal::ZeroChar => 11,
            Terminal::OneChar => 12,
            Terminal::TwoChar => 13,
            Terminal::ThreeChar => 14,
            Terminal::FourChar => 15,
            Terminal::FiveChar => 16,
            Terminal::SixChar => 17,
            Terminal::SevenChar => 18,
            Terminal::EightChar => 19,
            Terminal::NineChar => 20,

            Terminal::Epsilon => 21,
            Terminal::EOF => 22,
        }
    }
}

impl Display for Terminal {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let s = match self {
            Terminal::AChar => "a",
            Terminal::BChar => "b",
            Terminal::CChar => "c",
            Terminal::DChar => "d",
            Terminal::PChar => "p",
            Terminal::QChar => "q",
            Terminal::Epsilon => "ε",
            Terminal::FChar => "f",
            Terminal::GChar => "g",
            Terminal::XChar => "x",
            Terminal::YChar => "y",
            Terminal::ZChar => "z",
            Terminal::EOF => "$",

            Terminal::ZeroChar => "0",
            Terminal::OneChar => "1",
            Terminal::TwoChar => "2",
            Terminal::ThreeChar => "3",
            Terminal::FourChar => "4",
            Terminal::FiveChar => "5",
            Terminal::SixChar => "6",
            Terminal::SevenChar => "7",
            Terminal::EightChar => "8",
            Terminal::NineChar => "9",
        };

        write!(f, "{}", s)
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

impl PartialOrd for Terminal {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for Terminal {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.to_order().cmp(&other.to_order())
    }
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub enum NonTerminal {
    A,
    B,
    C,
    D,
    F,
    G,
    P,
    Q,
    R,
    X,
    Y,
    S, // starter symbol
    T,
    Z, // starter symbol
}

impl NonTerminal {
    fn to_order(&self) -> u8 {
        match self {
            NonTerminal::A => 0,
            NonTerminal::B => 1,
            NonTerminal::C => 2,
            NonTerminal::D => 3,
            NonTerminal::F => 4,
            NonTerminal::G => 5,
            NonTerminal::P => 6,
            NonTerminal::Q => 7,
            NonTerminal::R => 8,
            NonTerminal::X => 9,
            NonTerminal::Y => 10,
            NonTerminal::S => 11,
            NonTerminal::T => 12,
            NonTerminal::Z => 13,
        }
    }
}

impl NonTerminal {
    pub fn from_str(s: &str) -> Result<Self, String> {
        match s.trim() {
            "A" => Ok(NonTerminal::A),
            "B" => Ok(NonTerminal::B),
            "C" => Ok(NonTerminal::C),
            "D" => Ok(NonTerminal::D),
            "F" => Ok(NonTerminal::F),
            "G" => Ok(NonTerminal::G),
            "P" => Ok(NonTerminal::P),
            "Q" => Ok(NonTerminal::Q),
            "R" => Ok(NonTerminal::R),
            "X" => Ok(NonTerminal::X),
            "Y" => Ok(NonTerminal::Y),
            "S" => Ok(NonTerminal::S),
            "T" => Ok(NonTerminal::T),
            "Z" => Ok(NonTerminal::Z),

            _ => Err(format!("NonTerminal not recognized: {}", s)),
        }
    }
}

impl Display for NonTerminal {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let s = match self {
            NonTerminal::A => "A",
            NonTerminal::B => "B",
            NonTerminal::C => "C",
            NonTerminal::D => "D",
            NonTerminal::F => "F",
            NonTerminal::G => "G",
            NonTerminal::P => "P",
            NonTerminal::Q => "Q",
            NonTerminal::R => "R",
            NonTerminal::X => "X",
            NonTerminal::Y => "Y",
            NonTerminal::S => "S",
            NonTerminal::T => "T",
            NonTerminal::Z => "Z",
        };

        write!(f, "{}", s)
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

impl PartialOrd for NonTerminal {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for NonTerminal {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.to_order().cmp(&other.to_order())
    }
}

#[derive(Debug, Eq, Hash, PartialEq, Copy, Clone)]
pub enum Symbol {
    Terminal(Terminal),
    NonTerminal(NonTerminal),
}

impl Symbol {
    pub fn from_str(s: &str) -> Result<Self, String> {
        match s.trim() {
            // terminals
            "a" => Ok(Symbol::Terminal(Terminal::AChar)),
            "b" => Ok(Symbol::Terminal(Terminal::BChar)),
            "c" => Ok(Symbol::Terminal(Terminal::CChar)),
            "d" => Ok(Symbol::Terminal(Terminal::DChar)),
            "f" => Ok(Symbol::Terminal(Terminal::FChar)),
            "g" => Ok(Symbol::Terminal(Terminal::GChar)),
            "p" => Ok(Symbol::Terminal(Terminal::PChar)),
            "q" => Ok(Symbol::Terminal(Terminal::QChar)),
            "x" => Ok(Symbol::Terminal(Terminal::XChar)),
            "y" => Ok(Symbol::Terminal(Terminal::YChar)),
            "z" => Ok(Symbol::Terminal(Terminal::ZChar)),

            "0" => Ok(Symbol::Terminal(Terminal::ZeroChar)),
            "1" => Ok(Symbol::Terminal(Terminal::OneChar)),
            "2" => Ok(Symbol::Terminal(Terminal::TwoChar)),
            "3" => Ok(Symbol::Terminal(Terminal::ThreeChar)),
            "4" => Ok(Symbol::Terminal(Terminal::FourChar)),
            "5" => Ok(Symbol::Terminal(Terminal::FiveChar)),
            "6" => Ok(Symbol::Terminal(Terminal::SixChar)),
            "7" => Ok(Symbol::Terminal(Terminal::SevenChar)),
            "8" => Ok(Symbol::Terminal(Terminal::EightChar)),
            "9" => Ok(Symbol::Terminal(Terminal::NineChar)),

            // special mapping for epsilon
            "e" | "ε" => Ok(Symbol::Terminal(Terminal::Epsilon)),

            // special mapping for EOF
            "$" | "EOF" => Ok(Symbol::Terminal(Terminal::EOF)),

            // non-terminals
            "A" => Ok(Symbol::NonTerminal(NonTerminal::A)),
            "B" => Ok(Symbol::NonTerminal(NonTerminal::B)),
            "C" => Ok(Symbol::NonTerminal(NonTerminal::C)),
            "D" => Ok(Symbol::NonTerminal(NonTerminal::D)),
            "F" => Ok(Symbol::NonTerminal(NonTerminal::F)),
            "G" => Ok(Symbol::NonTerminal(NonTerminal::G)),
            "P" => Ok(Symbol::NonTerminal(NonTerminal::P)),
            "Q" => Ok(Symbol::NonTerminal(NonTerminal::Q)),
            "X" => Ok(Symbol::NonTerminal(NonTerminal::X)),
            "Y" => Ok(Symbol::NonTerminal(NonTerminal::Y)),
            "R" => Ok(Symbol::NonTerminal(NonTerminal::R)),
            "S" => Ok(Symbol::NonTerminal(NonTerminal::S)),
            "T" => Ok(Symbol::NonTerminal(NonTerminal::T)),
            "Z" => Ok(Symbol::NonTerminal(NonTerminal::Z)),

            _ => Err(format!("Symbol not recognized: {}", s)),
        }
    }

    pub fn is_terminal(&self) -> bool {
        match self {
            Symbol::NonTerminal(_) => false,
            Symbol::Terminal(_) => true,
        }
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

#[derive(Debug)]
pub struct Production {
    pub lhs: NonTerminal,               // left-hand side
    pub alternatives: Vec<Alternative>, // represents the '|'
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

use crate::{
    model::{grammar::Grammar, types::Terminal},
    parser::ll1::LL1Parser,
};

mod analyzer;
mod model;
mod parser;

fn main() {
    let grammar = match Grammar::from_file("./grammar") {
        Ok(g) => g,
        Err(e) => panic!("{}", e),
    };

    println!("{}", grammar.to_vertical_table());

    println!("{}", analyzer::ll1::to_first_set_table(&grammar));

    println!("{}", analyzer::ll1::to_follow_set_table(&grammar));

    println!(
        "{}",
        analyzer::ll1::to_parsing_table(&grammar).expect("Expected table, nothing found.")
    );

    let ll1_parser = LL1Parser::new(&grammar).unwrap();

    let test_str = &[
        Terminal::AChar,
        Terminal::BChar,
        Terminal::BChar,
        Terminal::BChar,
    ];
    let (result, trace) = ll1_parser.parse(test_str);

    println!("String {:?} parseable: {}", test_str, result);
    println!("{}", LL1Parser::trace_as_table(&trace));
}


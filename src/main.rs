use crate::builder::types::TableGenerator;
use crate::model::grammar::Grammar;
use crate::parser::lr::LRParser;

mod builder;
mod model;
mod parser;

fn main() {
    let grammar = match Grammar::from_file("./grammar") {
        Ok(g) => g,
        Err(e) => panic!("{}", e),
    };

    println!("{}", grammar.to_vertical_table());

    println!("{}", builder::common::to_first_set_table(&grammar));

    println!("{}", builder::common::to_follow_set_table(&grammar));

    println!(
        "{}",
        builder::ll1::to_printable_table(&grammar).expect("Expected table, nothing found.")
    );

    let lr0_builder = builder::lr::lr0::LR0Builder::new(&grammar);

    println!(
        "{}",
        lr0_builder
            .to_printable_table()
            .expect("Expected table, nothing found.")
    );

    let mut lr_parser = LRParser::new(
        lr0_builder
            .build_parsing_table()
            .expect("Failed to build LR Parsing Table."),
    );

    let input = "abbabb"
        .chars()
        .map(|c| crate::model::types::Terminal::Char(c))
        .collect::<Vec<crate::model::types::Terminal>>();

    let (result, trace) = lr_parser.parse(&input);

    println!("{:?}", result);
    println!("{}", lr_parser.trace_as_table(&trace));
}

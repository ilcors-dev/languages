use crate::{
    builder::lr0::LRBuilder,
    model::{grammar::Grammar, types::Terminal},
    parser::ll1::LL1Parser,
};

mod builder;
mod model;
mod parser;

fn main() {
    let grammar = match Grammar::from_file("./grammar") {
        Ok(g) => g,
        Err(e) => panic!("{}", e),
    };

    println!("{}", grammar.to_vertical_table());

    println!("{}", builder::ll1::to_first_set_table(&grammar));

    println!("{}", builder::ll1::to_follow_set_table(&grammar));

    println!(
        "{}",
        builder::ll1::to_parsing_table(&grammar).expect("Expected table, nothing found.")
    );

    let mut lr0_builder = builder::lr0::LR0Builder::new(&grammar);
    lr0_builder.build();

    println!("{}", lr0_builder);
}

use std::io::{self, Write};

mod lexer;
mod parser;
mod interpreter;

use lexer::Lexer;
use parser::Parser;
use interpreter::{Interpreter, Store};

fn main() {
    println!("Type IMP programs for interpretation.");

    loop {
        print!("> ");
        io::stdout().flush().ok();
        let mut input = String::new();
        io::stdin().read_line(&mut input).ok();
        match process(input) {
            Ok(store) => println!("{:?}", store),
            Err(msg) => println!("{}", msg),
        }
    }
}

/// Interprets a string as an IMP program and returns the resulting store.
fn process(s: String) -> Result<Store, interpreter::Error> {
    let mut l = Lexer::new(s.chars());
    let mut p = Parser::new(l.lex().into_iter());
    let mut i = Interpreter::new();
    let ast = p.parse();
    i.eval(&ast).and_then(|_| Ok(i.store()))
}

#[test]
fn test_if() {
    let store = process(String::from("if false then skip else skip")).unwrap();
    assert!(store.is_empty());
}

#[test]
fn test_while() {
    let store = process(String::from("x := 0; y := 1; while x < 3 do { x := \
                                      x + 1; y := y * 2 }"))
        .unwrap();
    assert_eq!(Some(&3), store.get(&String::from("x")));
    assert_eq!(Some(&8), store.get(&String::from("y")));
}

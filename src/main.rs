use std::io::{self, Write};

mod lexer;
mod parser;
mod interpreter;

use lexer::Lexer;
use parser::Parser;
use interpreter::Interpreter;

fn main() {
    println!("Type IMP programs for interpretation.");

    loop {
        print!("> ");
        io::stdout().flush().ok();
        let mut input = String::new();
        io::stdin().read_line(&mut input).ok();
        let mut l = Lexer::new(input.trim().chars());
        let mut p = Parser::new(l.lex().into_iter());
        let mut i = Interpreter::new();
        i.eval(&p.parse());
        println!("{:?}", i.store());
    }
}
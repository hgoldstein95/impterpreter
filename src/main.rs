use std::io;

mod lexer;
mod parser;
mod interpreter;

use lexer::Lexer;
use parser::Parser;
use interpreter::Interpreter;

fn main() {
    println!("Type IMP programs for interpretation.");
    print!("> ");
    let mut input = String::new();
    try!(io::stdin().read_line(&mut input));

    let l = Lexer::new(input.trim().chars());
    let p = Parser::new(l.lex().into_iter());
    let i = Interpreter::new();
    println!("{:?}", i.eval(p.parse()));
}
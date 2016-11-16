mod lexer;
mod parser;
mod interpreter;

use lexer::Lexer;

fn main() {
    let s = String::from("hello := 40; world := 2");
    let mut lx = Lexer::new(s.chars());
    lx.lex();
    println!("Welcome to the 'impterpreter'!");
}
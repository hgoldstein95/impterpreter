//! The error module.

use std::fmt::{self, Display};
use lexer::Tok;

#[derive(Debug)]
pub enum Error {
    UnboundVariable(String),
    LexNumberError(String),
    WrongToken(Tok, Tok),
    BadAexp,
    BadBexp,
    BadCom,
    EndOfFile,
}

impl Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            Error::UnboundVariable(ref s) => {
                write!(f, "Interpreter: Unbound variable '{}'.", s)
            }
            Error::LexNumberError(ref s) => {
                write!(f, "Lexer: Failed to lex number '{}'.", s)
            }
            Error::WrongToken(ref t1, ref t2) => {
                write!(f,
                       "Parser: Consumed incorrect token. Expected '{:?}' \
                        found '{:?}'.",
                       t1,
                       t2)
            }
            Error::BadAexp => write!(f, "Parser: Problem while parsing aexp."),
            Error::BadBexp => write!(f, "Parser: Problem while parsing bexp."),
            Error::BadCom => write!(f, "Parser: Problem while parsing com."),
            Error::EndOfFile => {
                write!(f, "Parser: Reached end of stream while parsing.")
            }
        }
    }
}

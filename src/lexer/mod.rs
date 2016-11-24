//! The lexer module.

use std::fmt::{self, Display};
use std::iter::Peekable;

/// Error type for `Lexer`.
#[derive(Debug)]
pub enum Error {
    LexNumberError(String),
}

impl Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            Error::LexNumberError(ref s) => {
                write!(f, "Failed to lex number '{}'.", s)
            }
        }
    }
}

/// The `Tok` type. Represents a single token of the IMP language.
#[derive(Debug, PartialEq)]
pub enum Tok {
    /// An integer; this it the only numeric type recognized in IMP.
    Num(i32),
    /// A variable, represented by any non-reserved alphanumeric string.
    Var(String),
    True,
    False,
    Less,
    Plus,
    Times,
    Assgn,
    Semi,
    LParen,
    RParen,
    LBrace,
    RBrace,
    If,
    Then,
    Else,
    While,
    Do,
    Skip,
}

/// The `Lexer` type. Lexes a stream of chars into a vector of tokens.
pub struct Lexer<I: Iterator<Item = char>> {
    iter: Peekable<I>,
}

impl<I: Iterator<Item = char>> Lexer<I> {
    /// Constructs a new `Lexer`.
    pub fn new(i: I) -> Self {
        Lexer { iter: i.peekable() }
    }

    /// Generates a vector of tokens from the iterator stored in the lexer.
    pub fn lex(&mut self) -> Result<Vec<Tok>, Error> {
        let mut toks = Vec::new();
        while let Some(&c) = self.iter.peek() {
            let t = match c {
                '0'...'9' => {
                    match self.lex_num() {
                        Ok(tok) => Some(tok),
                        Err(msg) => return Err(msg),
                    }
                }
                'a'...'z' => Some(self.lex_alph()),
                _ => self.lex_sym(),
            };
            if let Some(tok) = t {
                toks.push(tok)
            }
        }
        Ok(toks)
    }

    /// Lexes a number from the iterator.
    fn lex_num(&mut self) -> Result<Tok, Error> {
        let mut s: String = String::new();
        while let Some(&c) = self.iter.peek() {
            if !c.is_digit(10) {
                break;
            }
            s.push(c);
            self.iter.next();
        }
        match s.parse::<i32>() {
            Err(msg) => Err(Error::LexNumberError(format!("{}", msg))),
            Ok(n) => Ok(Tok::Num(n)),
        }
    }

    /// Lexes an alphanumeric string from the iterator.
    ///
    /// May be a reserved word `if`, `while`, etc. or a variable.
    fn lex_alph(&mut self) -> Tok {
        let mut s: String = String::new();
        while let Some(&c) = self.iter.peek() {
            if !c.is_alphabetic() {
                break;
            }
            s.push(c);
            self.iter.next();
        }
        match s.as_str() {
            "skip" => Tok::Skip,
            "true" => Tok::True,
            "false" => Tok::False,
            "if" => Tok::If,
            "then" => Tok::Then,
            "else" => Tok::Else,
            "while" => Tok::While,
            "do" => Tok::Do,
            _ => Tok::Var(s),
        }
    }

    /// Lexes a symbol from the iterator, or discards unrecognized characters.
    fn lex_sym(&mut self) -> Option<Tok> {
        self.iter.next().and_then(|c| match c {
            '<' => Some(Tok::Less),
            '+' => Some(Tok::Plus),
            '*' => Some(Tok::Times),
            '(' => Some(Tok::LParen),
            ')' => Some(Tok::RParen),
            '{' => Some(Tok::LBrace),
            '}' => Some(Tok::RBrace),
            ';' => Some(Tok::Semi),
            ':' => {
                self.iter.next();
                Some(Tok::Assgn)
            }
            _ => None,
        })
    }
}

#[test]
fn test_simple() {
    let s = String::from("x := 42");
    let mut lx = Lexer::new(s.chars());
    let toks = lx.lex().unwrap();
    let mut iter = toks.iter();

    assert_eq!(&Tok::Var(String::from("x")), iter.next().unwrap());
    assert_eq!(&Tok::Assgn, iter.next().unwrap());
    assert_eq!(&Tok::Num(42), iter.next().unwrap());
    assert!(iter.next().is_none());
}

#[test]
fn test_complex() {
    let s = String::from("if(3<2)then{hello:=42;world:=42}");
    let mut lx = Lexer::new(s.chars());
    let toks = lx.lex().unwrap();
    let mut iter = toks.iter();

    assert_eq!(&Tok::If, iter.next().unwrap());
    assert_eq!(&Tok::LParen, iter.next().unwrap());
    assert_eq!(&Tok::Num(3), iter.next().unwrap());
    assert_eq!(&Tok::Less, iter.next().unwrap());
    assert_eq!(&Tok::Num(2), iter.next().unwrap());
    assert_eq!(&Tok::RParen, iter.next().unwrap());
    assert_eq!(&Tok::Then, iter.next().unwrap());
    assert_eq!(&Tok::LBrace, iter.next().unwrap());
    assert_eq!(&Tok::Var(String::from("hello")), iter.next().unwrap());
    assert_eq!(&Tok::Assgn, iter.next().unwrap());
    assert_eq!(&Tok::Num(42), iter.next().unwrap());
    assert_eq!(&Tok::Semi, iter.next().unwrap());
    assert_eq!(&Tok::Var(String::from("world")), iter.next().unwrap());
    assert_eq!(&Tok::Assgn, iter.next().unwrap());
    assert_eq!(&Tok::Num(42), iter.next().unwrap());
    assert_eq!(&Tok::RBrace, iter.next().unwrap());
    assert!(iter.next().is_none());
}

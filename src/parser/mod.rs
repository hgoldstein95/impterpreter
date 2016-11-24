//! The parser module.
//!
//! # EBNF Grammar
//!
//! aexp ::= term | term + term
//! term ::= fact | fact * fact
//! fact ::= n | var | ( aexp )
//!
//! bexp ::= true | false | aexp < aexp
//!
//! com  ::= exp | exp ; com
//! exp  ::= skip
//!        | var := aexp
//!        | if bexp then body else body
//!        | while bexp do body
//! body ::= exp | { com }

use std::iter::Peekable;
use lexer::Tok;

/// The `Aexp` type. Represents an arithmetic expression.
#[derive(Debug, PartialEq)]
pub enum Aexp {
    /// An integer.
    Num(i32),
    /// A variable.
    Var(String),
    /// The sum of two arithmetic expressions.
    Add(Box<Aexp>, Box<Aexp>),
    /// The product of two arithmetic expressions.
    Mul(Box<Aexp>, Box<Aexp>),
}

/// The `Bexp` type. Represents a binary expression.
#[derive(Debug, PartialEq)]
pub enum Bexp {
    /// True.
    True,
    /// False.
    False,
    /// Less than relation on arithmetic expressions.
    Less(Box<Aexp>, Box<Aexp>),
}

/// The `Com` type. Represents a command.
#[derive(Debug, PartialEq)]
pub enum Com {
    /// The skip command; does nothing.
    Skip,
    /// An ordering of one command after another.
    Seq(Box<Com>, Box<Com>),
    /// Assignment of an arithmetic expresssion to a variable.
    Assgn(String, Box<Aexp>),
    /// A branched statement.
    If(Box<Bexp>, Box<Com>, Box<Com>),
    /// A loop statement.
    While(Box<Bexp>, Box<Com>),
}

/// The `Parser` type. Parses a stream of tokens into an AST.
pub struct Parser<I: Iterator<Item = Tok>> {
    iter: Peekable<I>,
}

impl<I: Iterator<Item = Tok>> Parser<I> {
    /// Constructs a new `Parser`.
    pub fn new(i: I) -> Self {
        Parser { iter: i.peekable() }
    }

    /// Checks if `self.iter.peek()` returns one of the elements in `list`.
    fn peek_one_of(&mut self, list: Vec<Tok>) -> bool {
        if let Some(tok) = self.iter.peek() {
            return list.contains(tok);
        }
        false
    }

    /// Consumes the first token in `self.iter`.
    ///
    /// # Panics
    ///
    /// Will panic if the iterator does not start with the expected element.
    fn consume(&mut self, t: Tok) {
        assert_eq!(Some(t), self.iter.next())
    }

    /// Parses the nonterminal <i>aexp</i>.
    fn parse_aexp(&mut self) -> Aexp {
        let t = self.parse_term();
        if !self.peek_one_of(vec![Tok::Plus]) {
            return t;
        }
        match self.iter.next().unwrap() { // won't panic, op_next == true
            Tok::Plus => Aexp::Add(Box::new(t), Box::new(self.parse_term())),
            _ => t,
        }
    }

    /// Parses the nonterminal <i>term</i>.
    fn parse_term(&mut self) -> Aexp {
        let f = self.parse_fact();
        if !self.peek_one_of(vec![Tok::Times]) {
            return f;
        }
        match self.iter.next().unwrap() { // won't panic, op_next == true
            Tok::Times => Aexp::Mul(Box::new(f), Box::new(self.parse_term())),
            _ => f,
        }
    }

    /// Parses the nonterminal <i>fact</i>.
    ///
    /// # Panics
    ///
    /// Will panic if `self.iter` is empty, or if no factor can be parsed.
    fn parse_fact(&mut self) -> Aexp {
        // want to panic if there is nothing left
        match self.iter.next().unwrap() {
            Tok::Num(n) => Aexp::Num(n),
            Tok::Var(x) => Aexp::Var(x),
            Tok::LParen => {
                let e = self.parse_aexp();
                self.consume(Tok::RParen);
                e
            }
            _ => panic!("No factor to parse."),
        }
    }

    /// Parses the nonterminal <i>rel</i>.
    ///
    /// # Panics
    ///
    /// Will panic if `self.iter` is empty, or if no rel can be parsed.
    fn parse_bexp(&mut self) -> Bexp {
        if self.peek_one_of(vec![Tok::True, Tok::False]) {
            return match self.iter.next().unwrap() {
                Tok::True => Bexp::True,
                Tok::False => Bexp::False,
                _ => panic!("Impossible statement reached."),
            };
        }
        let a = self.parse_aexp();
        match self.iter.next().unwrap() {
            Tok::Less => Bexp::Less(Box::new(a), Box::new(self.parse_aexp())),
            _ => panic!("Improper bexp"),
        }
    }

    /// Parses the nonterminal <i>com</i>.
    pub fn parse(&mut self) -> Com {
        let e = self.parse_exp();
        if !self.peek_one_of(vec![Tok::Semi]) {
            return e;
        }
        match self.iter.next().unwrap() {// won't panic, op_next == true
            Tok::Semi => Com::Seq(Box::new(e), Box::new(self.parse())),
            _ => e,
        }
    }

    /// Parses the nonterminal <i>exp</i>.
    ///
    /// # Panics
    ///
    /// Will panic if `self.iter` is empty, or if no exp can be parsed.
    fn parse_exp(&mut self) -> Com {
        // want to panic if there is nothing left
        match self.iter.next().unwrap() {
            Tok::Skip => Com::Skip,
            Tok::Var(x) => {
                self.consume(Tok::Assgn);
                Com::Assgn(x, Box::new(self.parse_aexp()))
            }
            Tok::If => {
                let b = self.parse_bexp();
                self.consume(Tok::Then);
                let c1 = self.parse_body();
                self.consume(Tok::Else);
                let c2 = self.parse_body();
                Com::If(Box::new(b), Box::new(c1), Box::new(c2))
            }
            Tok::While => {
                let b = self.parse_bexp();
                self.consume(Tok::Do);
                let c = self.parse_body();
                Com::While(Box::new(b), Box::new(c))
            }
            _ => panic!("No exp to parse."),
        }
    }

    /// Parses the nonterminal <i>body</i>.
    fn parse_body(&mut self) -> Com {
        if self.peek_one_of(vec![Tok::LBrace]) {
            self.consume(Tok::LBrace);
            let c = self.parse();
            self.consume(Tok::RBrace);
            c
        } else {
            self.parse_exp()
        }
    }
}

#[test]
fn test_num() {
    use lexer::Tok;
    use self::Aexp::Num;

    let mut p = Parser::new(vec![Tok::Num(2)].into_iter());
    let aexp = p.parse_aexp();
    assert_eq!(Num(2), aexp);
}

#[test]
fn test_add() {
    use lexer::Tok;
    use self::Aexp::{Add, Num};

    let mut p = Parser::new(vec![Tok::Num(2), Tok::Plus, Tok::Num(3)]
        .into_iter());
    let aexp = p.parse_aexp();
    assert_eq!(Add(Box::new(Num(2)), Box::new(Num(3))), aexp);
}

#[test]
fn test_parens() {
    use lexer::Tok;
    use self::Aexp::{Add, Num};

    let mut p = Parser::new(vec![Tok::Num(2),
             Tok::Plus,
             Tok::LParen,
             Tok::Num(3),
             Tok::RParen,
             ]
        .into_iter());
    let aexp = p.parse_aexp();
    assert_eq!(Add(Box::new(Num(2)), Box::new(Num(3))), aexp);
}

#[test]
fn test_complex_aexp_1() {
    use lexer::Tok;
    use self::Aexp::{Add, Num, Mul, Var};

    let mut p = Parser::new(vec![Tok::Num(2),
                                 Tok::Plus,
                                 Tok::Num(3),
                                 Tok::Times,
                                 Tok::Var(String::from("x"))]
        .into_iter());
    let aexp = p.parse_aexp();
    assert_eq!(Add(Box::new(Num(2)),
                   Box::new(Mul(Box::new(Num(3)),
                                Box::new(Var(String::from("x")))))),
               aexp);
}

#[test]
fn test_complex_aexp_2() {
    use lexer::Tok;
    use self::Aexp::{Add, Num, Mul, Var};

    let mut p = Parser::new(vec![Tok::Num(2),
                                 Tok::Times,
                                 Tok::Num(3),
                                 Tok::Plus,
                                 Tok::Var(String::from("x"))]
        .into_iter());
    let aexp = p.parse_aexp();
    assert_eq!(Add(Box::new(Mul(Box::new(Num(2)), Box::new(Num(3)))),
                   Box::new(Var(String::from("x")))),
               aexp);
}

#[test]
fn test_true() {
    use lexer::Tok;
    use self::Bexp::True;

    let mut p = Parser::new(vec![Tok::True].into_iter());
    let bexp = p.parse_bexp();
    assert_eq!(True, bexp);
}

#[test]
fn test_less() {
    use lexer::Tok;
    use self::Aexp::Num;
    use self::Bexp::Less;

    let mut p = Parser::new(vec![Tok::Num(2), Tok::Less, Tok::Num(3)]
        .into_iter());
    let bexp = p.parse_bexp();
    assert_eq!(Less(Box::new(Num(2)), Box::new(Num(3))), bexp);
}

#[test]
fn test_skip() {
    use lexer::Tok;
    use self::Com::Skip;

    let mut p = Parser::new(vec![Tok::Skip].into_iter());
    let prog = p.parse();
    assert_eq!(Skip, prog);
}

#[test]
fn test_seq() {
    use lexer::Tok;
    use self::Com::{Seq, Skip};

    let mut p = Parser::new(vec![Tok::Skip, Tok::Semi, Tok::Skip].into_iter());
    let prog = p.parse();
    assert_eq!(Seq(Box::new(Skip), Box::new(Skip)), prog);
}

#[test]
fn test_assgn() {
    use lexer::Tok;
    use self::Aexp::Num;
    use self::Com::Assgn;

    let mut p = Parser::new(vec![Tok::Var(String::from("x")),
                                 Tok::Assgn,
                                 Tok::Num(42)]
        .into_iter());
    let prog = p.parse();
    assert_eq!(Assgn(String::from("x"), Box::new(Num(42))), prog);
}

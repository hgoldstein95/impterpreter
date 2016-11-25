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
use error::Error;

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
    /// Returns true if the token is the expected token, false otherwise.
    fn consume(&mut self, t: Tok) -> Result<(), Error> {
        if let Some(other) = self.iter.next() {
            if t == other {
                Ok(())
            } else {
                Err(Error::WrongToken(t, other))
            }
        } else {
            Err(Error::EndOfFile)
        }
    }

    /// Parses the nonterminal <i>aexp</i>.
    fn parse_aexp(&mut self) -> Result<Aexp, Error> {
        self.parse_term().and_then(|t| {
            if self.peek_one_of(vec![Tok::Plus]) {
                match self.iter.next() {
                    Some(Tok::Plus) => {
                        self.parse_term().and_then(|t2| {
                            Ok(Aexp::Add(Box::new(t), Box::new(t2)))
                        })
                    }
                    _ => Ok(t),
                }
            } else {
                Ok(t)
            }
        })
    }

    /// Parses the nonterminal <i>term</i>.
    fn parse_term(&mut self) -> Result<Aexp, Error> {
        self.parse_fact().and_then(|f| {
            if self.peek_one_of(vec![Tok::Times]) {
                match self.iter.next() {
                    Some(Tok::Times) => {
                        self.parse_fact().and_then(|f2| {
                            Ok(Aexp::Mul(Box::new(f), Box::new(f2)))
                        })
                    }
                    _ => Ok(f),
                }
            } else {
                Ok(f)
            }
        })
    }

    /// Parses the nonterminal <i>fact</i>.
    fn parse_fact(&mut self) -> Result<Aexp, Error> {
        match self.iter.next() {
            Some(Tok::Num(n)) => Ok(Aexp::Num(n)),
            Some(Tok::Var(x)) => Ok(Aexp::Var(x)),
            Some(Tok::LParen) => {
                self.parse_aexp()
                    .and_then(|e| self.consume(Tok::RParen).and(Ok(e)))
            }
            None => Err(Error::EndOfFile),
            _ => Err(Error::BadAexp),
        }
    }

    /// Parses the nonterminal <i>rel</i>.
    fn parse_bexp(&mut self) -> Result<Bexp, Error> {
        if self.peek_one_of(vec![Tok::True, Tok::False]) {
            match self.iter.next() {
                Some(Tok::True) => Ok(Bexp::True),
                Some(Tok::False) => Ok(Bexp::False),
                _ => panic!("Impossible state reached."),
            }
        } else {
            self.parse_aexp().and_then(|a| {
                match self.iter.next() {
                    Some(Tok::Less) => {
                        self.parse_aexp().and_then(|a2| {
                            Ok(Bexp::Less(Box::new(a), Box::new(a2)))
                        })
                    }
                    None => Err(Error::EndOfFile),
                    _ => Err(Error::BadBexp),
                }
            })
        }
    }

    /// Parses the nonterminal <i>com</i>.
    pub fn parse(&mut self) -> Result<Com, Error> {
        self.parse_exp().and_then(|e| {
            if self.peek_one_of(vec![Tok::Semi]) {
                match self.iter.next() {
                    Some(Tok::Semi) => {
                        self.parse().and_then(|e2| {
                            Ok(Com::Seq(Box::new(e), Box::new(e2)))
                        })
                    }
                    _ => Ok(e),
                }
            } else {
                Ok(e)
            }
        })
    }

    /// Parses the nonterminal <i>exp</i>.
    fn parse_exp(&mut self) -> Result<Com, Error> {
        match self.iter.next() {
            Some(Tok::Skip) => Ok(Com::Skip),
            Some(Tok::Var(x)) => {
                self.consume(Tok::Assgn).and(self.parse_aexp()
                    .and_then(|a| Ok(Com::Assgn(x, Box::new(a)))))
            }
            Some(Tok::If) => {
                self.parse_bexp().and_then(|b| {
                    self.consume(Tok::Then)
                        .and(self.parse_body().and_then(|c1| {
                            self.consume(Tok::Else)
                                .and(self.parse_body().and_then(|c2| {
                                    Ok(Com::If(Box::new(b),
                                               Box::new(c1),
                                               Box::new(c2)))
                                }))
                        }))
                })
            }
            Some(Tok::While) => {
                self.parse_bexp().and_then(|b| {
                    self.consume(Tok::Do).and(self.parse_body()
                        .and_then(|c| Ok(Com::While(Box::new(b), Box::new(c)))))
                })
            }
            None => Err(Error::EndOfFile),
            _ => Err(Error::BadCom),
        }
    }

    /// Parses the nonterminal <i>body</i>.
    fn parse_body(&mut self) -> Result<Com, Error> {
        if self.peek_one_of(vec![Tok::LBrace]) {
            self.consume(Tok::LBrace).and(self.parse()
                .and_then(|c| self.consume(Tok::RBrace).and(Ok(c))))
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
    let aexp = p.parse_aexp().unwrap();
    assert_eq!(Num(2), aexp);
}

#[test]
fn test_add() {
    use lexer::Tok;
    use self::Aexp::{Add, Num};

    let mut p = Parser::new(vec![Tok::Num(2), Tok::Plus, Tok::Num(3)]
        .into_iter());
    let aexp = p.parse_aexp().unwrap();
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
    let aexp = p.parse_aexp().unwrap();
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
    let aexp = p.parse_aexp().unwrap();
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
    let aexp = p.parse_aexp().unwrap();
    assert_eq!(Add(Box::new(Mul(Box::new(Num(2)), Box::new(Num(3)))),
                   Box::new(Var(String::from("x")))),
               aexp);
}

#[test]
fn test_true() {
    use lexer::Tok;
    use self::Bexp::True;

    let mut p = Parser::new(vec![Tok::True].into_iter());
    let bexp = p.parse_bexp().unwrap();
    assert_eq!(True, bexp);
}

#[test]
fn test_less() {
    use lexer::Tok;
    use self::Aexp::Num;
    use self::Bexp::Less;

    let mut p = Parser::new(vec![Tok::Num(2), Tok::Less, Tok::Num(3)]
        .into_iter());
    let bexp = p.parse_bexp().unwrap();
    assert_eq!(Less(Box::new(Num(2)), Box::new(Num(3))), bexp);
}

#[test]
fn test_skip() {
    use lexer::Tok;
    use self::Com::Skip;

    let mut p = Parser::new(vec![Tok::Skip].into_iter());
    let prog = p.parse().unwrap();
    assert_eq!(Skip, prog);
}

#[test]
fn test_seq() {
    use lexer::Tok;
    use self::Com::{Seq, Skip};

    let mut p = Parser::new(vec![Tok::Skip, Tok::Semi, Tok::Skip].into_iter());
    let prog = p.parse().unwrap();
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
    let prog = p.parse().unwrap();
    assert_eq!(Assgn(String::from("x"), Box::new(Num(42))), prog);
}

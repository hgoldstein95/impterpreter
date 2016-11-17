use std::iter::Peekable;
use lexer::Tok;

#[derive(Debug, PartialEq)]
pub enum Aexp {
    Num(i32),
    Var(String),
    Add(Box<Aexp>, Box<Aexp>),
    Sub(Box<Aexp>, Box<Aexp>),
    Mul(Box<Aexp>, Box<Aexp>),
}

#[derive(Debug, PartialEq)]
pub enum Bexp {
    True,
    False,
    Eqs(Box<Aexp>, Box<Aexp>),
    Less(Box<Aexp>, Box<Aexp>),
    And(Box<Bexp>, Box<Bexp>),
    Or(Box<Bexp>, Box<Bexp>),
}

#[derive(Debug, PartialEq)]
pub enum Com {
    Skip,
    Seq(Box<Com>, Box<Com>),
    Assgn(String, Box<Aexp>),
    If(Box<Bexp>, Box<Com>, Box<Com>),
    While(Box<Bexp>, Box<Com>),
}
/*
EBNF Grammar

aexp ::= term | term + term | term - term
term ::= fact | fact * fact
fact ::= n | x | ( aexp )

bexp ::= cond | cond and cond
cond ::= rel | rel or rel
rel  ::= true | false | aexp = aexp | aexp < aexp

com  ::= exp | exp ; exp
exp  ::= skip
       | x := aexp
       | if bexp then com else com
       | while bexp do com
       | { com }
*/

pub struct Parser<I: Iterator<Item=Tok>> {
    iter: Peekable<I>,
}

impl <I: Iterator<Item=Tok>> Parser<I> {
    pub fn new(i: I) -> Self {
        Parser { iter: i.peekable() }
    }

    fn peek_one_of(&mut self, list: Vec<Tok>) -> bool {
        if let Some(tok) = self.iter.peek() {
            list.contains(tok)
        } else {
            false
        }
    }

    fn parse_aexp(&mut self) -> Aexp {
        let t = self.parse_term();
        if !self.peek_one_of(vec![Tok::Plus, Tok::Minus]) {
            return t; // Early return
        }
        let tok = self.iter.next().unwrap(); // won't panic, op_next == true
        match tok {
            Tok::Plus => 
                Aexp::Add(Box::new(t), Box::new(self.parse_term())),
            Tok::Minus =>
                Aexp::Sub(Box::new(t), Box::new(self.parse_term())),
            _ => t,
        }
    }

    fn parse_term(&mut self) -> Aexp {
        let f = self.parse_factor();
        if !self.peek_one_of(vec![Tok::Times]) {
            return f; // Early return
        }
        let tok = self.iter.next().unwrap(); // won't panic, op_next == true
        match tok {
            Tok::Times => 
                Aexp::Mul(Box::new(f), Box::new(self.parse_term())),
            _ => f,
        }
    }

    fn parse_factor(&mut self) -> Aexp {
        // want to panic if there is nothing left
        match self.iter.next().unwrap() {
            Tok::Num(n) => Aexp::Num(n),
            Tok::Var(x) => Aexp::Var(x),
            Tok::LParen => {
                let e = self.parse_aexp();
                self.iter.next();
                e
            },
            _ => panic!("No factor to parse."),
        }
    }

    fn parse_bexp(&mut self) -> Bexp {
        let c = self.parse_cond();
        if !self.peek_one_of(vec![Tok::And]) {
            return c; // Early return
        }
        let tok = self.iter.next().unwrap(); // won't panic, op_next == true
        match tok {
            Tok::And => 
                Bexp::And(Box::new(c), Box::new(self.parse_cond())),
            _ => c,
        }
    }

    fn parse_cond(&mut self) -> Bexp {
        let r = self.parse_rel();
        if !self.peek_one_of(vec![Tok::Or]) {
            return r; // Early return
        }
        let tok = self.iter.next().unwrap(); // won't panic, op_next == true
        match tok {
            Tok::Or => 
                Bexp::Or(Box::new(r), Box::new(self.parse_rel())),
            _ => r,
        }
    }

    fn parse_rel(&mut self) -> Bexp {
        if self.peek_one_of(vec![Tok::True, Tok::False]) {
            return match self.iter.next().unwrap() {
                Tok::True => Bexp::True,
                Tok::False => Bexp::False,
                _ => panic!("Impossible statement reached.")
            };
        }
        let a = self.parse_aexp();
        match self.iter.next().unwrap() {
            Tok::Eqs => Bexp::Eqs(Box::new(a), Box::new(self.parse_aexp())),
            Tok::Less => Bexp::Less(Box::new(a), Box::new(self.parse_aexp())),
            _ => panic!("Improper relation"),
        }
    }

    pub fn parse(&mut self) -> Com {
        let e = self.parse_exp();
        if !self.peek_one_of(vec![Tok::Semi]) {
            return e; // Early return
        }
        let tok = self.iter.next().unwrap(); // won't panic, op_next == true
        match tok {
            Tok::Semi => 
                Com::Seq(Box::new(e), Box::new(self.parse_exp())),
            _ => e,
        }
    }

    fn parse_exp(&mut self) -> Com {
        // want to panic if there is nothing left
        match self.iter.next().unwrap() {
            Tok::Skip => Com::Skip,
            Tok::Var(x) => {
                self.iter.next(); // consume :=
                Com::Assgn(x, Box::new(self.parse_aexp()))
            },
            Tok::If => {
                let b = self.parse_bexp();
                self.iter.next(); // consume then
                let c1 = self.parse();
                self.iter.next(); // consume else
                let c2 = self.parse();
                Com::If(Box::new(b), Box::new(c1), Box::new(c2))
            },
            Tok::While => {
                let b = self.parse_bexp();
                self.iter.next(); // consume do
                let c = self.parse();
                Com::While(Box::new(b), Box::new(c))
            },
            Tok::LBrace => {
                let com = self.parse();
                self.iter.next();
                com
            },
            _ => panic!("No ex to parse."),
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

    let mut p = Parser::new(
        vec![Tok::Num(2),
             Tok::Plus,
             Tok::Num(3)
             ].into_iter());
    let aexp = p.parse_aexp();
    assert_eq!(Add(Box::new(Num(2)), Box::new(Num(3))), aexp);
}

#[test]
fn test_parens() {
    use lexer::Tok;
    use self::Aexp::{Add, Num};

    let mut p = Parser::new(
        vec![Tok::Num(2),
             Tok::Plus,
             Tok::LParen,
             Tok::Num(3),
             Tok::RParen,
             ].into_iter());
    let aexp = p.parse_aexp();
    assert_eq!(Add(Box::new(Num(2)), Box::new(Num(3))), aexp);
}

#[test]
fn test_complex_aexp_1() {
    use lexer::Tok;
    use self::Aexp::{Add, Num, Mul, Var};

    let mut p = Parser::new(
        vec![Tok::Num(2),
             Tok::Plus,
             Tok::Num(3),
             Tok::Times,
             Tok::Var(String::from("x"))
             ].into_iter());
    let aexp = p.parse_aexp();
    assert_eq!(
        Add(
            Box::new(Num(2)),
            Box::new(Mul(
                Box::new(Num(3)),
                Box::new(Var(String::from("x")))))), aexp);
}

#[test]
fn test_complex_aexp_2() {
    use lexer::Tok;
    use self::Aexp::{Add, Num, Mul, Var};

    let mut p = Parser::new(
        vec![Tok::Num(2),
             Tok::Times,
             Tok::Num(3),
             Tok::Plus,
             Tok::Var(String::from("x"))
             ].into_iter());
    let aexp = p.parse_aexp();
    assert_eq!(
        Add(
            Box::new(Mul(Box::new(Num(2)), Box::new(Num(3)))),
            Box::new(Var(String::from("x")))), aexp);
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
fn test_and() {
    use lexer::Tok;
    use self::Bexp::{And, True, False};

    let mut p = Parser::new(vec![Tok::True, Tok::And, Tok::False].into_iter());
    let bexp = p.parse_bexp();
    assert_eq!(And(Box::new(True), Box::new(False)), bexp);
}

#[test]
fn test_eqs() {
    use lexer::Tok;
    use self::Aexp::Num;
    use self::Bexp::Eqs;

    let mut p = Parser::new(
        vec![Tok::Num(2),
             Tok::Eqs,
             Tok::Num(3)
             ].into_iter());
    let bexp = p.parse_bexp();
    assert_eq!(Eqs(Box::new(Num(2)), Box::new(Num(3))), bexp);
}

#[test]
fn test_complex_bexp() {
    use lexer::Tok;
    use self::Aexp::Num;
    use self::Bexp::{And, Eqs, False};

    let mut p = Parser::new(
        vec![Tok::Num(2),
             Tok::Eqs,
             Tok::Num(3),
             Tok::And,
             Tok::False
             ].into_iter());
    let bexp = p.parse_bexp();
    assert_eq!(
        And(
            Box::new(Eqs(Box::new(Num(2)), Box::new(Num(3)))),
            Box::new(False)), bexp);
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

    let mut p = Parser::new(
        vec![Tok::Var(String::from("x")),
             Tok::Assgn,
             Tok::Num(42)
             ].into_iter());
    let prog = p.parse();
    assert_eq!(Assgn(String::from("x"), Box::new(Num(42))), prog);
}
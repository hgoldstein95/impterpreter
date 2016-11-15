use std::iter::Peekable;

#[derive(Debug, PartialEq)]
pub enum Tok {
    Num(i32),
    Var(String),
    And, Or, True, False, Eqs, Less, 
    Plus, Minus, Assgn, Semi,
    LParen, RParen, LBrace, RBrace,
    If, Then, Else, While, Do, Skip,
}

pub struct Lexer<I: Iterator<Item=char>> {
    iter: Peekable<I>,
}

impl <I: Iterator<Item=char>> Lexer<I> {

    pub fn new(i: I) -> Self {
        Lexer { iter: i.peekable() }
    }

    pub fn lex(&mut self) -> Vec<Tok> {
        let mut toks = Vec::new();
        while let Some(&c) = self.iter.peek() {
            let t = match c {
                '0'...'9' => Some(self.lex_num()),
                'a'...'z' => Some(self.lex_alph()),
                _ => self.lex_sym(),
            };
            if let Some(tok) = t {
                toks.push(tok)
            }
        }
        toks
    }

    fn lex_num(&mut self) -> Tok {
        let mut s: String = String::new();
        while let Some(&c) = self.iter.peek() {
            if !c.is_digit(10) { break }
            s.push(c);
            self.iter.next();
        }
        match s.parse::<i32>() {
            Err(_) => panic!("Cannot parse int."),
            Ok(n) => Tok::Num(n),
        }
    }

    fn lex_alph(&mut self) -> Tok {
        let mut s: String = String::new();
        while let Some(&c) = self.iter.peek() {
            if !c.is_alphabetic() { break }
            s.push(c);
            self.iter.next();
        }
        match s.as_str() {
            "skip" => Tok::Skip,
            "true" => Tok::True,
            "false" => Tok::False,
            "and" => Tok::And,
            "or" => Tok::Or,
            "if" => Tok::If,
            "then" => Tok::Then,
            "else" => Tok::Else,
            "while" => Tok::While,
            "do" => Tok::Do,
            _ => Tok::Var(s),
        }
    }

    fn lex_sym(&mut self) -> Option<Tok> {
        self.iter.next().and_then(|c|
            match c {
                '=' => Some(Tok::Eqs),
                '<' => Some(Tok::Less),
                '+' => Some(Tok::Plus),
                '-' => Some(Tok::Minus),
                ':' => { self.iter.next(); Some(Tok::Assgn) },
                '(' => Some(Tok::LParen),
                ')' => Some(Tok::RParen),
                '{' => Some(Tok::LBrace),
                '}' => Some(Tok::RBrace),
                ';' => Some(Tok::Semi),
                _ => None,
            }
        )
    }
}

#[test]
fn test_simple() {
    use lexer::Tok;

    let s = String::from("x := 42");
    let mut lx = Lexer::new(s.chars());
    let toks = lx.lex();
    let mut iter = toks.iter();

    assert_eq!(&Tok::Var(String::from("x")), iter.next().unwrap());
    assert_eq!(&Tok::Assgn, iter.next().unwrap());
    assert_eq!(&Tok::Num(42), iter.next().unwrap());
    assert!(iter.next().is_none());
}

#[test]
fn test_complex() {
    use lexer::Tok;

    let s = String::from("if(3=2)then{hello:=42;world:=42}");
    let mut lx = Lexer::new(s.chars());
    let toks = lx.lex();
    let mut iter = toks.iter();

    assert_eq!(&Tok::If, iter.next().unwrap());
    assert_eq!(&Tok::LParen, iter.next().unwrap());
    assert_eq!(&Tok::Num(3), iter.next().unwrap());
    assert_eq!(&Tok::Eqs, iter.next().unwrap());
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
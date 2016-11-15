use lexer::Tok;

pub enum Aexp {
    Num(i32),
    Var(String),
    Add(Box<Aexp>, Box<Aexp>),
    Sub(Box<Aexp>, Box<Aexp>),
}

pub enum Bexp {
    True,
    False,
    Eqs(Box<Aexp>, Box<Aexp>),
    Less(Box<Aexp>, Box<Aexp>),
    And(Box<Bexp>, Box<Bexp>),
    Or(Box<Bexp>, Box<Bexp>),
}

pub enum Com {
    Skip,
    Seq(Box<Com>, Box<Com>),
    Assgn(String, Box<Aexp>),
    If(Box<Bexp>, Box<Com>, Box<Com>),
    While(Box<Bexp>, Box<Com>),
}

pub struct Parser<I: Iterator<Item=Tok>> {
    iter: I,
}

impl <I: Iterator<Item=Tok>> Parser<I> {
    pub fn new(i: I) -> Self {
        Parser { iter: i }
    }

    fn parse_aexp(&mut self) -> Aexp {
        Aexp::Num(0)
    }

    fn parse_bexp(&mut self) -> Bexp {
        Bexp::True
    }

    fn parse(&mut self) -> Com {
        Com::Skip
    }
}

#[test]
fn test_parse() {
    use lexer::Tok;

    Parser::new(vec![Tok::Skip].into_iter());
}
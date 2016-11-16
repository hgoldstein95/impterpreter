use std::collections::HashMap;
use parser::{Aexp, Bexp, Com};

pub struct Interpreter<'a> {
    store: HashMap<&'a str, i32>,
}

impl <'a> Interpreter<'a> {

    pub fn new() -> Self {
        Interpreter { store: HashMap::new() }
    }

    fn eval_aexp(&mut self, a: Aexp) -> i32 {
        use parser::Aexp::*;

        match a {
            Num(n) => n,
            Var(s) => *self.store.get(s.as_str()).unwrap(), // TODO: handle err
            Add(a1, a2) => self.eval_aexp(*a1) + self.eval_aexp(*a2),
            Sub(a1, a2) => self.eval_aexp(*a1) - self.eval_aexp(*a2),
            Mul(a1, a2) => self.eval_aexp(*a1) * self.eval_aexp(*a2),
        }
    }

    fn eval_bexp(&mut self, b: Bexp) -> bool {
        use parser::Bexp::*;

        match b {
            True => true,
            False => false,
            Eqs(a1, a2) => self.eval_aexp(*a1) == self.eval_aexp(*a2),
            Less(a1, a2) => self.eval_aexp(*a1) < self.eval_aexp(*a2),
            And(b1, b2) => self.eval_bexp(*b1) && self.eval_bexp(*b2),
            Or(b1, b2) => self.eval_bexp(*b1) || self.eval_bexp(*b2),
        }
    }

    pub fn eval(&mut self, c: Com) -> HashMap<&'a str, i32> {
        match c {
            _ => (),
        };
        self.store.clone()
    }
}

#[test]
fn test_num() {
    use parser::Aexp::Num;

    let mut interp = Interpreter::new();
    let a = Num(42);
    assert_eq!(42, interp.eval_aexp(a));
}

#[test]
fn test_true() {
    use parser::Bexp::True;

    let mut interp = Interpreter::new();
    let b = True;
    assert!(interp.eval_bexp(b));
}

#[test]
fn test_skip() {
    use parser::Com::Skip;

    let mut interp = Interpreter::new();
    interp.eval(Skip);
}
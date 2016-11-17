use std::collections::HashMap;
use parser::{Aexp, Bexp, Com};

pub struct Interpreter {
    store: HashMap<String, i32>,
}

impl Interpreter {

    pub fn new() -> Self {
        Interpreter { store: HashMap::new() }
    }

    fn eval_aexp(&mut self, a: &Aexp) -> i32 {
        use parser::Aexp::*;

        match a {
            &Num(n) => n,
            &Var(ref s) => *self.store.get(s).unwrap(), // TODO: handle err
            &Add(ref a1, ref a2) => self.eval_aexp(a1) + self.eval_aexp(a2),
            &Sub(ref a1, ref a2) => self.eval_aexp(a1) - self.eval_aexp(a2),
            &Mul(ref a1, ref a2) => self.eval_aexp(a1) * self.eval_aexp(a2),
        }
    }

    fn eval_bexp(&mut self, b: &Bexp) -> bool {
        use parser::Bexp::*;

        match b {
            &True => true,
            &False => false,
            &Eqs(ref a1, ref a2) => self.eval_aexp(a1) == self.eval_aexp(a2),
            &Less(ref a1, ref a2) => self.eval_aexp(a1) < self.eval_aexp(a2),
            &And(ref b1, ref b2) => self.eval_bexp(b1) && self.eval_bexp(b2),
            &Or(ref b1, ref b2) => self.eval_bexp(b1) || self.eval_bexp(b2),
        }
    }

    pub fn eval(&mut self, c: &Com) {
        use parser::Com::*;

        match c {
            &Skip => (),
            &Seq(ref c1, ref c2) => { self.eval(c1); self.eval(c2) },
            &Assgn(ref s, ref a) => {
                let n = self.eval_aexp(a);
                self.store.insert(s.clone(), n);
            },
            &If(ref b, ref c1, ref c2) => {
                if self.eval_bexp(b) {
                    self.eval(c1)
                } else {
                    self.eval(c2)
                }
            },
            &While(ref b, ref c1) => {
                if self.eval_bexp(b) {
                    self.eval(c1);
                    self.eval(c)
                }
            },
        }
    }

    pub fn store(&self) -> HashMap<String, i32> {
        self.store.clone()
    }
}

#[test]
fn test_num() {
    use parser::Aexp::Num;

    let mut interp = Interpreter::new();
    let a = Num(42);
    assert_eq!(42, interp.eval_aexp(&a));
}

#[test]
fn test_true() {
    use parser::Bexp::True;

    let mut interp = Interpreter::new();
    let b = True;
    assert!(interp.eval_bexp(&b));
}

#[test]
fn test_single_assgn() {
    use parser::Com::Assgn;
    use parser::Aexp::Num;

    let prog = Assgn(String::from("x"), Box::new(Num(42)));

    let mut interp = Interpreter::new();
    interp.eval(&prog);
    let s = interp.store();
    assert_eq!(Some(&42), s.get(&String::from("x")));
}

#[test]
fn test_double_assgn() {
    use parser::Com::{Seq, Assgn};
    use parser::Aexp::Num;

    let prog = Seq(Box::new(Assgn(String::from("x"), Box::new(Num(42)))),
                   Box::new(Assgn(String::from("y"), Box::new(Num(420)))));

    let mut interp = Interpreter::new();
    interp.eval(&prog);
    let s = interp.store();
    assert_eq!(Some(&42), s.get(&String::from("x")));
    assert_eq!(Some(&420), s.get(&String::from("y")));
}
//! The interpreter module.

use std::collections::HashMap;
use parser::{Aexp, Bexp, Com};

pub type Store = HashMap<String, i32>;

/// The `Interpreter` type. Interprets an AST to a map of values.
pub struct Interpreter {
    store: Store,
}

impl Interpreter {
    /// Constructs a new `Interpreter`.
    pub fn new() -> Self {
        Interpreter { store: HashMap::new() }
    }

    /// Evaluates an arithmetic expression.
    fn eval_aexp(&mut self, a: &Aexp) -> Result<i32, String> {
        use parser::Aexp::*;

        match a {
            &Num(n) => Ok(n),
            &Var(ref s) => {
                if let Some(&n) = self.store.get(s) {
                    Ok(n)
                } else {
                    Err(format!("Unbound variable '{}'.", s))
                }
            }
            &Add(ref a1, ref a2) => {
                self.eval_aexp(a1).and_then(|n1| {
                    self.eval_aexp(a2).and_then(|n2| Ok(n1 + n2))
                })
            }
            &Mul(ref a1, ref a2) => {
                self.eval_aexp(a1).and_then(|n1| {
                    self.eval_aexp(a2).and_then(|n2| Ok(n1 * n2))
                })
            }
        }
    }

    /// Evaluates a binary expression.
    fn eval_bexp(&mut self, b: &Bexp) -> Result<bool, String> {
        use parser::Bexp::*;

        match b {
            &True => Ok(true),
            &False => Ok(false),
            &Less(ref a1, ref a2) => {
                self.eval_aexp(a1).and_then(|n1| {
                    self.eval_aexp(a2).and_then(|n2| Ok(n1 < n2))
                })
            }
        }
    }

    /// Evaluates a command.
    pub fn eval(&mut self, c: &Com) -> Result<(), String> {
        use parser::Com::*;

        match c {
            &Skip => Ok(()),
            &Seq(ref c1, ref c2) => {
                self.eval(c1).and_then(|_| self.eval(c2).and(Ok(())))
            }
            &Assgn(ref s, ref a) => {
                self.eval_aexp(a).and_then(|n| {
                    self.store.insert(s.clone(), n);
                    Ok(())
                })
            }
            &If(ref b, ref c1, ref c2) => {
                self.eval_bexp(b).and_then(|v| {
                    if v {
                        self.eval(c1).and(Ok(()))
                    } else {
                        self.eval(c2).and(Ok(()))
                    }
                })
            }
            &While(ref b, ref c_body) => {
                self.eval_bexp(b).and_then(|v| {
                    if v {
                        self.eval(c_body).and_then(|_| self.eval(c).and(Ok(())))
                    } else {
                        Ok(())
                    }
                })
            }
        }
    }

    /// Returns a copy of the store.
    pub fn store(&self) -> Store {
        self.store.clone()
    }
}

#[test]
fn test_num() {
    use parser::Aexp::Num;

    let mut interp = Interpreter::new();
    let a = Num(42);
    assert_eq!(42, interp.eval_aexp(&a).unwrap());
}

#[test]
fn test_true() {
    use parser::Bexp::True;

    let mut interp = Interpreter::new();
    let b = True;
    assert!(interp.eval_bexp(&b).unwrap());
}

#[test]
fn test_single_assgn() {
    use parser::Com::Assgn;
    use parser::Aexp::Num;

    let prog = Assgn(String::from("x"), Box::new(Num(42)));

    let mut interp = Interpreter::new();
    interp.eval(&prog).unwrap();
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
    interp.eval(&prog).unwrap();
    let s = interp.store();
    assert_eq!(Some(&42), s.get(&String::from("x")));
    assert_eq!(Some(&420), s.get(&String::from("y")));
}

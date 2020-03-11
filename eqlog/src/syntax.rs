use crate::signature::*;
use std::fmt::{self, Display, Formatter};
use std::collections::HashMap;

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub enum Term {
    Variable(String),
    Wildcard(),
    Operation(String, Vec<Term>),
}

impl Term {
    fn visit_subterms<'a, V: FnMut(&'a Term)>(&'a self, mut v: V) {
        self.visit_subterms_impl(&mut v);
    }
    fn visit_subterms_impl<'a, V: FnMut(&'a Term)>(&'a self, v: &mut V) {
        match self {
            Term::Operation(_, args) => {
                for arg in args {
                    arg.visit_subterms_impl(v);
                }
            },
            _ => (),
        }
        v(self);
    }
}

impl Display for Term {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            Term::Variable(var) => {
                f.write_str(var)
            },
            Term::Wildcard() => {
                f.write_str("_")
            }
            Term::Operation(op, args) => {
                f.write_str(op)?;
                f.write_str("(")?;
                let mut arg_it = args.iter();
                if let Some(arg0) = arg_it.next() {
                    arg0.fmt(f)?;
                    
                    for arg in arg_it {
                        f.write_str(", ")?;
                        arg.fmt(f)?;
                    }
                }
                f.write_str(")")
            }
        }
    }
}

#[test]
fn test_term_display() {
    let v = Term::Variable("abc".to_string());
    assert_eq!(v.to_string(), "abc");
    let w = Term::Wildcard();
    assert_eq!(w.to_string(), "_");
    let o = Term::Operation("fun".to_string(), vec![v.clone(), w.clone()]);
    assert_eq!(o.to_string(), "fun(abc, _)");
    let o1 = Term::Operation("Fun".to_string(), vec![o.clone()]);
    assert_eq!(o1.to_string(), "Fun(fun(abc, _))");
    let o2 = Term::Operation("p".to_string(), vec![]);
    assert_eq!(o2.to_string(), "p()");
}

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub enum Atom {
    Equal(Term, Term),
    Defined(Term),
    Predicate(String, Vec<Term>),
}

impl Atom {
    fn visit_subterms<'a, V: FnMut(&'a Term)>(&'a self, mut v: V) {
        match self {
            Atom::Equal(lhs, rhs) => {
                lhs.visit_subterms(&mut v);
                rhs.visit_subterms(&mut v);
            },
            Atom::Defined(t) => {
                t.visit_subterms(&mut v);
            },
            Atom::Predicate(_, args) => {
                for arg in args {
                    arg.visit_subterms(&mut v);
                }
            }
        }
    }
}

impl Display for Atom {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            Atom::Equal(lhs, rhs) => {
                lhs.fmt(f)?;
                f.write_str(" = ")?;
                rhs.fmt(f)
            },
            Atom::Defined(t) => {
                f.write_str("~")?;
                t.fmt(f)
            },
            Atom::Predicate(p, args) => {
                f.write_str(p)?;
                f.write_str("(")?;
                let mut arg_it = args.iter();
                if let Some(arg0) = arg_it.next() {
                    arg0.fmt(f)?;
                    
                    for arg in arg_it {
                        f.write_str(", ")?;
                        arg.fmt(f)?;
                    }
                }
                f.write_str(")")
            },
        }
    }
}

#[test]
fn test_atom_display() {
    let v = Term::Variable("abc".to_string());
    let w = Term::Wildcard();
    let o = Term::Operation("fun".to_string(), vec![v.clone(), w.clone()]);

    let e = Atom::Equal(v.clone(), w.clone());
    assert_eq!(e.to_string(), "abc = _");
    let d = Atom::Defined(o.clone());
    assert_eq!(d.to_string(), "~fun(abc, _)");
    let p = Atom::Predicate("p".to_string(), vec![v.clone(), o.clone()]);
    assert_eq!(p.to_string(), "p(abc, fun(abc, _))");
}

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub struct Formula(Vec<Atom>);

impl Formula {
    fn visit_subterms<'a, V: FnMut(&'a Term)>(&'a self, mut v: V) {
        let Formula(atoms) = self;
        for atom in atoms {
            atom.visit_subterms(&mut v);
        }
    }
}

impl Display for Formula {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        let Formula(atoms) = self;
        let mut atom_it = atoms.iter();
        if let Some(atom0) = atom_it.next() {
            atom0.fmt(f)?;

            for atom in atom_it {
                f.write_str(" & ")?;
                atom.fmt(f)?;
            }
        }
        Ok(())
    }
}

#[test]
fn test_formula_display() {
    let abc = Term::Variable("abc".to_string());
    let xyz = Term::Variable("xyz".to_string());

    let e = Atom::Equal(abc.clone(), xyz.clone());
    let d = Atom::Defined(abc.clone());

    let f0 = Formula(vec![]);
    assert_eq!(f0.to_string(), "");
    let f1 = Formula(vec![e.clone()]);
    assert_eq!(f1.to_string(), "abc = xyz");
    let f2 = Formula(vec![e.clone(), d.clone()]);
    assert_eq!(f2.to_string(), "abc = xyz & ~abc");
}

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub enum Sequent {
    Implication(Formula, Formula),
    Reduction(Term, Term),
}

impl Sequent {
    fn visit_subterms<'a, V: FnMut(&'a Term)>(&'a self, mut v: V) {
        match self {
            Sequent::Implication(premise, conclusion) => {
                premise.visit_subterms(&mut v);
                conclusion.visit_subterms(&mut v);
            },
            Sequent::Reduction(from, to) => {
                from.visit_subterms(&mut v);
                to.visit_subterms(&mut v);
            },
        }
    }
}

impl Display for Sequent {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            Sequent::Implication(premise, conclusion) => {
                premise.fmt(f)?;
                f.write_str(" => ")?;
                conclusion.fmt(f)
            },
            Sequent::Reduction(from, to) => {
                from.fmt(f)?;
                f.write_str(" ~> ")?;
                to.fmt(f)
            },
        }
    }
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Theory {
    signature: Signature,
    sort_names: HashMap<String, SortId>,
    predicate_names: HashMap<String, RelationId>,
    operation_names: HashMap<String, RelationId>,
    sequents: Vec<Sequent>,
}

#[derive(Debug, Eq)]
struct RefEquality<'a, T>(&'a T);

// Stolen from
// https://stackoverflow.com/questions/33847537/how-do-i-make-a-pointer-hashable
// and used in check_sorts of Theory's impl
impl<'a, T> std::hash::Hash for RefEquality<'a, T> {
    fn hash<H>(&self, state: &mut H)
    where
        H: std::hash::Hasher,
    {
        (self.0 as *const T).hash(state)
    }
}

impl<'a, 'b, T> PartialEq<RefEquality<'b, T>> for RefEquality<'a, T> {
    fn eq(&self, other: &RefEquality<'b, T>) -> bool {
        self.0 as *const T == other.0 as *const T
    }
}

impl Theory {
    pub fn new() -> Self {
        Theory {
            signature: Signature::new(),
            sort_names: HashMap::new(),
            predicate_names: HashMap::new(),
            operation_names: HashMap::new(),
            sequents: Vec::new(),
        }
    }
    pub fn add_sort(&mut self, name: String) -> SortId {
        assert!(!self.sort_names.contains_key(&name));
        let s = self.signature.add_sort();
        self.sort_names.insert(name, s);
        s
    }
    pub fn add_predicate(&mut self, name: String, arity: Vec<SortId>) -> RelationId {
        assert!(
            !self.predicate_names.contains_key(&name) &&
            !self.operation_names.contains_key(&name)
        );
        let r = self.signature.add_relation(arity);
        self.predicate_names.insert(name, r);
        r
    }
    pub fn add_operation(
        &mut self,
        name: String,
        domain: Vec<SortId>,
        codomain: SortId,
    ) -> RelationId {
        assert!(
            !self.predicate_names.contains_key(&name) &&
            !self.operation_names.contains_key(&name)
        );
        let mut arity = domain;
        arity.push(codomain);
        let r = self.signature.add_relation(arity);
        self.operation_names.insert(name, r);
        r
    }
    pub fn add_sequent(&mut self, sequent: Sequent) {
        Self::check_occurence(&sequent);
        self.check_sorts(&sequent);
        self.sequents.push(sequent);
    }

    fn check_occurence(seq: &Sequent) {
        let mut var_occurences: HashMap<&str, usize> = HashMap::new();
        seq.visit_subterms(|t| {
            match t {
                Term::Variable(name) => {
                    match var_occurences.get_mut(name.as_str()) {
                        Some(occ) => *occ += 1,
                        None => {
                            var_occurences.insert(name, 1);
                        },
                    }
                },
                _ => (),
            }
        });

        for (name, occ_num) in var_occurences {
            if occ_num == 1 {
                panic!("In sequent {}: Variable {} used only once", seq, name);
            }
        }
    }

    fn check_sorts<'a>(&self, seq: &'a Sequent) {
        let require_sort = |
            t: &'a Term,
            s: SortId,
            sort_requirements: &mut HashMap<RefEquality<'a, Term>, SortId>,
        | {
            if let Some(old) = sort_requirements.get(&RefEquality(t)) {
                if *old != s {
                    let (old_name, _) = self.sort_names.iter().find(|(_, s0)| **s0 == *old).unwrap();
                    let (s_name, _) = self.sort_names.iter().find(|(_, s0)| **s0 == s).unwrap();
                    panic!(
                        "In sequent: {}: Term {} has conflicting sorts {} or {}",
                        seq, t, old_name, s_name
                    );
                }
            } else {
                sort_requirements.insert(RefEquality(t), s);
            }
        };

        let require_equal_sorts = |
            lhs: &'a Term,
            rhs: &'a Term,
            sort_requirements: &mut HashMap<RefEquality<'a, Term>, SortId>,
        | {
            if let Some(lhs_sort) = sort_requirements.get(&RefEquality(lhs)) {
                require_sort(rhs, *lhs_sort, sort_requirements);                        
            };
            if let Some(rhs_sort) = sort_requirements.get(&RefEquality(rhs)) {
                require_sort(lhs, *rhs_sort, sort_requirements);                        
            };
        };

        let check_atom = |
            atom: &'a Atom,
            sort_requirements: &mut HashMap<RefEquality<'a, Term>, SortId>,
        | {
            match atom {
                Atom::Defined(_) => (),
                Atom::Equal(lhs, rhs) => require_equal_sorts(lhs, rhs, sort_requirements),
                Atom::Predicate(name, args) => {
                    let relation_id = match self.predicate_names.get(name) {
                        None => panic!("In sequent{}: Undeclared predicate {}", seq, name),
                        Some(relation_id) => *relation_id,
                    };
                    let arity = self.signature.get_arity(relation_id).unwrap();
                    if arity.len() != args.len() {
                        panic!(
                            "In sequent {}: Predicate {} takes {} arguments, but is applied to {} arguments",
                            seq, name, arity.len(), args.len()
                        );
                    }
                    for (t, s) in args.iter().zip(arity) {
                        require_sort(t, *s, sort_requirements);
                    }
                },
            }
        };

        let mut sort_requirements: HashMap<RefEquality<'a, Term>, SortId> = HashMap::new();
        loop {
            let previous_len = sort_requirements.len();

            match seq {
                Sequent::Implication(Formula(premise), Formula(conclusion)) => {
                    for atom in premise.iter().chain(conclusion) {
                        check_atom(atom, &mut sort_requirements);
                    }
                },
                Sequent::Reduction(from, to) => {
                    require_equal_sorts(from, to, &mut sort_requirements);
                },
            };

            seq.visit_subterms(|t| {
                if let Term::Operation(name, args) = t {
                    let relation_id = match self.operation_names.get(name) {
                        None => panic!("In sequent{}: Undeclared operation {}", seq, name),
                        Some(relation_id) => *relation_id,
                    };
                    let arity = self.signature.get_arity(relation_id).unwrap();
                    let codomain = arity.last().unwrap();
                    let domain = &arity[0 .. arity.len() - 1];
                    if domain.len() != args.len() {
                        panic!(
                            "In sequent {}: Operation {} takes {} arguments, but is applied to {} arguments",
                            seq, name, domain.len(), args.len()
                        );
                    }
                    for (arg, s) in args.iter().zip(domain) {
                        require_sort(arg, *s, &mut sort_requirements);
                    }
                    require_sort(t, *codomain, &mut sort_requirements);
                }
            });

            if sort_requirements.len() == previous_len {
                break;
            }
        }
        
        seq.visit_subterms(|t| {
            if sort_requirements.get(&RefEquality(t)).is_none() {
                panic!(
                    "In sequent {}: Sort of term {} could not be inferred",
                    seq, t
                );
            }
        });
    }
}

#[macro_export]
macro_rules! term {
    ($x:ident) => {
        $crate::syntax::Term::Variable(stringify!($x).to_string())
    };
    (_) => {
        $crate::syntax::Term::Wildcard()
    };
    ($f:ident $arg:tt) => {
        term!(@impl
              (|args| $crate::syntax::Term::Operation(stringify!($f).to_string(), args))
              []
              $arg
        )
    };

    // empty argument list
    (@impl $op:tt [] ()) => {
        $op(vec![])
    };

    // singleton argument list with variable
    (@impl $op:tt [] ($var:ident)) => {
        $op(vec![term!($var)])
    };
    // >= 2 arguments; last arg is variable
    (@impl $op:tt [$($parsed_arg:tt)*] ($var:ident) ) => {
        $op(vec![$($parsed_arg),* , (term!($var))])
    };
    // >= 2 arguments; head of unparsed args is variable
    (@impl $op:tt [$($parsed_arg:tt)*] ($var:ident, $($tail:tt)* )) => {
        term!(@impl $op [$($parsed_arg)* (term!($var))] ($($tail)*))
    };

    // singleton argument list with wildcard
    (@impl $op:tt [] (_)) => {
        $op(vec![term!(_)])
    };
    // >= 2 arguments; last arg is wildcard
    (@impl $op:tt [$($parsed_arg:tt)*] (_) ) => {
        $op(vec![$($parsed_arg),* , (term!(_))])
    };
    // >= 2 arguments; head of unparsed args is variable
    (@impl $op:tt [$($parsed_arg:tt)*] (_, $($tail:tt)* )) => {
        term!(@impl $op [$($parsed_arg)* (term!(_))] ($($tail)*))
    };

    // singleton argument list with function call
    (@impl $op:tt [] ($g:ident $arg:tt)) => {
        $op(vec![term!($g $arg)])
    };
    // >= 2 arguments; last arg is function call
    (@impl $op:tt [$($parsed_arg:tt)*] ($g:ident $arg:tt) ) => {
        $op(vec![$($parsed_arg),* , (term!($g $arg))])
    };
    // >= 2 arguments; head of unparsed args is function call
    (@impl $op:tt [$($parsed_arg:tt)*] ($g:ident $arg:tt, $($tail:tt)* )) => {
        term!(@impl $op [$($parsed_arg)* (term!($g $arg))] ($($tail)*))
        // $f($($parsed_arg),* term!($var))
    };
}

#[test]
fn test_term_macro() {
    assert_eq!(term!(_).to_string(), "_");
    assert_eq!(term!(asdf).to_string(), "asdf");
    assert_eq!(term!(f(asdf)).to_string(), "f(asdf)");
    assert_eq!(term!(f(x, asdf)).to_string(), "f(x, asdf)");
    assert_eq!(term!(f(g(x), asdf)).to_string(), "f(g(x), asdf)");
    assert_eq!(term!(f(g(), asdf)).to_string(), "f(g(), asdf)");
    assert_eq!(term!(f(g(), h())).to_string(), "f(g(), h())");
}

#[macro_export]
macro_rules! atom {
    // a defined term
    (~ $($tm:tt)*) => {
        Atom::Defined(term!($($tm)*))
    };
    // a predicate applied to terms
    ($p:ident $args:tt) => {
        term!(@impl
              (|args| $crate::syntax::Atom::Predicate(stringify!($p).to_string(), args))
              []
              $args
        )
    };
    // lhs is an operation term
    ($f:tt $args:tt = $($rhs:tt)*) => {
        Atom::Equal(term!($f $args), term!($($rhs)*))
    };
    // lhs is a variable
    ($lhs:tt = $($rhs:tt)*) => {
        Atom::Equal(term!($lhs), term!($($rhs)*))
    };
}

#[test]
fn test_atom_macro() {
    assert_eq!(atom!(x = y).to_string(), "x = y");
    assert_eq!(atom!(f(x) = y).to_string(), "f(x) = y");
    assert_eq!(atom!(x = g(y)).to_string(), "x = g(y)");
    assert_eq!(atom!(f(x, g(z)) = g(y)).to_string(), "f(x, g(z)) = g(y)");

    assert_eq!(atom!(~x).to_string(), "~x");
    assert_eq!(atom!(~f(x)).to_string(), "~f(x)");
    assert_eq!(atom!(~g(f(x), y)).to_string(), "~g(f(x), y)");

    assert_eq!(atom!(r()).to_string(), "r()");
    assert_eq!(atom!(r(x)).to_string(), "r(x)");
    assert_eq!(atom!(r(x, f(y))).to_string(), "r(x, f(y))");
    assert_eq!(atom!(r(g(x), y)).to_string(), "r(g(x), y)");
    assert_eq!(atom!(rel(g(x, y), y)).to_string(), "rel(g(x, y), y)");
}

#[macro_export]
macro_rules! formula {
    (@impl [$($atoms:tt)*] []) => {
        Formula(vec![$($atoms),*])
    };
    (@impl [$($prev_atoms:tt)*] [$($cur_atom:tt)*]) => {
        formula!(@impl [$($prev_atoms)* (atom!($($cur_atom)*))] [])
    };
    (@impl [$($prev_atoms:tt)*] [$($cur_atom:tt)*] & $($tail:tt)*) => {
        formula!(@impl [$($prev_atoms)* (atom!($($cur_atom)*))] [] $($tail)*)
    };
    (@impl $prev_atoms:tt [$($cur_atom:tt)*] $head:tt $($tail:tt)*) => {
        formula!(@impl $prev_atoms [$($cur_atom)* $head] $($tail)*)
    };

    ($($toks:tt)*) => {
        formula!(@impl [] [] $($toks)*)
    }
}

#[test]
fn test_formula_macro() {
    assert_eq!(formula!().to_string(), "");

    assert_eq!(formula!(f(x, g(z)) = g(y)).to_string(), "f(x, g(z)) = g(y)");
    assert_eq!(formula!(~g(f(x), y)).to_string(), "~g(f(x), y)");
    assert_eq!(formula!(rel(g(x, y), y)).to_string(), "rel(g(x, y), y)");

    assert_eq!(
        formula!(f(x, g(z)) = g(y) & ~g(f(x), y)).to_string(),
        "f(x, g(z)) = g(y) & ~g(f(x), y)"
    );
    assert_eq!(
        formula!(f(x, g(z)) = g(y) & ~g(f(x), y) & rel(g(x, y), y)).to_string(),
        "f(x, g(z)) = g(y) & ~g(f(x), y) & rel(g(x, y), y)"
    );
}

#[macro_export]
macro_rules! sequent {
    (@impl [$($from:tt)*] ~> $($to:tt)*) => {
        $crate::syntax::Sequent::Reduction(
            term!($($from)*),
            term!($($to)*)
        )
    };
    (@impl [$($prem:tt)*] => $($con:tt)*) => {
        $crate::syntax::Sequent::Implication(
            formula!($($prem)*),
            formula!($($con)*)
        )
    };
    (@impl [$($from:tt)*] $to:tt $($tail:tt)*) => {
        sequent!(@impl [$($from)* $to] $($tail)*)
    };
    ($($toks:tt)*) => {
        sequent!(@impl [] $($toks)*)
    };
}

#[test]
fn test_sequent_macro() {
    assert_eq!(sequent!( => ).to_string(), " => ");
    assert_eq!(
        sequent!(f(x, g(z)) = g(y) => ).to_string(),
        "f(x, g(z)) = g(y) => "
    );
    assert_eq!(
        sequent!( => f(x, g(z)) = g(y)).to_string(),
        " => f(x, g(z)) = g(y)"
    );
    assert_eq!(
        sequent!(f(x, g(z)) = g(y) => r(g(x), y)).to_string(),
        "f(x, g(z)) = g(y) => r(g(x), y)"
    );
    assert_eq!(
        sequent!(f(x, g(z)) = g(y) & r(g(x), y) => a(x) & b()).to_string(),
        "f(x, g(z)) = g(y) & r(g(x), y) => a(x) & b()"
    );

    assert_eq!(
        sequent!(x ~> y).to_string(),
        "x ~> y"
    );
    assert_eq!(
        sequent!(f(x, g(z)) ~> g(y)).to_string(),
        "f(x, g(z)) ~> g(y)"
    );
}

#[cfg(test)]
mod test_theory {
    use super::*;

    fn theory() -> Theory {
        let mut theory: Theory = Theory::new();
        let s0 = theory.add_sort("s0".to_string());
        let s1 = theory.add_sort("s1".to_string());
        theory.add_operation("o".to_string(), vec![s1, s0], s1);
        theory.add_predicate("p".to_string(), vec![s0, s1]);
        theory
    }

    #[test]
    fn add_sequent_valid() {
        let mut theory = theory();
        theory.add_sequent(sequent!(
            p(x, y) & p(y, _) => o(x, y) = o(y, x) & ~o(x, x)
        ));
    }

    #[test] #[should_panic]
    fn add_sequent_undetermined_sort() {
        let mut theory = theory();
        theory.add_sequent(sequent!(
            p(x, y) => x = y & z = z
        ));
    }

    #[test] #[should_panic]
    fn add_sequent_predicate_wrong_argument_number() {
        let mut theory = theory();
        theory.add_sequent(sequent!(
            p(x, y, z) => p(x, y, z)
        ));
    }

    #[test] #[should_panic]
    fn add_sequent_operation_wrong_argument_number() {
        let mut theory = theory();
        theory.add_sequent(sequent!(
            ~o(x, y, z) => ~o(x, y, z)
        ));
    }

    #[test] #[should_panic]
    fn add_sequent_wrong_sorts_operation() {
        let mut theory = theory();
        theory.add_sequent(sequent!(
            ~o(x, y) => ~o(y, x)
        ));
    }

    #[test] #[should_panic]
    fn add_sequent_invalid_1() {
        let mut theory = theory();
        theory.add_sequent(sequent!(
            p(x, y, z) & ~z => x = y
        ));
    }
}

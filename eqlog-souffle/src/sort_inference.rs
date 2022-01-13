use ena::unify::EqUnifyValue;
use super::signature::*;
use super::ast::*;
use std::collections::HashMap;
use super::error::{SortCheckResult, SortCheckError};
use super::union_map::*;

use SortCheckError::*;

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
struct Sort(String);

impl EqUnifyValue for Sort { }

// 'a is the lifetime of the Signature, 'b is the lifetime of terms.
struct SortInference<'a, 'b> {
    signature: &'a Signature,
    term_sorts: UnionMap<&'b Term, Option<Sort>>,
}

type TermSortMap<'a> = UnionMap<&'a Term, Option<Sort>>;

fn into_conflict<'a>(term: &'a Term) -> impl 'a + Fn((Sort, Sort)) -> SortCheckError {
    move |(Sort(s0), Sort(s1))| { SortCheckError::ConflictingSort(term.clone(), s0, s1) }
}

fn add_term<'a>(
    tm: &'a Term,
    term_sorts: &mut TermSortMap<'a>,
    signature: &Signature,
) -> SortCheckResult<()> {
    use Term::*;
    match tm {
        Variable(_) => (),
        Wildcard(_) => (),
        Application(fun_name, args) => {
            let (_, dom, cod) = signature.lookup_func(fun_name)?;
            if args.len() != dom.len() {
                return Err(WrongArgumentNumber { expected: dom.len(), got: args.len() });
            }
            for (arg, arg_sort) in args.iter().zip(dom) {
                term_sorts.update(arg, Some(Sort(arg_sort.to_string()))).map_err(into_conflict(arg))?;
            }
            term_sorts.update(tm, Some(Sort(cod.to_string()))).map_err(into_conflict(tm))?;
        }
    }
    Ok(())
}

fn add_equation<'a>(
    lhs: &'a Term,
    rhs: &'a Term,
    term_sorts: &mut TermSortMap<'a>,
    signature: &Signature,
) -> SortCheckResult<()> {
    add_term(lhs, term_sorts, signature)?;
    add_term(rhs, term_sorts, signature)?;
    term_sorts.unify(lhs, rhs).map_err(into_conflict(rhs))
}

fn add_atom<'a>(
    atom: &'a Atom,
    term_sorts: &mut TermSortMap<'a>,
    signature: &Signature,
) -> SortCheckResult<()> {
    use Atom::*;
    match atom {
        Equal(tm0, tm1) => { add_equation(tm0, tm1, term_sorts, signature)?; },
        Defined(tm, sort) => {
            add_term(tm, term_sorts, signature)?;
            if let Some(s) = sort {
                term_sorts.update(tm, Some(Sort(s.to_string()))).map_err(into_conflict(tm))?;
            }
        },
        Predicate(pred_name, args) => {
            let (_, arity) = signature.lookup_pred(pred_name)?;
            if args.len() != arity.len() {
                return Err(WrongArgumentNumber { expected: arity.len(), got: args.len() });
            }
            for (arg, arg_sort) in args.iter().zip(arity) {
                add_term(arg, term_sorts, signature)?;
                term_sorts.update(arg, Some(Sort(arg_sort.to_string()))).map_err(into_conflict(arg))?;
            }
        },
    };
    Ok(())
}

pub fn infer_sorts<'a>(
    sequent: &'a Sequent,
    signature: &Signature,
) -> SortCheckResult<HashMap<&'a Term, String>> {
    let mut term_sorts = TermSortMap::new();

    use Sequent::*;
    match sequent {
        Implication(premise, conclusion) => {
            for atom in premise.0.iter().chain(conclusion.0.iter()) {
                add_atom(atom, &mut term_sorts, signature)?;
            }
        },
        //Introduction(premise, conclusion) => {
        //    for atom in premise.0.iter().chain(conclusion.0.iter()) {
        //        add_atom(atom, &mut term_sorts, signature)?;
        //    }
        //},
        Reduction(from, to) => {
            add_equation(from, to, &mut term_sorts, signature)?;
        },
        ConditionalReduction(premise, from, to) => {
            for atom in premise.0.iter() {
                add_atom(atom, &mut term_sorts, signature)?;
            }
            add_equation(from, to, &mut term_sorts, signature)?;
        },
    };

    let mut result: HashMap<&'a Term, String> = HashMap::new();
    for (tm, sort) in term_sorts.iter() {
        match sort {
            Some(Sort(s)) => {
                result.insert(tm, s);
            },
            None => {
                return Err(UnspecifiedSort(tm.clone()));
            },
        }
    }
    Ok(result)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::grammar::*;
    use std::boxed::Box;


    fn s() -> String { "S".to_string() }
    fn t() -> String { "T".to_string() }
    fn p() -> String { "P".to_string() }
    fn f() -> String { "F".to_string() }
    fn signature() -> Signature {
        let mut signature = Signature::new();
        signature.insert_sort(s()).unwrap();
        signature.insert_sort(t()).unwrap();
        signature.insert_pred(p(), vec![s(), t()]).unwrap();
        signature.insert_func(f(), vec![t()], s()).unwrap();
        signature
    }

    fn term(src: &'static str) -> &'static Term {
        Box::leak(Box::new(TermParser::new().parse(src).unwrap()))
    }
    fn sequent(src: &'static str) -> &'static Sequent {
        Box::leak(Box::new(SequentParser::new().parse(src).unwrap()))
    }

    #[test]
    fn valid_sequents() {
        let sig = signature();
        assert_eq!(
            infer_sorts(sequent("P(x0, y0) & P(x1, y1) => P(x0, y1)"), &sig).unwrap(),
            hashmap!{
                term("x0") => s(),
                term("x1") => s(),
                term("y0") => t(),
                term("y1") => t(),
            }
        );
        assert_eq!(
            infer_sorts(sequent("P(x, y0) & P(x, y1) => F(y0) = F(y1)"), &sig).unwrap(),
            hashmap!{
                term("x") => s(),
                term("y0") => t(),
                term("y1") => t(),
                term("F(y0)") => s(),
                term("F(y1)") => s(),
            }
        );
        assert_eq!(
            infer_sorts(sequent("!F(y0) & P(x, y0) & P(x, y1) => F(y0) = F(y1)"), &sig).unwrap(),
            hashmap!{
                term("x") => s(),
                term("y0") => t(),
                term("F(y0)") => s(),
                term("y1") => t(),
                term("F(y1)") => s(),
            }
        );
        assert_eq!(
            infer_sorts(sequent("!F(y0) & P(x, y0) & P(x, y1) => F(y1) = F(y0)"), &sig).unwrap(),
            infer_sorts(sequent("!F(y0) & P(x, y0) & P(x, y1) => F(y0) = F(y1)"), &sig).unwrap(),
        );
        assert_eq!(
            infer_sorts(sequent("P(x, y) => !F(y)"), &sig).unwrap(),
            hashmap!{
                term("x") => s(),
                term("y") => t(),
                term("F(y)") => s(),
            }
        );
        assert_eq!(
            infer_sorts(sequent("F(x) = y & F(x) = z => y = z"), &sig).unwrap(),
            hashmap!{
                term("x") => t(),
                term("F(x)") => s(),
                term("y") => s(),
                term("z") => s(),
            }
        );
        assert_eq!(
            infer_sorts(sequent("!(x : S) & !(y : S) => x = y"), &sig).unwrap(),
            hashmap!{
                term("x") => s(),
                term("y") => s(),
            }
        );
    }

    #[test]
    fn invalid_sequents() {
        let sig = signature();
        // Wrong argument number:
        assert!(infer_sorts(sequent("P(x, y, z) => "), &sig).is_err());
        assert!(infer_sorts(sequent("F() => "), &sig).is_err());

        // Wrong argument sorts:
        assert!(infer_sorts(sequent("P(x, y) => P(y, x)"), &sig).is_err());
        assert!(infer_sorts(sequent("F(x) = x => "), &sig).is_err());
        assert!(infer_sorts(sequent("F(x) = y => F(F(x)) = F(y)"), &sig).is_err());
        assert!(infer_sorts(sequent("P(x, F(x)) => "), &sig).is_err());

        // Sort of var can't be inferred:
        assert!(infer_sorts(sequent("x = y & y = z => x = z"), &sig).is_err());

        // Sort of var can't be inferred:
        assert!(infer_sorts(sequent("x = y & y = z => x = z"), &sig).is_err());

        // Wrong sort ascription:
        assert!(infer_sorts(sequent("!(F(x) : T)  => x = x"), &sig).is_err());
    }
}

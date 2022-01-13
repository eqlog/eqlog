use super::ast::*;
use std::collections::HashSet;
use super::error::{SortCheckResult, SortCheckError};

use SortCheckError::*;
use super::signature::Signature;
use super::sort_inference::infer_sorts;

fn collect_terms<'a, A: Ast>(ast: &'a A) -> HashSet<&'a Term> {
    let mut tms: HashSet<&'a Term> = HashSet::new();
    ast.for_each_subterm(|tm| { tms.insert(tm); });
    tms
}

// TODO: Crude.
// - The only supported non-surjective implications are of the form
//  
//     A1 & ... & An => !Func(t1, ..., tm)
//   
//   with t1, ..., tm all defined in the premise.  Other conclusions may not contain an atom of the
//   form !tm.
// - For these other ("complex") conclusions, it doesn't understand congruence, and depends on
//   order.  If the conclusion is B1 & ... & Bm with the Bi atoms, then the following must hold for
//   all i:
//   - If Bi is of the form Pred(t1, ..., tk), then the tk must have been defined in the premise or
//     in one of the Bj with j < i.
//   - If Bi is an equality s = t, then either s or t must be defined from the premise or Bj, j <
//     i, and the same must hold for the arguments of the other term.  (Also both s and t may be
//     defined already.) For Bj, j > i, both s and t are considered as defined.
//   - Bi cannot be of the form !t.
fn check_implication(premise: &Formula, conclusion: &Formula) -> SortCheckResult<()> {
    use Atom::*;
    use Term::*;

    let mut defined_terms = collect_terms(premise);

    if let [Defined(tm, _)] = conclusion.0.as_slice() {
        let args = match tm {
            Application(_, args) => args,
            Variable(_) => { return Err(VariableOrWildcardInConclusionDefineAtom(tm.clone())); },
            Wildcard(_) => { return Err(VariableOrWildcardInConclusionDefineAtom(tm.clone())); },
        };

        if let Some(bad_arg) = args.iter().find(|&arg| !defined_terms.contains(arg)) {
            return Err(SubtermOfDefineConclusionUndefined(bad_arg.clone()));
        }

        return Ok(());
    }

    for atom in conclusion.0.iter() {
        use Atom::*;
        match atom {
            Equal(tm0, tm1) => {
                let undefined_tm = 
                    match (defined_terms.contains(tm0), defined_terms.contains(tm1)) {
                        (true, true) => continue,
                        (false, false) => {
                            return Err(BothSidesUndefined(tm0.clone(), tm1.clone()));
                        }
                        (true, false) => tm1,
                        (false, true) => tm0,
                    };

                let mut undefined_subterm: Option<&Term> = None;
                undefined_tm.for_each_subterm(|subterm| {
                    if !defined_terms.contains(subterm) && subterm != undefined_tm {
                        undefined_subterm = Some(subterm);
                    }
                });

                if let Some(subterm) = undefined_subterm {
                    return Err(SubtermUndefined(subterm.clone()));
                }

                defined_terms.insert(undefined_tm);
            },
            Defined(tm, _) => {
                return Err(DefineInComplexConclusion(tm.clone()));
            },
            Predicate(_, args) => {
                for arg in args {
                    if !defined_terms.contains(arg) {
                        return Err(SubtermUndefined(arg.clone()));
                    }
                }
            },
        }
    }
    Ok(())

}

pub fn check_theory(decls: &[Declaration]) -> SortCheckResult<Signature> {
    let mut signature = Signature::new();
    for decl in decls {
        use Declaration::*;
        match decl {
            Sort(s) => { signature.insert_sort(s.to_string())?; },
            Predicate { name, arity } => {
                signature.insert_pred(name.to_string(), arity.clone())?;
            },
            Function { name, dom, cod } => {
                signature.insert_func(name.to_string(), dom.clone(), cod.to_string())?;
            },
            Axiom(sequent) => {
                use Sequent::*;
                infer_sorts(sequent, &mut signature)?;
                match sequent {
                    Implication(premise, conclusion) => {
                        check_implication(premise, conclusion)?;
                    },
                    Reduction(_, _) => (),
                    ConditionalReduction(_, _, _) => (),
                };
            },
        };
    }
    Ok(signature)
}

#[cfg(test)]
mod tests {
    use super::*;
    use Atom::*;
    use Term::*;
    use Sequent::*;
    use crate::grammar::*;

    #[test]
    fn valid_theories() {
        let cat = TheoryParser::new().parse("\
            Sort Ob;\n\
            Sort Mor;\n\
            Func dom : Mor -> Ob;\n\
            Func cod : Mor -> Ob;\n\
            Func comp : Mor * Mor -> Mor;\n\
            Axiom cod(f) = dom(g) => !comp(g, f);\n\
            Func id : Ob -> Mor;\n\
            Axiom comp(id(cod(f)), f) ~> f;\n\
            Axiom comp(f, id(dom(f))) ~> f;\n\
            Axiom comp(comp(h, g), f) ~> comp(h, comp(g, f));\n\
            Axiom comp(h, comp(g, f)) ~> comp(comp(h, g), f);\n\
        ").unwrap();
        check_theory(&cat).unwrap();

        //let sig = signature();
        //// Wrong argument number:
        //assert!(infer_sorts(sequent("P(x, y, z) => "), &sig).is_err());
        //assert!(infer_sorts(sequent("F() => "), &sig).is_err());

        //// Wrong argument sorts:
        ////assert_eq!(infer_sorts(sequent("P(x, y) => P(y, x)"), &sig).unwrap(), hashmap!{});
        //assert!(infer_sorts(sequent("P(x, y) => P(y, x)"), &sig).is_err());
        //assert!(infer_sorts(sequent("F(x) = x => "), &sig).is_err());
        //assert!(infer_sorts(sequent("F(x) = y => F(F(x)) = F(y)"), &sig).is_err());

        //// // Not surjective:
        //// assert!(infer_sorts(&sig, sequent("P(x, y) => !F(y)")).is_err());
        //// assert!(infer_sorts(&sig, sequent("P(x, y0) & P(x, y1) => F(y0) = F(y1)")).is_err());

        //// Sort of var can't be inferred:
        //assert!(infer_sorts(sequent("x = y  & y = z => x = z"), &sig).is_err());

        //// // Variable only in conclusion, i.e. not epi:
        //// assert!(infer_sorts(&sig, sequent("!F(x) =!> F(x) = y")).is_err());
    }
}

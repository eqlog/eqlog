use crate::ast::*;
use crate::error::*;
use crate::unification::*;

// A term unification data structure to keep track of whether a term is equal to a term that has
// already occurred in the rule.
struct OccurredMerge {}
impl MergeFn<bool> for OccurredMerge {
    fn merge(&mut self, lhs_occurred: bool, rhs_occurred: bool) -> bool {
        lhs_occurred || rhs_occurred
    }
}
type OccurredMap<'a> = TermUnification<'a, bool, OccurredMerge>;

/// Adds terms and equalities of an [IfAtom] to an [OccurredMap].
fn process_if_atom<'a>(atom: &IfAtom, context: &'a TermContext, occurred: &mut OccurredMap<'a>) {
    for tm in atom.iter_subterms(context) {
        occurred[tm] = true;
    }

    match &atom.data {
        IfAtomData::Equal(lhs, rhs) => {
            occurred.union(*lhs, *rhs);
        }
        IfAtomData::Defined(_) => {}
        IfAtomData::Pred { .. } => {}
        IfAtomData::Var { .. } => {}
    }
}

/// Checks that no new variables occur in a [ThenAtom].
///
/// The only exception is a variable `v` in an atom `v := t!`, which must *not* have occurred.
fn check_then_atom_epic(
    atom: &ThenAtom,
    context: &TermContext,
    occurred: &OccurredMap,
) -> Result<(), CompileError> {
    let check_occurred = |term: Term| -> Result<(), CompileError> {
        match context.data(term) {
            TermData::Variable(name) => {
                if !occurred[term] {
                    return Err(CompileError::VariableIntroducedInThenStmt {
                        var: name.clone(),
                        location: Some(context.loc(term)),
                    });
                }
            }
            TermData::Wildcard => {
                return Err(CompileError::WildcardInThenStmt {
                    location: Some(context.loc(term)),
                })
            }
            TermData::Application { .. } => {}
        };

        Ok(())
    };

    match &atom.data {
        ThenAtomData::Equal(_, _) => {
            for tm in atom.iter_subterms(context) {
                check_occurred(tm)?;
            }
        }
        ThenAtomData::Defined { var, term } => {
            for tm in context.iter_subterms(*term) {
                check_occurred(tm)?;
            }
            if let Some(var) = var {
                if occurred[*var] {
                    return Err(CompileError::ThenDefinedVarNotNew {
                        location: context.loc(*var),
                    });
                }
            }
        }
        ThenAtomData::Pred { pred: _, args } => {
            for tm in args
                .iter()
                .copied()
                .flat_map(|arg| context.iter_subterms(arg))
            {
                check_occurred(tm)?;
            }
        }
    }

    Ok(())
}

/// Checks that an epic [ThenAtom] is surjective.
///
/// Non-surjectivity is only allowed in [ThenAtomData::Defined].
fn check_then_atom_surjective<'a>(
    atom: &ThenAtom,
    context: &'a TermContext,
    occurred: &OccurredMap<'a>,
) -> Result<(), CompileError> {
    // Check that non-surjectivity can only occur using ThenAtomData::Defined.
    match &atom.data {
        ThenAtomData::Equal(lhs, rhs) => {
            let lhs = *lhs;
            let rhs = *rhs;
            if !occurred[lhs] && !occurred[rhs] {
                return Err(CompileError::ConclusionEqualityOfNewTerms {
                    location: Some(atom.loc),
                });
            }

            if !occurred[lhs] || !occurred[rhs] {
                let new = if occurred[lhs] { rhs } else { lhs };
                use TermData::*;
                match context.data(new) {
                    TermData::Variable(_) | TermData::Wildcard => {
                        assert!(
                            occurred[new],
                            "new variables or wildcards cannot appear in an epic then atom"
                        );
                    }
                    Application { args, .. } => {
                        if let Some(arg) = args.iter().find(|arg| !occurred[**arg]) {
                            return Err(CompileError::ConclusionEqualityArgNew {
                                location: Some(context.loc(*arg)),
                            });
                        }
                    }
                }
            }
        }
        ThenAtomData::Pred { pred: _, args } => {
            if let Some(arg) = args.iter().copied().find(|arg| !occurred[*arg]) {
                return Err(CompileError::ConclusionPredicateArgNew {
                    location: Some(context.loc(arg)),
                });
            }
        }
        ThenAtomData::Defined { var: _, term: _ } => {}
    }
    Ok(())
}

/// Adds terms and equalities of a [ThenAtom] to an [OccurredMap].
fn process_then_atom<'a>(
    atom: &ThenAtom,
    context: &'a TermContext,
    occurred: &mut OccurredMap<'a>,
) {
    for tm in atom.iter_subterms(context) {
        occurred[tm] = true;
    }

    match &atom.data {
        ThenAtomData::Equal(lhs, rhs) => {
            occurred.union(*lhs, *rhs);
        }
        ThenAtomData::Defined { var, term } => {
            if let Some(var) = var {
                occurred.union(*var, *term);
            }
        }
        ThenAtomData::Pred { .. } => {}
    }
}

pub fn check_epic(rule: &RuleDecl) -> Result<(), CompileError> {
    let context = &rule.term_context;
    let mut occurred = OccurredMap::new(context, vec![false; context.len()], OccurredMerge {});
    for stmt in rule.body.iter() {
        match &stmt.data {
            StmtData::If(atom) => {
                process_if_atom(atom, context, &mut occurred);
            }
            StmtData::Then(atom) => {
                occurred.congruence_closure();
                check_then_atom_epic(atom, context, &occurred)?;
                check_then_atom_surjective(atom, context, &occurred)?;
                process_then_atom(atom, context, &mut occurred);
            }
        }
    }

    Ok(())
}

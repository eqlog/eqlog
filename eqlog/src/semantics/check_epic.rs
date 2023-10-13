use std::collections::BTreeMap;
use std::collections::BTreeSet;

use crate::ast::*;
use crate::error::*;
use crate::grammar_util::*;
use crate::unification::*;
use eqlog_eqlog::*;

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
            TermData::Variable(_) => {
                if !occurred[term] {
                    return Err(CompileError::VariableIntroducedInThenStmt {
                        location: context.loc(term),
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

pub fn check_surjective<'a>(
    eqlog: &Eqlog,
    locations: &BTreeMap<Loc, Location>,
) -> Result<(), CompileError> {
    let should_be_ok: BTreeSet<El> = eqlog.iter_el_should_be_surjective_ok().collect();
    let is_ok: BTreeSet<El> = eqlog.iter_el_is_surjective_ok().collect();
    let not_ok: Option<(TermNode, Location)> = should_be_ok
        .difference(&is_ok)
        .copied()
        .flat_map(|el| {
            eqlog.iter_semantic_el().filter_map(move |(tm, tm_el)| {
                if eqlog.are_equal_el(tm_el, el) {
                    let loc = eqlog.term_node_loc(tm).unwrap();
                    let location = *locations.get(&loc).unwrap();
                    Some((tm, location))
                } else {
                    None
                }
            })
        })
        .min_by_key(|(_, location)| location.1);

    let (_, location): (TermNode, Location) = match not_ok {
        Some(not_ok) => not_ok,
        None => {
            return Ok(());
        }
    };

    Err(CompileError::SurjectivityViolation { location })
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

pub fn check_epic_new(
    eqlog: &Eqlog,
    locations: &BTreeMap<Loc, Location>,
) -> Result<(), CompileError> {
    let bad_location: Option<Location> = eqlog
        .iter_term_should_be_epic_ok()
        .filter_map(|tm| {
            let name = eqlog.iter_var_term_node().find_map(|(var_tm, ident)| {
                if eqlog.are_equal_term_node(tm, var_tm) {
                    Some(ident)
                } else {
                    None
                }
            })?;
            let virt_name = eqlog.real_virt_ident(name).unwrap();
            if !eqlog.var_before_term(tm, virt_name) {
                let loc = eqlog.term_node_loc(tm).unwrap();
                let location = *locations.get(&loc).unwrap();
                Some(location)
            } else {
                None
            }
        })
        .min_by_key(|location| location.1);

    match bad_location {
        Some(location) => Err(CompileError::VariableIntroducedInThenStmt { location }),
        None => Ok(()),
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

use std::collections::BTreeSet;

use super::symbol_table::*;
use crate::ast::*;
use crate::error::*;
use crate::unification::*;

// The term unification used for type inference and checking. For each term, we infer a set of
// types that the term must have, and in the end check that the set has precisely one element.
struct TypeMerge {}
impl<'a> MergeFn<BTreeSet<&'a str>> for TypeMerge {
    fn merge(&mut self, mut lhs: BTreeSet<&'a str>, rhs: BTreeSet<&'a str>) -> BTreeSet<&'a str> {
        lhs.extend(rhs);
        lhs
    }
}
type TypeConstraints<'a> = TermUnification<'a, BTreeSet<&'a str>, TypeMerge>;

fn collect_term_type_constraints<'a, 'b>(
    symbols: &'a SymbolTable,
    context: &'a TermContext,
    types: &'b mut TypeConstraints<'a>,
) -> Result<(), CompileError> {
    for tm in context.iter_terms() {
        match context.data(tm) {
            TermData::Application { func, args } => {
                let loc = context.loc(tm);
                let FuncDecl {
                    arg_decls, result, ..
                } = symbols.get_func(func, loc)?;
                if args.len() != arg_decls.len() {
                    return Err(CompileError::FunctionArgumentNumber {
                        function: func.clone(),
                        expected: arg_decls.len(),
                        got: args.len(),
                        location: context.loc(tm),
                    });
                }
                for (arg, arg_decl) in args.iter().copied().zip(arg_decls) {
                    types[arg].insert(&arg_decl.typ);
                }
                types[tm].insert(result);
            }
            TermData::Wildcard | TermData::Variable(_) => (),
        }
    }
    Ok(())
}

fn collect_if_atom_type_constraints<'a, 'b>(
    symbols: &'a SymbolTable,
    context: &'a TermContext,
    atom: &'a IfAtom,
    types: &'b mut TypeConstraints<'a>,
) -> Result<(), CompileError> {
    match &atom.data {
        IfAtomData::Equal(lhs, rhs) => {
            types.union(*lhs, *rhs);
        }
        IfAtomData::Defined(_) => {}
        IfAtomData::Pred { pred, args } => {
            let PredDecl { arg_decls, .. } = symbols.get_pred(pred, atom.loc)?;
            if args.len() != arg_decls.len() {
                return Err(CompileError::PredicateArgumentNumber {
                    predicate: pred.clone(),
                    expected: arg_decls.len(),
                    got: args.len(),
                    location: atom.loc,
                });
            }
            for (arg, arg_decl) in args.iter().copied().zip(arg_decls) {
                types[arg].insert(arg_decl.typ.as_str());
            }
        }
        IfAtomData::Var { term, typ } => {
            symbols.get_type(typ, context.loc(*term))?;
            types[*term].insert(typ);
        }
    }
    Ok(())
}

fn collect_then_atom_type_constraints<'a, 'b>(
    symbols: &'a SymbolTable,
    atom: &'a ThenAtom,
    types: &'b mut TypeConstraints<'a>,
) -> Result<(), CompileError> {
    match &atom.data {
        ThenAtomData::Equal(lhs, rhs) => {
            types.union(*lhs, *rhs);
        }
        ThenAtomData::Pred { pred, args } => {
            let PredDecl { arg_decls, .. } = symbols.get_pred(pred, atom.loc)?;
            if args.len() != arg_decls.len() {
                return Err(CompileError::PredicateArgumentNumber {
                    predicate: pred.clone(),
                    expected: arg_decls.len(),
                    got: args.len(),
                    location: atom.loc,
                });
            }
            for (arg, arg_decl) in args.iter().copied().zip(arg_decls) {
                types[arg].insert(arg_decl.typ.as_str());
            }
        }
        ThenAtomData::Defined { var, term } => {
            if let Some(var) = var {
                types.union(*var, *term);
            }
        }
    }
    Ok(())
}

/// Checks that all terms have precisely one assigned type.
fn into_unique_types<'a>(
    context: &TermContext,
    mut types: TypeConstraints<'a>,
) -> Result<TermMap<&'a str>, CompileError> {
    // Merge all syntactically equal terms (i.e. variables with the same name and all terms
    // implied by functionality/right-uniqueness of functions.
    types.congruence_closure();

    for tm in context.iter_terms() {
        match types[tm].len() {
            0 => {
                return Err(CompileError::UndeterminedTermType {
                    location: context.loc(tm),
                })
            }
            1 => (),
            _ => {
                return Err(CompileError::ConflictingTermType {
                    location: context.loc(tm),
                    types: types[tm].iter().map(|typ| typ.to_string()).collect(),
                })
            }
        }
    }

    let types = types
        .freeze()
        .map(|types| types.into_iter().next().unwrap());
    Ok(types)
}

/// Infers types for terms appearing in a rule.
pub fn infer_types<'a>(
    symbols: &'a SymbolTable<'a>,
    rule: &'a RuleDecl,
) -> Result<TermMap<&'a str>, CompileError> {
    let context = &rule.term_context;
    let mut types = TermUnification::new(
        context,
        vec![BTreeSet::new(); rule.term_context.len()],
        TypeMerge {},
    );

    collect_term_type_constraints(symbols, context, &mut types)?;

    for stmt in rule.body.iter() {
        match &stmt.data {
            StmtData::If(atom) => {
                collect_if_atom_type_constraints(symbols, context, &atom, &mut types)?;
            }
            StmtData::Then(atom) => {
                collect_then_atom_type_constraints(symbols, &atom, &mut types)?;
            }
        }
    }

    let types = into_unique_types(&context, types)?;
    Ok(types)
}

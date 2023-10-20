use super::symbol_table::*;
use crate::ast::*;
use crate::error::*;

fn collect_term_type_constraints<'a, 'b>(
    symbols: &'a SymbolTable,
    context: &'a TermContext,
) -> Result<(), CompileError> {
    for tm in context.iter_terms() {
        match context.data(tm) {
            TermData::Application { func, args } => {
                let loc = context.loc(tm);
                let FuncDecl { arg_decls, .. } = symbols.get_func(func, loc)?;
                if args.len() != arg_decls.len() {
                    return Err(CompileError::FunctionArgumentNumber {
                        function: func.clone(),
                        expected: arg_decls.len(),
                        got: args.len(),
                        location: context.loc(tm),
                    });
                }
            }
            TermData::Wildcard | TermData::Variable(_) => (),
        }
    }
    Ok(())
}

fn collect_if_atom_type_constraints<'a, 'b>(
    symbols: &'a SymbolTable,
    atom: &'a IfAtom,
) -> Result<(), CompileError> {
    match &atom.data {
        IfAtomData::Equal(_, _) => {}
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
        }
        IfAtomData::Var { .. } => {}
    }
    Ok(())
}

fn collect_then_atom_type_constraints<'a, 'b>(
    symbols: &'a SymbolTable,
    atom: &'a ThenAtom,
) -> Result<(), CompileError> {
    match &atom.data {
        ThenAtomData::Equal(_, _) => {}
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
        }
        ThenAtomData::Defined { .. } => {}
    }
    Ok(())
}

/// Infers types for terms appearing in a rule.
pub fn infer_types<'a>(
    symbols: &'a SymbolTable<'a>,
    rule: &'a RuleDecl,
) -> Result<(), CompileError> {
    let context = &rule.term_context;

    collect_term_type_constraints(symbols, context)?;

    for stmt in rule.body.iter() {
        match &stmt.data {
            StmtData::If(atom) => {
                collect_if_atom_type_constraints(symbols, &atom)?;
            }
            StmtData::Then(atom) => {
                collect_then_atom_type_constraints(symbols, &atom)?;
            }
        }
    }

    Ok(())
}

//! Match-statement validation: each pattern must be a constructor, the
//! cases must all belong to the same enum, and the case list must cover
//! every constructor of that enum.
//!
//! Earlier passes already weed out obviously bad patterns: [`crate::syntactic`]
//! rejects variable, wildcard and member-func patterns and nested
//! constructor args; [`crate::scope_checks::bindings`] requires pattern
//! variables to be fresh. By the time this pass runs, every well-formed
//! pattern is either an `App` whose func is an ambient ctor name, or
//! something one of those passes has already flagged.
//!
//! The check is purely AST + [`Signature`] driven: it does not consult the
//! per-rule [`crate::algebra::structure::Structure`]s. The set of
//! constructors a case pattern names is enough to identify the enum and
//! decide exhaustiveness; the scrutinee's element type plays no role here.

use std::collections::{BTreeMap, BTreeSet};

use crate::algebra::signature::Signature;
use crate::ast::*;
use crate::error::CompileError;
use crate::scopes::{Scopes, Symbol};

/// Walks every match statement in `rid`'s body and appends any match
/// diagnostics it finds to `errors`, in source order.
pub fn check_rule_matches(
    rid: RuleDeclId,
    ast: &Ast,
    scopes: &Scopes,
    signature: &Signature,
    errors: &mut Vec<CompileError>,
) {
    let body = ast.rule_decl(rid).body.clone();
    let mut match_stmts: Vec<MatchStmtId> = Vec::new();
    collect_from_block(ast, &body, &mut match_stmts);
    for stmt in match_stmts {
        check_match(stmt, ast, scopes, signature, errors);
    }
}

fn collect_from_block(ast: &Ast, stmts: &[StmtId], out: &mut Vec<MatchStmtId>) {
    for s in stmts {
        match *ast.stmt(*s) {
            Stmt::Match(mid) => {
                out.push(mid);
                let cases = ast.match_stmt(mid).cases.clone();
                for case in cases {
                    let body = ast.match_case(case).body.clone();
                    collect_from_block(ast, &body, out);
                }
            }
            Stmt::Branch(bid) => {
                let blocks = ast.branch_stmt(bid).blocks.clone();
                for block in blocks {
                    collect_from_block(ast, &block, out);
                }
            }
            Stmt::If(_) | Stmt::Then(_) => {}
        }
    }
}

/// Resolves `pattern` to the constructor it names, if any. A pattern that
/// fails to resolve here is the responsibility of [`crate::syntactic`] or
/// the symbol-lookup pass; this function quietly skips it.
fn pattern_ctor(pattern: TermId, ast: &Ast, scopes: &Scopes) -> Option<CtorDeclId> {
    let Term::App(aid) = *ast.term(pattern) else {
        return None;
    };
    let head = ast.app_term(aid).head;
    let Term::Ident(id) = *ast.term(head) else {
        return None;
    };
    let scope = scopes.entry(id);
    let name = &ast.ident_term(id).name;
    match scopes.lookup(scope, name)? {
        Symbol::Ctor(cid) => Some(cid),
        _ => None,
    }
}

/// Looks up the [`EnumDeclId`] a constructor belongs to via its registered
/// codomain in `signature`. Returns `None` when the constructor is
/// malformed (its signature did not register).
fn ctor_enum(ctor: CtorDeclId, signature: &Signature) -> Option<EnumDeclId> {
    let fid = signature.func_for_ctor_decl(ctor)?;
    let codomain = signature.func(fid).codomain;
    signature.enum_decl_for_type(codomain)
}

fn check_match(
    stmt: MatchStmtId,
    ast: &Ast,
    scopes: &Scopes,
    signature: &Signature,
    errors: &mut Vec<CompileError>,
) {
    let cases = ast.match_stmt(stmt).cases.clone();

    // For each enum that appears among the case ctors, remember the first
    // case ctor that introduced it. BTreeMap keeps the order deterministic.
    let mut first_ctor_per_enum: BTreeMap<EnumDeclId, CtorDeclId> = BTreeMap::new();
    let mut used_ctors: BTreeSet<CtorDeclId> = BTreeSet::new();
    for case in &cases {
        let pattern = ast.match_case(*case).pattern;
        let Some(ctor) = pattern_ctor(pattern, ast, scopes) else {
            continue;
        };
        used_ctors.insert(ctor);
        let Some(enum_id) = ctor_enum(ctor, signature) else {
            continue;
        };
        first_ctor_per_enum.entry(enum_id).or_insert(ctor);
    }

    if first_ctor_per_enum.len() >= 2 {
        let mut iter = first_ctor_per_enum.values().copied();
        let first = iter.next().unwrap();
        let second = iter.next().unwrap();
        errors.push(CompileError::MatchConflictingEnum {
            match_stmt_location: ast.loc(stmt),
            first_ctor_decl_location: ast.loc(first),
            second_ctor_decl_location: ast.loc(second),
        });
        return;
    }

    let Some((&enum_id, _)) = first_ctor_per_enum.iter().next() else {
        return;
    };
    for ctor in ast.enum_decl(enum_id).ctors.clone() {
        if !used_ctors.contains(&ctor) {
            errors.push(CompileError::MatchNotExhaustive {
                match_location: ast.loc(stmt),
                missing_ctor_decl_location: ast.loc(ctor),
            });
        }
    }
}

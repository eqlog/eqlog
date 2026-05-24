//! Position-local binding checks on rule bodies. See [`check_bindings`] for
//! the entry point.
//!
//! Each check asks, at a specific AST position, whether a variable name is
//! already bound in the enclosing scope:
//!
//! * [`CompileError::VariableIntroducedInThenStmt`]: a variable occurs in a
//!   `then` atom in an epic position without having been bound earlier.
//! * [`CompileError::ThenDefinedVarNotNew`]: the variable slot of a
//!   `then v := t` is already in scope.
//! * [`CompileError::MatchPatternArgVarIsNotFresh`]: a variable used as a
//!   constructor argument in a match pattern is already bound in the
//!   enclosing scope.
//!
//! All findings are collected and returned; the caller is responsible for
//! merging them with errors from later passes so that the global error
//! priority ordering applies.

use crate::ast::*;
use crate::error::CompileError;
use crate::resolution::{NameResolution, ResolvedIdentTerm, VarBindingId};

/// Walks rule bodies under `module` and returns all binding-position errors
/// in source order.
pub fn check_bindings(ast: &Ast, names: &NameResolution, module: ModuleId) -> Vec<CompileError> {
    let mut checker = BindingsChecker {
        ast,
        names,
        errors: Vec::new(),
    };
    checker.walk_module(module);
    checker.errors
}

struct BindingsChecker<'a> {
    ast: &'a Ast,
    names: &'a NameResolution,
    errors: Vec<CompileError>,
}

impl<'a> BindingsChecker<'a> {
    fn walk_module(&mut self, module: ModuleId) {
        for decl in self.ast.module(module).decls.clone() {
            self.walk_decl(decl);
        }
    }

    fn walk_decl(&mut self, decl: DeclId) {
        match *self.ast.decl(decl) {
            Decl::Type(_) | Decl::Pred(_) | Decl::Func(_) | Decl::Const(_) | Decl::Enum(_) => {}
            Decl::Rule(id) => {
                let body = self.ast.rule_decl(id).body.clone();
                self.walk_stmt_block(&body);
            }
            Decl::Model(id) => {
                for child in self.ast.model_decl(id).body.clone() {
                    self.walk_decl(child);
                }
            }
        }
    }

    fn walk_stmt_block(&mut self, stmts: &[StmtId]) {
        for stmt in stmts {
            self.walk_stmt(*stmt);
        }
    }

    fn walk_stmt(&mut self, stmt: StmtId) {
        match *self.ast.stmt(stmt) {
            Stmt::If(_) => {}
            Stmt::Then(id) => {
                let atom = self.ast.then_stmt(id).atom;
                self.check_then_atom(atom);
            }
            Stmt::Branch(id) => {
                for block in self.ast.branch_stmt(id).blocks.clone() {
                    self.walk_stmt_block(&block);
                }
            }
            Stmt::Match(id) => {
                for case in self.ast.match_stmt(id).cases.clone() {
                    self.check_match_case_pattern(case);
                    let body = self.ast.match_case(case).body.clone();
                    self.walk_stmt_block(&body);
                }
            }
        }
    }

    fn check_then_atom(&mut self, atom: ThenAtomId) {
        match *self.ast.then_atom(atom) {
            ThenAtom::Equal(id) => {
                let EqualAtom { lhs, rhs } = *self.ast.equal_atom(id);
                self.check_epic_term(lhs);
                self.check_epic_term(rhs);
            }
            ThenAtom::Defined(id) => {
                let DefinedThenAtom { var, term } = *self.ast.defined_then_atom(id);
                if let Some(var) = var {
                    self.check_then_defined_var(atom, var);
                }
                self.check_epic_term(term);
            }
            ThenAtom::Pred(id) => {
                let PredAtom { args, .. } = *self.ast.pred_atom(id);
                for arg in self.ast.term_list(args).terms.clone() {
                    self.check_epic_term(arg);
                }
            }
        }
    }

    /// Mirrors eqlog's `term_should_be_epic_ok` propagation: seeded by
    /// `then`-atom terms and descending only into app-term arguments. A
    /// variable in such a position is an error unless it was bound earlier.
    fn check_epic_term(&mut self, term: TermId) {
        match *self.ast.term(term) {
            Term::Ident(id) => {
                if let ResolvedIdentTerm::Var(binding) = self.names.resolved_ident(id) {
                    let name = &self.names.binding(binding).name;
                    if !self.binding_visible_before(term, name, binding) {
                        self.errors
                            .push(CompileError::VariableIntroducedInThenStmt {
                                location: self.ast.loc(term),
                            });
                    }
                }
            }
            Term::MemberConst(id) => {
                self.check_epic_term(self.ast.member_const_term(id).receiver);
            }
            Term::Wildcard => {}
            Term::App(id) => {
                let args = self.ast.app_term(id).args;
                for arg in self.ast.term_list(args).terms.clone() {
                    self.check_epic_term(arg);
                }
            }
            Term::Dom(_) | Term::Cod(_) | Term::MorApp(_) => {}
        }
    }

    fn binding_visible_before(&self, term: TermId, name: &str, binding: VarBindingId) -> bool {
        self.names.entry(term).lookup(name) == Some(binding)
    }

    /// The variable slot of `then v := t`. Wildcards are fine; an identifier
    /// must not already be in scope before the initializer is resolved.
    fn check_then_defined_var(&mut self, atom: ThenAtomId, var: TermId) {
        let name = match *self.ast.term(var) {
            Term::Ident(id) => &self.ast.ident_term(id).name,
            Term::Wildcard => return,
            Term::App(_) | Term::MemberConst(_) | Term::Dom(_) | Term::Cod(_) | Term::MorApp(_) => {
                unreachable!("defined-then variable terms are checked by syntactic.rs")
            }
        };
        if self.names.entry(atom).lookup(name).is_some() {
            self.errors.push(CompileError::ThenDefinedVarNotNew {
                location: self.ast.loc(var),
            });
        }
    }

    /// Variables used as direct constructor arguments in a match pattern must
    /// be fresh in the enclosing scope. Non-var args (wildcards, Dom/Cod/etc.)
    /// are handled by other passes.
    fn check_match_case_pattern(&mut self, case: MatchCaseId) {
        let pattern = self.ast.match_case(case).pattern;
        let app = match *self.ast.term(pattern) {
            Term::App(id) => id,
            _ => return,
        };
        let args = self.ast.app_term(app).args;
        for arg in self.ast.term_list(args).terms.clone() {
            if let Term::Ident(id) = *self.ast.term(arg) {
                if let ResolvedIdentTerm::Var(binding) = self.names.resolved_ident(id) {
                    let name = &self.names.binding(binding).name;
                    if self.names.entry(arg).lookup(name).is_some() {
                        self.errors
                            .push(CompileError::MatchPatternArgVarIsNotFresh {
                                location: self.ast.loc(arg),
                            });
                    }
                }
            }
        }
    }
}

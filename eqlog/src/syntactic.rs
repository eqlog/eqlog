//! Syntactic AST checks. See [`check_syntactic`] for the entry point.
//!
//! This pass runs right after parsing and catches errors that can be decided
//! purely from the AST shape, without any scope or type information. It walks
//! the arena in source order, accumulates all errors it finds, and returns
//! the earliest one.

use crate::ast::*;
use crate::error::CompileError;

/// Walks `ast` rooted at `module` and returns the first syntactic error in
/// source order, or `Ok(())` if the program is syntactically clean.
pub fn check_syntactic(ast: &Ast, module: ModuleId) -> Result<(), CompileError> {
    let mut checker = SyntacticChecker {
        ast,
        errors: Vec::new(),
    };
    checker.walk_module(module);
    checker.errors.into_iter().min().map_or(Ok(()), Err)
}

struct SyntacticChecker<'a> {
    ast: &'a Ast,
    errors: Vec<CompileError>,
}

impl<'a> SyntacticChecker<'a> {
    fn walk_module(&mut self, module: ModuleId) {
        let decls = self.ast.module(module).decls.clone();
        for decl in decls {
            self.walk_decl(decl);
        }
    }

    fn walk_decl(&mut self, decl: DeclId) {
        match *self.ast.decl(decl) {
            Decl::Type(_) => {}
            Decl::Pred(id) => {
                let args = self.ast.pred_decl(id).args;
                self.check_signature_arg_list(args);
            }
            Decl::Func(id) => {
                let FuncDecl { args, result, .. } = *self.ast.func_decl(id);
                self.check_signature_arg_list(args);
                self.check_signature_type_expr(result);
            }
            Decl::Enum(id) => {
                let ctors = self.ast.enum_decl(id).ctors.clone();
                for ctor in ctors {
                    let args = self.ast.ctor_decl(ctor).args;
                    self.check_signature_arg_list(args);
                }
            }
            Decl::Rule(id) => {
                let body = self.ast.rule_decl(id).body.clone();
                self.walk_stmt_block(&body);
            }
            Decl::Model(id) => {
                let body = self.ast.model_decl(id).body.clone();
                for child in body {
                    self.walk_decl(child);
                }
            }
        }
    }

    fn check_signature_arg_list(&mut self, list: ArgDeclListId) {
        let args = self.ast.arg_decl_list(list).args.clone();
        for arg in args {
            let typ = self.ast.arg_decl(arg).typ;
            self.check_signature_type_expr(typ);
        }
    }

    fn check_signature_type_expr(&mut self, type_expr: TypeExprId) {
        if let TypeExpr::Member(id) = *self.ast.type_expr(type_expr) {
            self.errors
                .push(CompileError::IllegalMemberTypeExprInArgDecl {
                    location: self.ast.loc(id),
                });
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
                let blocks = self.ast.branch_stmt(id).blocks.clone();
                for block in blocks {
                    self.walk_stmt_block(&block);
                }
            }
            Stmt::Match(id) => {
                let cases = self.ast.match_stmt(id).cases.clone();
                for case in cases {
                    self.check_match_case(case);
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
                self.check_then_term(lhs);
                self.check_then_term(rhs);
            }
            ThenAtom::Defined(id) => {
                let DefinedThenAtom { var, term } = *self.ast.defined_then_atom(id);
                if let Some(var_term) = var {
                    self.check_defined_then_var(var_term);
                }
                self.check_then_term(term);
            }
            ThenAtom::Pred(id) => {
                let args = self.ast.pred_atom(id).args;
                let terms = self.ast.term_list(args).terms.clone();
                for arg in terms {
                    self.check_then_term(arg);
                }
            }
        }
    }

    /// Flag wildcards in a term that appears in a `then` atom, recursing into
    /// `App` term arguments but not into other compound forms (matching the
    /// historical eqlog-side propagation).
    fn check_then_term(&mut self, term: TermId) {
        match *self.ast.term(term) {
            Term::Wildcard => {
                self.errors.push(CompileError::WildcardInThenStmt {
                    location: self.ast.loc(term),
                });
            }
            Term::App(id) => {
                let args = self.ast.app_term(id).args;
                let terms = self.ast.term_list(args).terms.clone();
                for arg in terms {
                    self.check_then_term(arg);
                }
            }
            Term::Var(_) | Term::Dom(_) | Term::Cod(_) | Term::MorApp(_) => {}
        }
    }

    /// The variable slot of a `defined := term` statement must be a variable
    /// or a wildcard.
    fn check_defined_then_var(&mut self, var_term: TermId) {
        match *self.ast.term(var_term) {
            Term::Var(_) | Term::Wildcard => {}
            _ => {
                self.errors.push(CompileError::ThenDefinedNotVar {
                    location: self.ast.loc(var_term),
                });
            }
        }
    }

    fn check_match_case(&mut self, case: MatchCaseId) {
        let pattern = self.ast.match_case(case).pattern;
        let location = self.ast.loc(pattern);
        match *self.ast.term(pattern) {
            Term::Var(_) => {
                self.errors
                    .push(CompileError::MatchPatternIsVariable { location });
            }
            Term::Wildcard => {
                self.errors
                    .push(CompileError::MatchPatternIsWildcard { location });
            }
            Term::App(id) => {
                let AppTerm { func, args } = *self.ast.app_term(id);
                match *self.ast.func_expr(func) {
                    FuncExpr::Member(_) => {
                        self.errors
                            .push(CompileError::MatchPatternIsMemberFunc { location });
                    }
                    FuncExpr::Ambient(_) => {}
                }
                let terms = self.ast.term_list(args).terms.clone();
                for arg in terms {
                    if let Term::App(_) = *self.ast.term(arg) {
                        self.errors.push(CompileError::MatchPatternCtorArgIsApp {
                            location: self.ast.loc(arg),
                        });
                    }
                }
            }
            Term::Dom(_) | Term::Cod(_) | Term::MorApp(_) => {}
        }
    }
}

//! Syntactic AST checks. See [`check_syntactic`] for the entry point.
//!
//! This pass runs right after parsing and catches errors that can be decided
//! purely from the AST shape, without any scope or type information. It
//! walks the arena in source order (depth-first, pre-order) and returns the
//! first error it finds.

use crate::ast::*;
use crate::error::CompileError;

/// Walks `ast` rooted at `module` and returns the first syntactic error in
/// source order, or `Ok(())` if the program is syntactically clean.
pub fn check_syntactic(ast: &Ast, module: ModuleId) -> Result<(), CompileError> {
    let checker = SyntacticChecker { ast };
    checker.walk_module(module)
}

struct SyntacticChecker<'a> {
    ast: &'a Ast,
}

type Check = Result<(), CompileError>;

impl<'a> SyntacticChecker<'a> {
    fn walk_module(&self, module: ModuleId) -> Check {
        for decl in self.ast.module(module).decls.clone() {
            self.walk_decl(decl)?;
        }
        Ok(())
    }

    fn walk_decl(&self, decl: DeclId) -> Check {
        match *self.ast.decl(decl) {
            Decl::Type(_) => Ok(()),
            Decl::Pred(id) => {
                let args = self.ast.pred_decl(id).args;
                self.check_signature_arg_list(args)
            }
            Decl::Func(id) => {
                let FuncDecl { args, result, .. } = *self.ast.func_decl(id);
                self.check_signature_arg_list(args)?;
                self.check_signature_type_expr(result)
            }
            Decl::Enum(id) => {
                for ctor in self.ast.enum_decl(id).ctors.clone() {
                    let args = self.ast.ctor_decl(ctor).args;
                    self.check_signature_arg_list(args)?;
                }
                Ok(())
            }
            Decl::Rule(id) => {
                let body = self.ast.rule_decl(id).body.clone();
                self.walk_stmt_block(&body)
            }
            Decl::Model(id) => {
                for child in self.ast.model_decl(id).body.clone() {
                    self.walk_decl(child)?;
                }
                Ok(())
            }
        }
    }

    fn check_signature_arg_list(&self, list: ArgDeclListId) -> Check {
        for arg in self.ast.arg_decl_list(list).args.clone() {
            let typ = self.ast.arg_decl(arg).typ;
            self.check_signature_type_expr(typ)?;
        }
        Ok(())
    }

    fn check_signature_type_expr(&self, type_expr: TypeExprId) -> Check {
        match *self.ast.type_expr(type_expr) {
            TypeExpr::Member(id) => Err(CompileError::IllegalMemberTypeExprInArgDecl {
                location: self.ast.loc(id),
            }),
            TypeExpr::Ambient(_) | TypeExpr::Mor(_) => Ok(()),
        }
    }

    fn walk_stmt_block(&self, stmts: &[StmtId]) -> Check {
        for stmt in stmts {
            self.walk_stmt(*stmt)?;
        }
        Ok(())
    }

    fn walk_stmt(&self, stmt: StmtId) -> Check {
        match *self.ast.stmt(stmt) {
            Stmt::If(_) => Ok(()),
            Stmt::Then(id) => {
                let atom = self.ast.then_stmt(id).atom;
                self.check_then_atom(atom)
            }
            Stmt::Branch(id) => {
                for block in self.ast.branch_stmt(id).blocks.clone() {
                    self.walk_stmt_block(&block)?;
                }
                Ok(())
            }
            Stmt::Match(id) => {
                for case in self.ast.match_stmt(id).cases.clone() {
                    self.check_match_case(case)?;
                    let body = self.ast.match_case(case).body.clone();
                    self.walk_stmt_block(&body)?;
                }
                Ok(())
            }
        }
    }

    fn check_then_atom(&self, atom: ThenAtomId) -> Check {
        match *self.ast.then_atom(atom) {
            ThenAtom::Equal(id) => {
                let EqualAtom { lhs, rhs } = *self.ast.equal_atom(id);
                self.check_then_term(lhs)?;
                self.check_then_term(rhs)
            }
            ThenAtom::Defined(id) => {
                let DefinedThenAtom { var, term } = *self.ast.defined_then_atom(id);
                if let Some(var_term) = var {
                    self.check_defined_then_var(var_term)?;
                }
                self.check_then_term(term)
            }
            ThenAtom::Pred(id) => {
                let PredAtom { pred, args } = *self.ast.pred_atom(id);
                self.check_then_pred_expr(pred)?;
                for arg in self.ast.term_list(args).terms.clone() {
                    self.check_then_term(arg)?;
                }
                Ok(())
            }
        }
    }

    /// Flag wildcards in a term that appears in a `then` atom, descending
    /// into every subterm.
    fn check_then_term(&self, term: TermId) -> Check {
        match *self.ast.term(term) {
            Term::Wildcard => Err(CompileError::WildcardInThenStmt {
                location: self.ast.loc(term),
            }),
            Term::Var(_) => Ok(()),
            Term::App(id) => {
                let AppTerm { func, args } = *self.ast.app_term(id);
                self.check_then_func_expr(func)?;
                for arg in self.ast.term_list(args).terms.clone() {
                    self.check_then_term(arg)?;
                }
                Ok(())
            }
            Term::Dom(id) => self.check_then_term(self.ast.dom_term(id).arg),
            Term::Cod(id) => self.check_then_term(self.ast.cod_term(id).arg),
            Term::MorApp(id) => {
                let MorAppTerm { mor, arg } = *self.ast.mor_app_term(id);
                self.check_then_term(mor)?;
                self.check_then_term(arg)
            }
        }
    }

    fn check_then_pred_expr(&self, pred_expr: PredExprId) -> Check {
        match *self.ast.pred_expr(pred_expr) {
            PredExpr::Ambient(_) => Ok(()),
            PredExpr::Member(id) => self.check_then_term(self.ast.member_pred_expr(id).term),
        }
    }

    fn check_then_func_expr(&self, func_expr: FuncExprId) -> Check {
        match *self.ast.func_expr(func_expr) {
            FuncExpr::Ambient(_) => Ok(()),
            FuncExpr::Member(id) => self.check_then_term(self.ast.member_func_expr(id).term),
        }
    }

    /// The variable slot of a `defined := term` statement must be a variable
    /// or a wildcard.
    fn check_defined_then_var(&self, var_term: TermId) -> Check {
        match *self.ast.term(var_term) {
            Term::Var(_) | Term::Wildcard => Ok(()),
            Term::App(_) | Term::Dom(_) | Term::Cod(_) | Term::MorApp(_) => {
                Err(CompileError::ThenDefinedNotVar {
                    location: self.ast.loc(var_term),
                })
            }
        }
    }

    fn check_match_case(&self, case: MatchCaseId) -> Check {
        let pattern = self.ast.match_case(case).pattern;
        let location = self.ast.loc(pattern);
        match *self.ast.term(pattern) {
            Term::Var(_) => Err(CompileError::MatchPatternIsVariable { location }),
            Term::Wildcard => Err(CompileError::MatchPatternIsWildcard { location }),
            Term::App(id) => {
                let AppTerm { func, args } = *self.ast.app_term(id);
                match *self.ast.func_expr(func) {
                    FuncExpr::Member(_) => {
                        return Err(CompileError::MatchPatternIsMemberFunc { location });
                    }
                    FuncExpr::Ambient(_) => {}
                }
                for arg in self.ast.term_list(args).terms.clone() {
                    match *self.ast.term(arg) {
                        Term::App(_) => {
                            return Err(CompileError::MatchPatternCtorArgIsApp {
                                location: self.ast.loc(arg),
                            });
                        }
                        Term::Var(_)
                        | Term::Wildcard
                        | Term::Dom(_)
                        | Term::Cod(_)
                        | Term::MorApp(_) => {}
                    }
                }
                Ok(())
            }
            Term::Dom(_) | Term::Cod(_) | Term::MorApp(_) => Ok(()),
        }
    }
}

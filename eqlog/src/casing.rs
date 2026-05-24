//! Casing checks. See [`check_casing`] for the entry point.
//!
//! Two independent analyses share one walk of the module:
//!
//! * [`CompileError::SymbolNotCamelCase`] / [`CompileError::SymbolNotSnakeCase`]:
//!   declaration names must follow the casing expected for their symbol kind.
//! * [`CompileError::VariableNotSnakeCase`]: every variable occurrence in a
//!   rule body must be snake_case.
//!
//! The walk visits nodes in source order and returns the first error found.
//! The caller merges that error with findings from later passes through
//! `CompileError`'s `Ord`.

use convert_case::{Case, Casing};

use crate::ast::*;
use crate::error::{CompileError, SymbolKind};
use crate::grammar_util::Location;
use crate::scopes::{Scopes, Symbol};

/// Walks `ast` rooted at `module` and returns the first casing error in
/// source order, or `Ok(())` if the program is clean.
pub fn check_casing(ast: &Ast, scopes: &Scopes, module: ModuleId) -> Result<(), CompileError> {
    let checker = CasingChecker { ast, scopes };
    checker.walk_module(module)
}

struct CasingChecker<'a> {
    ast: &'a Ast,
    scopes: &'a Scopes,
}

type Check = Result<(), CompileError>;

impl<'a> CasingChecker<'a> {
    fn walk_module(&self, module: ModuleId) -> Check {
        for decl in self.ast.module(module).decls.clone() {
            self.walk_decl(decl)?;
        }
        Ok(())
    }

    fn walk_decl(&self, decl: DeclId) -> Check {
        match *self.ast.decl(decl) {
            Decl::Type(id) => {
                let name = self.ast.type_decl(id).name.clone();
                self.check_camel(name, self.ast.loc(id), SymbolKind::Type)
            }
            Decl::Pred(id) => {
                let name = self.ast.pred_decl(id).name.clone();
                self.check_snake(name, self.ast.loc(id), SymbolKind::Pred)
            }
            Decl::Func(id) => {
                let name = self.ast.func_decl(id).name.clone();
                self.check_snake(name, self.ast.loc(id), SymbolKind::Func)
            }
            Decl::Const(id) => {
                let name = self.ast.const_decl(id).name.clone();
                self.check_snake(name, self.ast.loc(id), SymbolKind::Const)
            }
            Decl::Enum(id) => {
                let name = self.ast.enum_decl(id).name.clone();
                self.check_camel(name, self.ast.loc(id), SymbolKind::Enum)?;
                for ctor in self.ast.enum_decl(id).ctors.clone() {
                    let cname = self.ast.ctor_decl(ctor).name.clone();
                    self.check_camel(cname, self.ast.loc(ctor), SymbolKind::Ctor)?;
                }
                Ok(())
            }
            Decl::Rule(id) => {
                if let Some(name) = self.ast.rule_decl(id).name.clone() {
                    self.check_snake(name, self.ast.loc(id), SymbolKind::Rule)?;
                }
                for stmt in self.ast.rule_decl(id).body.clone() {
                    self.walk_stmt(stmt)?;
                }
                Ok(())
            }
            Decl::Model(id) => {
                let name = self.ast.model_decl(id).name.clone();
                self.check_camel(name, self.ast.loc(id), SymbolKind::Model)?;
                for child in self.ast.model_decl(id).body.clone() {
                    self.walk_decl(child)?;
                }
                Ok(())
            }
        }
    }

    fn check_camel(&self, name: String, location: Location, symbol_kind: SymbolKind) -> Check {
        if name != name.to_case(Case::UpperCamel) {
            return Err(CompileError::SymbolNotCamelCase {
                name,
                location,
                symbol_kind,
            });
        }
        Ok(())
    }

    fn check_snake(&self, name: String, location: Location, symbol_kind: SymbolKind) -> Check {
        if name != name.to_case(Case::Snake) {
            return Err(CompileError::SymbolNotSnakeCase {
                name,
                location,
                symbol_kind,
            });
        }
        Ok(())
    }

    fn walk_stmt(&self, stmt: StmtId) -> Check {
        match *self.ast.stmt(stmt) {
            Stmt::If(id) => self.walk_if_atom(self.ast.if_stmt(id).atom),
            Stmt::Then(id) => self.walk_then_atom(self.ast.then_stmt(id).atom),
            Stmt::Branch(id) => {
                for block in self.ast.branch_stmt(id).blocks.clone() {
                    for s in block {
                        self.walk_stmt(s)?;
                    }
                }
                Ok(())
            }
            Stmt::Match(id) => {
                let MatchStmt { term, cases } = self.ast.match_stmt(id);
                let term = *term;
                let cases = cases.clone();
                self.walk_term(term)?;
                for case in cases {
                    let MatchCase { pattern, body } = self.ast.match_case(case);
                    let pattern = *pattern;
                    let body = body.clone();
                    self.walk_term(pattern)?;
                    for s in body {
                        self.walk_stmt(s)?;
                    }
                }
                Ok(())
            }
        }
    }

    fn walk_if_atom(&self, atom: IfAtomId) -> Check {
        match *self.ast.if_atom(atom) {
            IfAtom::Equal(id) => {
                let EqualAtom { lhs, rhs } = *self.ast.equal_atom(id);
                self.walk_term(lhs)?;
                self.walk_term(rhs)
            }
            IfAtom::Defined(id) => {
                let DefinedIfAtom { term } = *self.ast.defined_if_atom(id);
                self.walk_term(term)
            }
            IfAtom::Pred(id) => {
                let PredAtom { pred, args } = *self.ast.pred_atom(id);
                self.walk_pred_expr(pred)?;
                self.walk_term_list(args)
            }
            IfAtom::Var(id) => {
                let VarIfAtom { term, typ } = *self.ast.var_if_atom(id);
                self.walk_type_expr(typ)?;
                self.walk_term(term)
            }
        }
    }

    fn walk_then_atom(&self, atom: ThenAtomId) -> Check {
        match *self.ast.then_atom(atom) {
            ThenAtom::Equal(id) => {
                let EqualAtom { lhs, rhs } = *self.ast.equal_atom(id);
                self.walk_term(lhs)?;
                self.walk_term(rhs)
            }
            ThenAtom::Defined(id) => {
                let DefinedThenAtom { var, term } = *self.ast.defined_then_atom(id);
                if let Some(var) = var {
                    self.walk_term(var)?;
                }
                self.walk_term(term)
            }
            ThenAtom::Pred(id) => {
                let PredAtom { pred, args } = *self.ast.pred_atom(id);
                self.walk_pred_expr(pred)?;
                self.walk_term_list(args)
            }
        }
    }

    fn walk_term(&self, term: TermId) -> Check {
        match *self.ast.term(term) {
            Term::Ident(id) => self.check_ident_term(id, self.ast.loc(term)),
            Term::Wildcard => Ok(()),
            Term::App(id) => {
                let AppTerm { func, args } = *self.ast.app_term(id);
                self.walk_func_expr(func)?;
                self.walk_term_list(args)
            }
            Term::MemberConst(id) => {
                let MemberConstTerm { receiver, .. } = *self.ast.member_const_term(id);
                self.walk_term(receiver)
            }
            Term::Dom(id) => self.walk_term(self.ast.dom_term(id).arg),
            Term::Cod(id) => self.walk_term(self.ast.cod_term(id).arg),
            Term::MorApp(id) => {
                let MorAppTerm { mor, arg } = *self.ast.mor_app_term(id);
                self.walk_term(mor)?;
                self.walk_term(arg)
            }
        }
    }

    fn walk_term_list(&self, list: TermListId) -> Check {
        for term in self.ast.term_list(list).terms.clone() {
            self.walk_term(term)?;
        }
        Ok(())
    }

    fn check_ident_term(&self, id: IdentTermId, location: Location) -> Check {
        let name = self.ast.ident_term(id).name.clone();
        match self.scopes.lookup(self.scopes.exit(id), &name) {
            Some(Symbol::Var(_)) => self.check_variable_name(name, location),
            _ => Ok(()),
        }
    }

    fn check_variable_name(&self, name: String, location: Location) -> Check {
        if name != name.to_case(Case::Snake) {
            return Err(CompileError::VariableNotSnakeCase { name, location });
        }
        Ok(())
    }

    fn walk_type_expr(&self, type_expr: TypeExprId) -> Check {
        match *self.ast.type_expr(type_expr) {
            TypeExpr::Ambient(_) | TypeExpr::Mor(_) => Ok(()),
            TypeExpr::Member(id) => self.walk_term(self.ast.member_type_expr(id).term),
        }
    }

    fn walk_pred_expr(&self, pred_expr: PredExprId) -> Check {
        match *self.ast.pred_expr(pred_expr) {
            PredExpr::Ambient(_) => Ok(()),
            PredExpr::Member(id) => self.walk_term(self.ast.member_pred_expr(id).term),
        }
    }

    fn walk_func_expr(&self, func_expr: FuncExprId) -> Check {
        match *self.ast.func_expr(func_expr) {
            FuncExpr::Ambient(_) => Ok(()),
            FuncExpr::Member(id) => self.walk_term(self.ast.member_func_expr(id).term),
        }
    }
}

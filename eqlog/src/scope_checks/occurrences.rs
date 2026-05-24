//! Per-rule "variable occurs at least twice" check. See [`check_occurrences`]
//! for the entry point.

use std::collections::BTreeMap;

use crate::ast::*;
use crate::error::CompileError;
use crate::resolution::{NameResolution, ResolvedBinder, ResolvedIdentTerm, VarBindingId};

/// Walk `ast` rooted at `module` and report the first variable occurrence
/// that is not reachable from (and to) another occurrence of the same name
/// via the scope graph, i.e. the first variable that is used only once in
/// its scope.
pub fn check_occurrences(
    ast: &Ast,
    names: &NameResolution,
    module: ModuleId,
) -> Result<(), CompileError> {
    let checker = OccurrencesChecker { ast, names };
    checker.check_module(module)
}

struct OccurrencesChecker<'a> {
    ast: &'a Ast,
    names: &'a NameResolution,
}

#[derive(Copy, Clone)]
struct VarOccurrence {
    binding: VarBindingId,
    location: crate::grammar_util::Location,
}

impl<'a> OccurrencesChecker<'a> {
    fn check_module(&self, module: ModuleId) -> Result<(), CompileError> {
        for decl in self.ast.module(module).decls.clone() {
            self.check_decl(decl)?;
        }
        Ok(())
    }

    fn check_decl(&self, decl: DeclId) -> Result<(), CompileError> {
        match *self.ast.decl(decl) {
            Decl::Type(_) | Decl::Pred(_) | Decl::Func(_) | Decl::Const(_) | Decl::Enum(_) => {
                Ok(())
            }
            Decl::Rule(id) => self.check_rule(id),
            Decl::Model(id) => {
                for child in self.ast.model_decl(id).body.clone() {
                    self.check_decl(child)?;
                }
                Ok(())
            }
        }
    }

    /// Collect every resolved variable occurrence in source order. Constants
    /// do not participate in the variable occurrence rule.
    fn check_rule(&self, rule: RuleDeclId) -> Result<(), CompileError> {
        let mut occurrences: Vec<VarOccurrence> = Vec::new();
        for stmt in self.ast.rule_decl(rule).body.clone() {
            self.collect_stmt(stmt, &mut occurrences);
        }

        let mut counts: BTreeMap<VarBindingId, usize> = BTreeMap::new();
        for occ in &occurrences {
            *counts.entry(occ.binding).or_default() += 1;
        }

        match occurrences
            .into_iter()
            .find(|occ| counts.get(&occ.binding).copied().unwrap_or(0) < 2)
        {
            Some(occ) => Err(CompileError::VariableOccursOnlyOnce {
                name: self.names.binding(occ.binding).name.clone(),
                location: occ.location,
            }),
            None => Ok(()),
        }
    }

    fn collect_stmt(&self, stmt: StmtId, occ: &mut Vec<VarOccurrence>) {
        match *self.ast.stmt(stmt) {
            Stmt::If(id) => self.collect_if_atom(self.ast.if_stmt(id).atom, occ),
            Stmt::Then(id) => self.collect_then_atom(self.ast.then_stmt(id).atom, occ),
            Stmt::Branch(id) => {
                for block in self.ast.branch_stmt(id).blocks.clone() {
                    for s in &block {
                        self.collect_stmt(*s, occ);
                    }
                }
            }
            Stmt::Match(id) => {
                let MatchStmt { term, cases } = self.ast.match_stmt(id);
                let term = *term;
                let cases = cases.clone();
                self.collect_term(term, occ);
                for case in &cases {
                    let MatchCase { pattern, body } = self.ast.match_case(*case);
                    let pattern = *pattern;
                    let body = body.clone();
                    self.collect_term(pattern, occ);
                    for s in &body {
                        self.collect_stmt(*s, occ);
                    }
                }
            }
        }
    }

    fn collect_if_atom(&self, atom: IfAtomId, occ: &mut Vec<VarOccurrence>) {
        match *self.ast.if_atom(atom) {
            IfAtom::Equal(id) => {
                let EqualAtom { lhs, rhs } = *self.ast.equal_atom(id);
                self.collect_term(lhs, occ);
                self.collect_term(rhs, occ);
            }
            IfAtom::Defined(id) => {
                let DefinedIfAtom { term } = *self.ast.defined_if_atom(id);
                self.collect_term(term, occ);
            }
            IfAtom::Pred(id) => {
                let PredAtom { pred, args } = *self.ast.pred_atom(id);
                self.collect_pred_expr(pred, occ);
                self.collect_term_list(args, occ);
            }
            IfAtom::Var(id) => {
                let VarIfAtom { binder, typ, .. } = *self.ast.var_if_atom(id);
                self.collect_type_expr(typ, occ);
                if let Some(binder) = binder {
                    self.collect_binder(binder, occ);
                }
            }
        }
    }

    fn collect_then_atom(&self, atom: ThenAtomId, occ: &mut Vec<VarOccurrence>) {
        match *self.ast.then_atom(atom) {
            ThenAtom::Equal(id) => {
                let EqualAtom { lhs, rhs } = *self.ast.equal_atom(id);
                self.collect_term(lhs, occ);
                self.collect_term(rhs, occ);
            }
            ThenAtom::Defined(id) => {
                let DefinedThenAtom { binder, term, .. } = *self.ast.defined_then_atom(id);
                if let Some(binder) = binder {
                    self.collect_binder(binder, occ);
                }
                self.collect_term(term, occ);
            }
            ThenAtom::Pred(id) => {
                let PredAtom { pred, args } = *self.ast.pred_atom(id);
                self.collect_pred_expr(pred, occ);
                self.collect_term_list(args, occ);
            }
        }
    }

    fn collect_term(&self, term: TermId, occ: &mut Vec<VarOccurrence>) {
        match *self.ast.term(term) {
            Term::Ident(id) => {
                if let ResolvedIdentTerm::Var(binding) = self.names.resolved_ident(id) {
                    occ.push(VarOccurrence {
                        binding,
                        location: self.ast.loc(term),
                    });
                }
            }
            Term::Wildcard => {}
            Term::App(id) => {
                let AppTerm { func, args } = *self.ast.app_term(id);
                self.collect_func_expr(func, occ);
                self.collect_term_list(args, occ);
            }
            Term::MemberConst(id) => {
                let receiver = self.ast.member_const_term(id).receiver;
                self.collect_term(receiver, occ);
            }
            Term::Dom(id) => self.collect_term(self.ast.dom_term(id).arg, occ),
            Term::Cod(id) => self.collect_term(self.ast.cod_term(id).arg, occ),
            Term::MorApp(id) => {
                let MorAppTerm { mor, arg } = *self.ast.mor_app_term(id);
                self.collect_term(mor, occ);
                self.collect_term(arg, occ);
            }
        }
    }

    fn collect_term_list(&self, list: TermListId, occ: &mut Vec<VarOccurrence>) {
        for term in self.ast.term_list(list).terms.clone() {
            self.collect_term(term, occ);
        }
    }

    fn collect_binder(&self, binder: BinderId, occ: &mut Vec<VarOccurrence>) {
        if let ResolvedBinder::Var(binding) = self.names.resolved_binder(binder) {
            occ.push(VarOccurrence {
                binding,
                location: self.ast.loc(binder),
            });
        }
    }

    fn collect_type_expr(&self, type_expr: TypeExprId, occ: &mut Vec<VarOccurrence>) {
        match *self.ast.type_expr(type_expr) {
            TypeExpr::Ambient(_) | TypeExpr::Mor(_) => {}
            TypeExpr::Member(id) => self.collect_term(self.ast.member_type_expr(id).term, occ),
        }
    }

    fn collect_pred_expr(&self, pred_expr: PredExprId, occ: &mut Vec<VarOccurrence>) {
        match *self.ast.pred_expr(pred_expr) {
            PredExpr::Ambient(_) => {}
            PredExpr::Member(id) => self.collect_term(self.ast.member_pred_expr(id).term, occ),
        }
    }

    fn collect_func_expr(&self, func_expr: FuncExprId, occ: &mut Vec<VarOccurrence>) {
        match *self.ast.func_expr(func_expr) {
            FuncExpr::Ambient(_) => {}
            FuncExpr::Member(id) => self.collect_term(self.ast.member_func_expr(id).term, occ),
        }
    }
}

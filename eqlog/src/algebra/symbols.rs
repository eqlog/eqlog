//! Rule-body symbol lookup diagnostics.
//!
//! Signature-position type lookups are handled while building the
//! [`crate::algebra::signature::Signature`]. This pass covers the remaining
//! symbol positions in rule bodies. Ambient lookups are checked directly
//! against [`crate::scopes::Scopes`]; member lookups are reported only when
//! the receiver term has a known model type in the finished
//! [`crate::algebra::populate::RuleStructures`].

use std::collections::BTreeMap;

use crate::algebra::populate::RuleStructures;
use crate::algebra::signature::Signature;
use crate::algebra::structure::StructureId;
use crate::ast::*;
use crate::error::{CompileError, SymbolKind};
use crate::grammar_util::Location;
use crate::scopes::{ScopeId, Scopes, Symbol};

/// Checks every rule body under `module` for symbol lookup failures.
///
/// Member lookups are skipped when their receiver does not have a known model
/// type. In those cases the type diagnostics remain responsible for explaining
/// the invalid receiver.
pub fn check_symbol_lookups(
    ast: &Ast,
    scopes: &Scopes,
    signature: &Signature,
    module: ModuleId,
    rules: &BTreeMap<RuleDeclId, RuleStructures>,
) -> Vec<CompileError> {
    let mut checker = Checker {
        ast,
        scopes,
        signature,
        rules,
        errors: Vec::new(),
    };
    checker.walk_module(module);
    checker.errors
}

struct Checker<'a> {
    ast: &'a Ast,
    scopes: &'a Scopes,
    signature: &'a Signature,
    rules: &'a BTreeMap<RuleDeclId, RuleStructures>,
    errors: Vec<CompileError>,
}

#[derive(Copy, Clone)]
struct RuleCtx<'a> {
    rule: Option<&'a RuleStructures>,
    current: Option<StructureId>,
}

#[derive(Copy, Clone, PartialEq, Eq)]
enum LookupKind {
    Type,
    Pred,
    Func,
    Const,
    Enum,
    Ctor,
    Model,
    Rule,
}

impl LookupKind {
    fn symbol_kind(self) -> SymbolKind {
        match self {
            LookupKind::Type => SymbolKind::Type,
            LookupKind::Pred => SymbolKind::Pred,
            LookupKind::Func => SymbolKind::Func,
            LookupKind::Const => SymbolKind::Const,
            LookupKind::Enum => SymbolKind::Enum,
            LookupKind::Ctor => SymbolKind::Ctor,
            LookupKind::Model => SymbolKind::Model,
            LookupKind::Rule => SymbolKind::Rule,
        }
    }
}

impl Symbol {
    fn lookup_kind(self) -> Option<LookupKind> {
        Some(match self {
            Symbol::Type(_) => LookupKind::Type,
            Symbol::Pred(_) => LookupKind::Pred,
            Symbol::Func(_) => LookupKind::Func,
            Symbol::Const(_) => LookupKind::Const,
            Symbol::Enum(_) => LookupKind::Enum,
            Symbol::Ctor(_) => LookupKind::Ctor,
            Symbol::Model(_) => LookupKind::Model,
            Symbol::Rule(_) => LookupKind::Rule,
            Symbol::Arg(_) | Symbol::Var(_) => return None,
        })
    }
}

impl<'a> Checker<'a> {
    fn walk_module(&mut self, module: ModuleId) {
        for decl in self.ast.module(module).decls.clone() {
            self.walk_decl(decl);
        }
    }

    fn walk_decl(&mut self, decl: DeclId) {
        match *self.ast.decl(decl) {
            Decl::Rule(id) => {
                let ctx = RuleCtx {
                    rule: self.rules.get(&id),
                    current: self.rules.get(&id).map(|_| StructureId(0)),
                };
                let body = self.ast.rule_decl(id).body.clone();
                self.walk_stmt_block(&body, ctx);
            }
            Decl::Model(id) => {
                for child in self.ast.model_decl(id).body.clone() {
                    self.walk_decl(child);
                }
            }
            Decl::Type(_) | Decl::Pred(_) | Decl::Func(_) | Decl::Const(_) | Decl::Enum(_) => {}
        }
    }

    fn walk_stmt_block(&mut self, stmts: &[StmtId], ctx: RuleCtx<'a>) {
        for stmt in stmts {
            self.walk_stmt(*stmt, ctx.rule);
        }
    }

    fn walk_stmt(&mut self, stmt: StmtId, rule: Option<&'a RuleStructures>) {
        match *self.ast.stmt(stmt) {
            Stmt::If(id) => {
                let ctx = RuleCtx {
                    rule,
                    current: rule.and_then(|r| r.stmt_after.get(&stmt).copied()),
                };
                self.walk_if_atom(self.ast.if_stmt(id).atom, ctx);
            }
            Stmt::Then(id) => {
                let ctx = RuleCtx {
                    rule,
                    current: rule.and_then(|r| r.stmt_after.get(&stmt).copied()),
                };
                self.walk_then_atom(self.ast.then_stmt(id).atom, ctx);
            }
            Stmt::Branch(id) => {
                for block in self.ast.branch_stmt(id).blocks.clone() {
                    self.walk_stmt_block(
                        &block,
                        RuleCtx {
                            rule,
                            current: None,
                        },
                    );
                }
            }
            Stmt::Match(id) => {
                let MatchStmt { term, cases } = self.ast.match_stmt(id);
                let term = *term;
                let cases = cases.clone();
                let scrutinee_ctx = RuleCtx {
                    rule,
                    current: rule.and_then(|r| r.match_after_scrutinee.get(&id).copied()),
                };
                self.walk_term(term, scrutinee_ctx);
                for case in cases {
                    let MatchCase { pattern, body } = self.ast.match_case(case).clone();
                    let case_ctx = RuleCtx {
                        rule,
                        current: rule.and_then(|r| r.match_case_starts.get(&case).copied()),
                    };
                    self.walk_match_case_pattern(pattern, case_ctx);
                    self.walk_stmt_block(&body, case_ctx);
                }
            }
        }
    }

    fn walk_if_atom(&mut self, atom: IfAtomId, ctx: RuleCtx<'a>) {
        match *self.ast.if_atom(atom) {
            IfAtom::Equal(id) => {
                let EqualAtom { lhs, rhs } = *self.ast.equal_atom(id);
                self.walk_term(lhs, ctx);
                self.walk_term(rhs, ctx);
            }
            IfAtom::Defined(id) => {
                self.walk_term(self.ast.defined_if_atom(id).term, ctx);
            }
            IfAtom::Pred(id) => self.walk_pred_atom(id, ctx),
            IfAtom::Var(id) => {
                let VarIfAtom { typ, .. } = *self.ast.var_if_atom(id);
                self.check_type_expr(typ, ctx, self.ast.loc(atom));
            }
        }
    }

    fn walk_then_atom(&mut self, atom: ThenAtomId, ctx: RuleCtx<'a>) {
        match *self.ast.then_atom(atom) {
            ThenAtom::Equal(id) => {
                let EqualAtom { lhs, rhs } = *self.ast.equal_atom(id);
                self.walk_term(lhs, ctx);
                self.walk_term(rhs, ctx);
            }
            ThenAtom::Defined(id) => {
                let DefinedThenAtom { term, .. } = *self.ast.defined_then_atom(id);
                self.walk_term(term, ctx);
            }
            ThenAtom::Pred(id) => self.walk_pred_atom(id, ctx),
        }
    }

    fn walk_pred_atom(&mut self, id: PredAtomId, ctx: RuleCtx<'a>) {
        let PredAtom { pred, args } = *self.ast.pred_atom(id);
        self.check_pred_expr(pred, ctx);
        for arg in self.ast.term_list(args).terms.clone() {
            self.walk_term(arg, ctx);
        }
    }

    fn walk_term(&mut self, term: TermId, ctx: RuleCtx<'a>) {
        match *self.ast.term(term) {
            Term::Ident(_) | Term::Wildcard => {}
            Term::App(id) => {
                let AppTerm { func, args } = *self.ast.app_term(id);
                self.check_func_expr(func, ctx, &[LookupKind::Func, LookupKind::Ctor]);
                for arg in self.ast.term_list(args).terms.clone() {
                    self.walk_term(arg, ctx);
                }
            }
            Term::MemberConst(id) => {
                let MemberConstTerm { receiver, name } = *self.ast.member_const_term(id);
                self.walk_term(receiver, ctx);
                let name = self.ast.ident_term(name).name.clone();
                for scope in self.member_receiver_scopes(receiver, ctx) {
                    self.check_member_const_lookup(scope, name.clone(), self.ast.loc(term));
                }
            }
            Term::Dom(id) => self.walk_term(self.ast.dom_term(id).arg, ctx),
            Term::Cod(id) => self.walk_term(self.ast.cod_term(id).arg, ctx),
            Term::MorApp(id) => {
                let MorAppTerm { mor, arg } = *self.ast.mor_app_term(id);
                self.walk_term(mor, ctx);
                self.walk_term(arg, ctx);
            }
        }
    }

    fn walk_match_case_pattern(&mut self, pattern: TermId, ctx: RuleCtx<'a>) {
        let Term::App(app) = *self.ast.term(pattern) else {
            self.walk_term(pattern, ctx);
            return;
        };

        let func = self.ast.app_term(app).func;
        if let FuncExpr::Ambient(id) = *self.ast.func_expr(func) {
            let name = self.ast.ambient_func_expr(id).name.clone();
            self.check_lookup(
                self.scopes.entry(id),
                name,
                &[LookupKind::Ctor],
                self.ast.loc(pattern),
            );
        }

        for arg in self
            .ast
            .term_list(self.ast.app_term(app).args)
            .terms
            .clone()
        {
            self.walk_term(arg, ctx);
        }
    }

    fn check_type_expr(&mut self, typ: TypeExprId, ctx: RuleCtx<'a>, used_at: Location) {
        match *self.ast.type_expr(typ) {
            TypeExpr::Ambient(id) => {
                let name = self.ast.ambient_type_expr(id).name.clone();
                self.check_lookup(
                    self.scopes.entry(id),
                    name,
                    &[LookupKind::Type, LookupKind::Enum, LookupKind::Model],
                    used_at,
                );
            }
            TypeExpr::Mor(id) => {
                let name = self.ast.mor_type_expr(id).name.clone();
                self.check_lookup(self.scopes.entry(id), name, &[LookupKind::Model], used_at);
            }
            TypeExpr::Member(id) => {
                let MemberTypeExpr { term, name } = self.ast.member_type_expr(id).clone();
                self.walk_term(term, ctx);
                for scope in self.member_receiver_scopes(term, ctx) {
                    self.check_member_lookup(
                        scope,
                        name.clone(),
                        &[LookupKind::Type, LookupKind::Enum, LookupKind::Model],
                        used_at,
                    );
                }
            }
        }
    }

    fn check_pred_expr(&mut self, pred: PredExprId, ctx: RuleCtx<'a>) {
        match *self.ast.pred_expr(pred) {
            PredExpr::Ambient(id) => {
                let name = self.ast.ambient_pred_expr(id).name.clone();
                self.check_lookup(
                    self.scopes.entry(id),
                    name,
                    &[LookupKind::Pred],
                    self.ast.loc(pred),
                );
            }
            PredExpr::Member(id) => {
                let MemberPredExpr { term, name } = self.ast.member_pred_expr(id).clone();
                self.walk_term(term, ctx);
                for scope in self.member_receiver_scopes(term, ctx) {
                    self.check_member_lookup(
                        scope,
                        name.clone(),
                        &[LookupKind::Pred],
                        self.ast.loc(pred),
                    );
                }
            }
        }
    }

    fn check_func_expr(&mut self, func: FuncExprId, ctx: RuleCtx<'a>, ambient: &[LookupKind]) {
        match *self.ast.func_expr(func) {
            FuncExpr::Ambient(id) => {
                let name = self.ast.ambient_func_expr(id).name.clone();
                self.check_func_call_lookup(
                    self.scopes.entry(id),
                    name,
                    ambient,
                    self.ast.loc(func),
                );
            }
            FuncExpr::Member(id) => {
                let MemberFuncExpr { term, name } = self.ast.member_func_expr(id).clone();
                self.walk_term(term, ctx);
                for scope in self.member_receiver_scopes(term, ctx) {
                    self.check_member_func_call_lookup(
                        scope,
                        name.clone(),
                        &[LookupKind::Func, LookupKind::Ctor],
                        self.ast.loc(func),
                    );
                }
            }
        }
    }

    fn member_receiver_scopes(&self, term: TermId, ctx: RuleCtx<'a>) -> Vec<ScopeId> {
        let Some(rule) = ctx.rule else {
            return Vec::new();
        };
        let Some(current) = ctx.current else {
            return Vec::new();
        };
        let Some(el) = rule
            .semantic_els
            .get(current.0)
            .and_then(|els| els.get(&term))
        else {
            return Vec::new();
        };
        let Some(structure) = rule.cat.structures.get(current.0) else {
            return Vec::new();
        };
        structure
            .concrete_types_of(*el)
            .into_iter()
            .filter_map(|ct| {
                let model_decl = self.signature.model_decl_for_type(ct.typ)?;
                Some(self.scopes.unordered(model_decl))
            })
            .collect()
    }

    fn check_lookup(
        &mut self,
        scope: ScopeId,
        name: String,
        expected: &[LookupKind],
        used_at: Location,
    ) {
        let decls = lookup_decl_symbols(self.scopes, scope, &name);
        self.check_decl_symbols(name, expected, used_at, decls);
    }

    fn check_func_call_lookup(
        &mut self,
        scope: ScopeId,
        name: String,
        expected: &[LookupKind],
        used_at: Location,
    ) {
        let decls = lookup_decl_symbols(self.scopes, scope, &name);
        if decls.iter().any(|sym| matches!(sym, Symbol::Const(_))) {
            self.errors.push(CompileError::ConstCalledAsFunction {
                name,
                location: used_at,
            });
            return;
        }
        self.check_decl_symbols(name, expected, used_at, decls);
    }

    fn check_member_lookup(
        &mut self,
        scope: ScopeId,
        name: String,
        expected: &[LookupKind],
        used_at: Location,
    ) {
        let decls = lookup_direct_decl_symbols(self.scopes, scope, &name);
        self.check_decl_symbols(name, expected, used_at, decls);
    }

    fn check_member_func_call_lookup(
        &mut self,
        scope: ScopeId,
        name: String,
        expected: &[LookupKind],
        used_at: Location,
    ) {
        let decls = lookup_direct_decl_symbols(self.scopes, scope, &name);
        if decls.iter().any(|sym| matches!(sym, Symbol::Const(_))) {
            self.errors.push(CompileError::ConstCalledAsFunction {
                name,
                location: used_at,
            });
            return;
        }
        self.check_decl_symbols(name, expected, used_at, decls);
    }

    fn check_member_const_lookup(&mut self, scope: ScopeId, name: String, used_at: Location) {
        let decls = lookup_direct_decl_symbols(self.scopes, scope, &name);
        if decls.iter().any(|sym| matches!(sym, Symbol::Const(_))) {
            return;
        }
        if decls
            .iter()
            .any(|sym| matches!(sym, Symbol::Func(_) | Symbol::Ctor(_)))
        {
            self.errors.push(CompileError::FunctionUsedWithoutCall {
                name,
                location: used_at,
            });
            return;
        }
        self.check_decl_symbols(name, &[LookupKind::Const], used_at, decls);
    }

    fn check_decl_symbols(
        &mut self,
        name: String,
        expected: &[LookupKind],
        used_at: Location,
        decls: Vec<Symbol>,
    ) {
        if decls.is_empty() {
            self.errors
                .push(CompileError::UndeclaredSymbol { name, used_at });
            return;
        }

        if decls.iter().any(|sym| {
            sym.lookup_kind()
                .is_some_and(|kind| expected.contains(&kind))
        }) {
            return;
        }

        let found = decls[0];
        let found_kind = found
            .lookup_kind()
            .expect("symbol lookup excludes variables and args");
        self.errors.push(CompileError::BadSymbolKind {
            name,
            expected: expected[0].symbol_kind(),
            found: found_kind.symbol_kind(),
            used_at,
            declared_at: found.location(self.ast),
        });
    }
}

fn lookup_direct_decl_symbols(scopes: &Scopes, scope: ScopeId, name: &str) -> Vec<Symbol> {
    scopes
        .scope(scope)
        .symbols
        .get(name)
        .copied()
        .into_iter()
        .filter(|sym| !matches!(sym, Symbol::Arg(_) | Symbol::Var(_)))
        .collect()
}

fn lookup_decl_symbols(scopes: &Scopes, scope: ScopeId, name: &str) -> Vec<Symbol> {
    match scopes.lookup(scope, name) {
        Some(Symbol::Arg(_) | Symbol::Var(_)) | None => Vec::new(),
        Some(sym) => vec![sym],
    }
}

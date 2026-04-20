//! Dependent signatures: types, predicates and functions, parameterised by
//! enclosing model types.
//!
//! Following the AST conventions of the rest of the crate, ids ([`TypeId`],
//! [`PredId`], [`FuncId`]) are opaque indices into flat `Vec`s on
//! [`Signature`]. The data structs ([`Type`], [`Pred`], [`Func`]) hold the
//! algebraic shape only and carry no source-name information. Downstream
//! callers needing names go through the AST.
//!
//! [`build_signature`] runs in two passes:
//!
//! 1. Walk the AST and register one [`Type`] per `type` / `enum` / `model`
//!    declaration, plus the auto-generated mor companion type for every
//!    model. This produces lookups from AST decl ids to [`TypeId`]s, exposed
//!    via [`Signature::type_for_type_decl`] and friends.
//! 2. Walk the AST again to register [`Pred`]s and [`Func`]s. Type-name
//!    references in pred/func/ctor arg decls (and func result types) are
//!    resolved against the ambient [`crate::scopes::Scopes`] entry of the
//!    relevant AST node, then translated through the pass-1 lookups.
//!
//! Symbol-resolution failures (undeclared names, names that resolve to a
//! non-type symbol) are accumulated as [`CompileError`]s and returned
//! alongside the partial [`Signature`]. The caller is responsible for
//! merging them with errors from other passes.

use std::collections::BTreeMap;

use eqlog_eqlog::SymbolKindCase;

use crate::ast::*;
use crate::error::CompileError;
use crate::grammar_util::Location;
use crate::scopes::{Scopes, Symbol};

#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct TypeId(u32);

#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct PredId(u32);

#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct FuncId(u32);

/// What flavour of declaration a [`Type`] originated from.
///
/// `Mor(model)` is the auto-generated companion type for morphisms between
/// instances of the model type identified by `model`.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum TypeKind {
    Plain,
    Model,
    Enum,
    Mor(TypeId),
}

#[allow(dead_code)]
#[derive(Clone, Debug)]
pub struct Type {
    pub kind: TypeKind,
    /// Enclosing model types, outermost first.
    pub parents: Vec<TypeId>,
}

#[allow(dead_code)]
#[derive(Clone, Debug)]
pub struct Pred {
    /// Enclosing model types, outermost first.
    pub parents: Vec<TypeId>,
    pub arity: Vec<TypeId>,
}

#[allow(dead_code)]
#[derive(Clone, Debug)]
pub struct Func {
    /// Enclosing model types, outermost first.
    pub parents: Vec<TypeId>,
    pub domain: Vec<TypeId>,
    pub codomain: TypeId,
}

/// The pair of [`TypeId`]s a `model` declaration produces: the model type
/// itself and its auto-generated morphism-type companion.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub struct ModelTypeIds {
    pub type_: TypeId,
    pub mor: TypeId,
}

#[derive(Clone, Debug, Default)]
pub struct Signature {
    types: Vec<Type>,
    preds: Vec<Pred>,
    funcs: Vec<Func>,
    type_decls: BTreeMap<TypeDeclId, TypeId>,
    enum_decls: BTreeMap<EnumDeclId, TypeId>,
    model_decls: BTreeMap<ModelDeclId, ModelTypeIds>,
}

impl Signature {
    pub fn type_for_type_decl(&self, id: TypeDeclId) -> TypeId {
        *self
            .type_decls
            .get(&id)
            .expect("type decl was not registered")
    }

    pub fn type_for_enum_decl(&self, id: EnumDeclId) -> TypeId {
        *self
            .enum_decls
            .get(&id)
            .expect("enum decl was not registered")
    }

    pub fn types_for_model_decl(&self, id: ModelDeclId) -> ModelTypeIds {
        *self
            .model_decls
            .get(&id)
            .expect("model decl was not registered")
    }

    fn push_type(&mut self, t: Type) -> TypeId {
        let id = TypeId(self.types.len() as u32);
        self.types.push(t);
        id
    }

    fn push_pred(&mut self, p: Pred) -> PredId {
        let id = PredId(self.preds.len() as u32);
        self.preds.push(p);
        id
    }

    fn push_func(&mut self, f: Func) -> FuncId {
        let id = FuncId(self.funcs.len() as u32);
        self.funcs.push(f);
        id
    }
}

/// Walks `ast` rooted at `module` and produces a [`Signature`] together with
/// any symbol-resolution errors it encounters in pred/func/ctor signatures.
///
/// Pass 1 (type registration) is total. It sees every type/enum/model decl
/// regardless of what later resolves. Pass 2 (relation registration) skips
/// any pred/func/ctor whose arg types or result type fail to resolve, but
/// records the failure as a [`CompileError`].
///
/// `MemberTypeExpr`s in arg-decl positions are silently skipped here because
/// [`crate::syntactic::check_syntactic`] already emits a higher-priority
/// [`CompileError::IllegalMemberTypeExprInArgDecl`] for them.
pub fn build_signature(
    ast: &Ast,
    scopes: &Scopes,
    module: ModuleId,
) -> (Signature, Vec<CompileError>) {
    let mut builder = Builder {
        ast,
        scopes,
        signature: Signature::default(),
        errors: Vec::new(),
    };
    let decls = ast.module(module).decls.clone();
    builder.populate_types(&decls, &[]);
    builder.populate_relations(&decls, &[]);
    (builder.signature, builder.errors)
}

struct Builder<'a> {
    ast: &'a Ast,
    scopes: &'a Scopes,
    signature: Signature,
    errors: Vec<CompileError>,
}

impl<'a> Builder<'a> {
    /// Pass 1: walk the AST registering one [`Type`] per `type`/`enum`/`model`
    /// declaration (plus the mor companion of each model) and recording the
    /// AST-id to [`TypeId`] lookups on [`Signature`].
    fn populate_types(&mut self, decls: &[DeclId], parents: &[TypeId]) {
        for decl in decls {
            match *self.ast.decl(*decl) {
                Decl::Type(id) => {
                    let tid = self.signature.push_type(Type {
                        kind: TypeKind::Plain,
                        parents: parents.to_vec(),
                    });
                    self.signature.type_decls.insert(id, tid);
                }
                Decl::Enum(id) => {
                    let tid = self.signature.push_type(Type {
                        kind: TypeKind::Enum,
                        parents: parents.to_vec(),
                    });
                    self.signature.enum_decls.insert(id, tid);
                }
                Decl::Model(id) => {
                    let model_tid = self.signature.push_type(Type {
                        kind: TypeKind::Model,
                        parents: parents.to_vec(),
                    });
                    let mor_tid = self.signature.push_type(Type {
                        kind: TypeKind::Mor(model_tid),
                        parents: parents.to_vec(),
                    });
                    self.signature.model_decls.insert(
                        id,
                        ModelTypeIds {
                            type_: model_tid,
                            mor: mor_tid,
                        },
                    );
                    let body = self.ast.model_decl(id).body.clone();
                    let mut new_parents = parents.to_vec();
                    new_parents.push(model_tid);
                    self.populate_types(&body, &new_parents);
                }
                Decl::Pred(_) | Decl::Func(_) | Decl::Rule(_) => {}
            }
        }
    }

    /// Pass 2: walk the AST again registering [`Pred`]s and [`Func`]s.
    /// Constructors are treated as functions in the ambient scope of their
    /// enum, with codomain pinned to the enum's [`TypeId`].
    fn populate_relations(&mut self, decls: &[DeclId], parents: &[TypeId]) {
        for decl in decls {
            match *self.ast.decl(*decl) {
                Decl::Pred(id) => {
                    let args = self.ast.pred_decl(id).args;
                    if let Some(arity) = self.resolve_arg_types(args) {
                        self.signature.push_pred(Pred {
                            parents: parents.to_vec(),
                            arity,
                        });
                    }
                }
                Decl::Func(id) => {
                    let FuncDecl { args, result, .. } = *self.ast.func_decl(id);
                    let domain = self.resolve_arg_types(args);
                    let codomain = self.resolve_signature_type_expr(result);
                    if let (Some(domain), Some(codomain)) = (domain, codomain) {
                        self.signature.push_func(Func {
                            parents: parents.to_vec(),
                            domain,
                            codomain,
                        });
                    }
                }
                Decl::Enum(id) => {
                    let codomain = self.signature.type_for_enum_decl(id);
                    let ctors = self.ast.enum_decl(id).ctors.clone();
                    for ctor in ctors {
                        let args = self.ast.ctor_decl(ctor).args;
                        if let Some(domain) = self.resolve_arg_types(args) {
                            self.signature.push_func(Func {
                                parents: parents.to_vec(),
                                domain,
                                codomain,
                            });
                        }
                    }
                }
                Decl::Model(id) => {
                    let model_tid = self.signature.types_for_model_decl(id).type_;
                    let body = self.ast.model_decl(id).body.clone();
                    let mut new_parents = parents.to_vec();
                    new_parents.push(model_tid);
                    self.populate_relations(&body, &new_parents);
                }
                Decl::Type(_) | Decl::Rule(_) => {}
            }
        }
    }

    /// Resolves every arg's type expression. Errors are accumulated for all
    /// args before returning. The final `Option` is `None` iff at least one
    /// resolution failed.
    fn resolve_arg_types(&mut self, args: ArgDeclListId) -> Option<Vec<TypeId>> {
        let arg_ids: Vec<ArgDeclId> = self.ast.arg_decl_list(args).args.clone();
        let mut tids = Vec::with_capacity(arg_ids.len());
        let mut all_ok = true;
        for arg in arg_ids {
            let typ_expr = self.ast.arg_decl(arg).typ;
            match self.resolve_signature_type_expr(typ_expr) {
                Some(tid) => tids.push(tid),
                None => all_ok = false,
            }
        }
        if all_ok {
            Some(tids)
        } else {
            None
        }
    }

    fn resolve_signature_type_expr(&mut self, type_expr: TypeExprId) -> Option<TypeId> {
        let scope = self.scopes.entry(type_expr);
        match *self.ast.type_expr(type_expr) {
            TypeExpr::Ambient(id) => {
                let used_at = self.ast.loc(id);
                let name = self.ast.ambient_type_expr(id).name.clone();
                match self.scopes.lookup(scope, &name) {
                    Some(Symbol::Type(td)) => Some(self.signature.type_for_type_decl(td)),
                    Some(Symbol::Enum(ed)) => Some(self.signature.type_for_enum_decl(ed)),
                    Some(Symbol::Model(md)) => Some(self.signature.types_for_model_decl(md).type_),
                    Some(other) => {
                        // Sig-position ambient accepts type, enum or model.
                        // Mirror eqlog.eql's `should_be_symbol_3(name, type_kind, enum_kind, model_kind, ...)`
                        // by reporting `type` as the primary expected kind.
                        self.emit_wrong_kind(name, other, SymbolKindCase::TypeSymbol(), used_at);
                        None
                    }
                    None => {
                        self.errors
                            .push(CompileError::UndeclaredSymbol { name, used_at });
                        None
                    }
                }
            }
            TypeExpr::Mor(id) => {
                let used_at = self.ast.loc(id);
                let name = self.ast.mor_type_expr(id).name.clone();
                match self.scopes.lookup(scope, &name) {
                    Some(Symbol::Model(md)) => Some(self.signature.types_for_model_decl(md).mor),
                    Some(other) => {
                        // Mirrors eqlog.eql's `should_be_symbol(model_ty_ident, model_kind, ...)`
                        // for sig-position mor type expressions.
                        self.emit_wrong_kind(name, other, SymbolKindCase::ModelSymbol(), used_at);
                        None
                    }
                    None => {
                        self.errors
                            .push(CompileError::UndeclaredSymbol { name, used_at });
                        None
                    }
                }
            }
            TypeExpr::Member(_) => {
                // `crate::syntactic::check_syntactic` already emits
                // `IllegalMemberTypeExprInArgDecl` for these. We'd just
                // duplicate.
                None
            }
        }
    }

    fn emit_wrong_kind(
        &mut self,
        name: String,
        found: Symbol,
        expected: SymbolKindCase,
        used_at: Location,
    ) {
        match symbol_kind_case(found) {
            Some(found_kind) => {
                self.errors.push(CompileError::BadSymbolKind {
                    name,
                    expected,
                    found: found_kind,
                    used_at,
                    declared_at: found.location(self.ast),
                });
            }
            None => {
                // The eqlog-side `accessible_symbol` predicate doesn't track
                // variable bindings (rule-body vars and named args), so it
                // would report this as undeclared rather than as a wrong
                // kind. Mirror that to avoid fabricating a SymbolKindCase
                // that doesn't exist for variables.
                self.errors
                    .push(CompileError::UndeclaredSymbol { name, used_at });
            }
        }
    }
}

fn symbol_kind_case(sym: Symbol) -> Option<SymbolKindCase> {
    Some(match sym {
        Symbol::Type(_) => SymbolKindCase::TypeSymbol(),
        Symbol::Pred(_) => SymbolKindCase::PredSymbol(),
        Symbol::Func(_) => SymbolKindCase::FuncSymbol(),
        Symbol::Enum(_) => SymbolKindCase::EnumSymbol(),
        Symbol::Ctor(_) => SymbolKindCase::CtorSymbol(),
        Symbol::Model(_) => SymbolKindCase::ModelSymbol(),
        Symbol::Rule(_) => SymbolKindCase::RuleSymbol(),
        Symbol::Arg(_) | Symbol::Var(_) => return None,
    })
}

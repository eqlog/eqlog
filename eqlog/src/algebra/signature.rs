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
//!    model. The same pass also registers the morphism operations that
//!    every model implies: the `dom`/`cod` projections (one [`Func`] each
//!    per model, on [`ModelIds`]) and the `mor_app` functions (one
//!    [`Func`] per member type, on
//!    [`Signature::mor_app_func_for_type`]). Produces lookups from AST
//!    decl ids to ids, exposed via [`Signature::type_for_type_decl`] and
//!    friends.
//! 2. Walk the AST again to register the user-declared [`Pred`]s and
//!    [`Func`]s. Type-name references in pred/func/ctor arg decls (and
//!    func result types) are resolved against the ambient
//!    [`crate::scopes::Scopes`] entry of the relevant AST node, then
//!    translated through the pass-1 lookups.
//!
//! Symbol-resolution failures (undeclared names, names that resolve to a
//! non-type symbol) are accumulated as [`CompileError`]s and returned
//! alongside the partial [`Signature`]. The caller is responsible for
//! merging them with errors from other passes.

use std::collections::BTreeMap;

use crate::ast::*;
use crate::error::{CompileError, SymbolKind};
use crate::grammar_util::Location;
use crate::scopes::{Scopes, Symbol};

#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct TypeId(usize);

#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct PredId(usize);

#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct FuncId(usize);

impl FuncId {
    pub fn as_usize(self) -> usize {
        self.0
    }
}

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

#[derive(Clone, Debug)]
pub struct Type {
    #[allow(dead_code)]
    pub kind: TypeKind,
    /// Enclosing model types, outermost first.
    pub parents: Vec<TypeId>,
}

#[derive(Clone, Debug)]
pub struct Pred {
    /// Enclosing model types, outermost first.
    pub parents: Vec<TypeId>,
    pub arity: Vec<TypeId>,
}

#[derive(Clone, Debug)]
pub struct Func {
    /// Enclosing model types, outermost first.
    pub parents: Vec<TypeId>,
    pub domain: Vec<TypeId>,
    #[allow(dead_code)]
    pub codomain: TypeId,
}

/// The ids a `model` declaration produces: the model type itself, its
/// auto-generated morphism-type companion, and the dom/cod projections
/// that read the source/target model instance from a morphism. The
/// morphism-application functions live separately on
/// [`Signature::mor_app_func`], with both type roles named explicitly.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub struct ModelIds {
    pub type_: TypeId,
    pub mor: TypeId,
    pub dom: FuncId,
    pub cod: FuncId,
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct MorphismMemberTypes {
    pub morphism_type: TypeId,
    pub member_type: TypeId,
}

impl MorphismMemberTypes {
    pub fn model_type(self, signature: &Signature) -> TypeId {
        match signature.type_(self.morphism_type).kind {
            TypeKind::Mor(model_type) => model_type,
            TypeKind::Plain | TypeKind::Model | TypeKind::Enum => {
                panic!("morphism application requires a morphism type")
            }
        }
    }
}

#[derive(Clone, Debug, Default)]
pub struct Signature {
    types: Vec<Type>,
    preds: Vec<Pred>,
    funcs: Vec<Func>,
    type_decls: BTreeMap<TypeDeclId, TypeId>,
    enum_decls: BTreeMap<EnumDeclId, TypeId>,
    model_decls: BTreeMap<ModelDeclId, ModelIds>,
    pred_decls: BTreeMap<PredDeclId, PredId>,
    func_decls: BTreeMap<FuncDeclId, FuncId>,
    const_decls: BTreeMap<ConstDeclId, FuncId>,
    ctor_decls: BTreeMap<CtorDeclId, FuncId>,
    /// Morphism-application functions keyed by a morphism type and a
    /// descendant member type. Each function takes `(Mor<M>, T)` and
    /// returns `T`, allowing the same morphism to act at every depth.
    mor_app_funcs: BTreeMap<MorphismMemberTypes, FuncId>,
}

impl Signature {
    pub fn type_(&self, id: TypeId) -> &Type {
        &self.types[id.0]
    }

    pub fn pred(&self, id: PredId) -> &Pred {
        &self.preds[id.0]
    }

    pub fn func(&self, id: FuncId) -> &Func {
        &self.funcs[id.0]
    }

    pub fn iter_funcs(&self) -> impl Iterator<Item = FuncId> + '_ {
        (0..self.funcs.len()).map(FuncId)
    }

    pub fn iter_preds(&self) -> impl Iterator<Item = PredId> + '_ {
        (0..self.preds.len()).map(PredId)
    }

    pub fn iter_types(&self) -> impl Iterator<Item = TypeId> + '_ {
        (0..self.types.len()).map(TypeId)
    }

    pub fn iter_type_decls(&self) -> impl Iterator<Item = (TypeDeclId, TypeId)> + '_ {
        self.type_decls.iter().map(|(&decl, &typ)| (decl, typ))
    }

    pub fn iter_enum_decls(&self) -> impl Iterator<Item = (EnumDeclId, TypeId)> + '_ {
        self.enum_decls.iter().map(|(&decl, &typ)| (decl, typ))
    }

    pub fn iter_model_decls(&self) -> impl Iterator<Item = (ModelDeclId, ModelIds)> + '_ {
        self.model_decls.iter().map(|(&decl, &ids)| (decl, ids))
    }

    pub fn iter_pred_decls(&self) -> impl Iterator<Item = (PredDeclId, PredId)> + '_ {
        self.pred_decls.iter().map(|(&decl, &pred)| (decl, pred))
    }

    pub fn iter_func_decls(&self) -> impl Iterator<Item = (FuncDeclId, FuncId)> + '_ {
        self.func_decls.iter().map(|(&decl, &func)| (decl, func))
    }

    pub fn iter_const_decls(&self) -> impl Iterator<Item = (ConstDeclId, FuncId)> + '_ {
        self.const_decls.iter().map(|(&decl, &func)| (decl, func))
    }

    pub fn iter_ctor_decls(&self) -> impl Iterator<Item = (CtorDeclId, FuncId)> + '_ {
        self.ctor_decls.iter().map(|(&decl, &func)| (decl, func))
    }

    pub fn iter_mor_app_funcs(&self) -> impl Iterator<Item = (MorphismMemberTypes, FuncId)> + '_ {
        self.mor_app_funcs
            .iter()
            .map(|(&types, &func)| (types, func))
    }

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

    pub fn ids_for_model_decl(&self, id: ModelDeclId) -> ModelIds {
        *self
            .model_decls
            .get(&id)
            .expect("model decl was not registered")
    }

    /// Inverse of [`Self::ids_for_model_decl`] on the model type itself.
    /// Returns the [`ModelDeclId`] whose model-instance type is `tid`, or
    /// `None` if `tid` is not a model-instance type.
    pub fn model_decl_for_type(&self, tid: TypeId) -> Option<ModelDeclId> {
        self.model_decls
            .iter()
            .find_map(|(d, ids)| (ids.type_ == tid).then_some(*d))
    }

    /// Returns the morphism-application function for `tid`, or `None`
    /// if `tid` is not a member type (i.e. its `parents` is empty).
    /// The returned function has signature `(Mor<M>, T) -> T`, where
    /// `M` is the innermost enclosing model and `T = tid`.
    pub fn mor_app_func_for_type(&self, tid: TypeId) -> Option<FuncId> {
        let parent = self.type_(tid).parents.last()?;
        let morphism_type = self.ids_for_model_type(*parent)?.mor;
        self.mor_app_func(MorphismMemberTypes {
            morphism_type,
            member_type: tid,
        })
    }

    pub fn mor_app_func(&self, types: MorphismMemberTypes) -> Option<FuncId> {
        self.mor_app_funcs.get(&types).copied()
    }

    /// Returns the morphism and member types for a generated action.
    pub fn types_for_mor_app_func(&self, fid: FuncId) -> Option<MorphismMemberTypes> {
        self.mor_app_funcs
            .iter()
            .find_map(|(types, f)| (*f == fid).then_some(*types))
    }

    pub fn type_for_mor_app_func(&self, fid: FuncId) -> Option<TypeId> {
        self.types_for_mor_app_func(fid)
            .map(|types| types.member_type)
    }

    /// Returns the [`ModelIds`] whose model-instance type is `tid`, or
    /// `None` if `tid` is not a model-instance type.
    pub fn ids_for_model_type(&self, tid: TypeId) -> Option<ModelIds> {
        self.model_decls
            .values()
            .find_map(|ids| (ids.type_ == tid).then_some(*ids))
    }

    /// Returns the [`PredId`] for `id`, or `None` if the pred decl is
    /// malformed (e.g. one of its arg types failed to resolve).
    pub fn pred_for_pred_decl(&self, id: PredDeclId) -> Option<PredId> {
        self.pred_decls.get(&id).copied()
    }

    /// Returns the [`FuncId`] for `id`, or `None` if the func decl is
    /// malformed.
    pub fn func_for_func_decl(&self, id: FuncDeclId) -> Option<FuncId> {
        self.func_decls.get(&id).copied()
    }

    /// Returns the [`FuncId`] for the constant `id`, or `None` if the
    /// constant declaration is malformed.
    pub fn func_for_const_decl(&self, id: ConstDeclId) -> Option<FuncId> {
        self.const_decls.get(&id).copied()
    }

    /// Returns the [`FuncId`] for the constructor `id`, or `None` if the
    /// constructor is malformed.
    pub fn func_for_ctor_decl(&self, id: CtorDeclId) -> Option<FuncId> {
        self.ctor_decls.get(&id).copied()
    }

    /// Inverse of [`Self::type_for_enum_decl`]. Returns the [`EnumDeclId`]
    /// whose registered type is `tid`, or `None` if `tid` is not an enum
    /// type.
    pub fn enum_decl_for_type(&self, tid: TypeId) -> Option<EnumDeclId> {
        self.enum_decls
            .iter()
            .find_map(|(d, t)| (*t == tid).then_some(*d))
    }

    /// Human-readable name for `tid`, suitable for diagnostic messages.
    /// Uses the AST to resolve the decl that introduced the type. Morphism
    /// companions are rendered as `Mor<ModelName>`; if the decl for `tid`
    /// cannot be found, returns `"?"`.
    pub fn type_name(&self, ast: &Ast, tid: TypeId) -> String {
        match self.type_(tid).kind {
            TypeKind::Plain => self
                .type_decls
                .iter()
                .find_map(|(d, t)| (*t == tid).then(|| ast.type_decl(*d).name.clone()))
                .unwrap_or_else(|| "?".into()),
            TypeKind::Enum => self
                .enum_decls
                .iter()
                .find_map(|(d, t)| (*t == tid).then(|| ast.enum_decl(*d).name.clone()))
                .unwrap_or_else(|| "?".into()),
            TypeKind::Model => self
                .model_decls
                .iter()
                .find_map(|(d, ids)| (ids.type_ == tid).then(|| ast.model_decl(*d).name.clone()))
                .unwrap_or_else(|| "?".into()),
            TypeKind::Mor(inner) => format!("Mor<{}>", self.type_name(ast, inner)),
        }
    }

    fn push_type(&mut self, t: Type) -> TypeId {
        let id = TypeId(self.types.len());
        self.types.push(t);
        id
    }

    fn push_pred(&mut self, p: Pred) -> PredId {
        let id = PredId(self.preds.len());
        self.preds.push(p);
        id
    }

    fn push_func(&mut self, f: Func) -> FuncId {
        let id = FuncId(self.funcs.len());
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
/// Member type expressions in arg-decl positions are silently skipped here
/// because [`crate::syntactic::check_syntactic`] already emits a
/// higher-priority [`CompileError::IllegalMemberTypeExprInArgDecl`] for them.
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
    /// declaration (plus the mor companion of each model) and the morphism
    /// operations (`dom`, `cod` per model and `mor_app` per member type),
    /// recording the AST-id to [`TypeId`] lookups on [`Signature`].
    fn populate_types(&mut self, decls: &[DeclId], parents: &[TypeId]) {
        for decl in decls {
            match *self.ast.decl(*decl) {
                Decl::Type(id) => {
                    let tid = self.push_member_type(TypeKind::Plain, parents);
                    self.signature.type_decls.insert(id, tid);
                }
                Decl::Enum(id) => {
                    let tid = self.push_member_type(TypeKind::Enum, parents);
                    self.signature.enum_decls.insert(id, tid);
                }
                Decl::Model(id) => {
                    let model_tid = self.push_member_type(TypeKind::Model, parents);
                    let mor_tid = self.push_member_type(TypeKind::Mor(model_tid), parents);
                    let dom = self.signature.push_func(Func {
                        parents: parents.to_vec(),
                        domain: vec![mor_tid],
                        codomain: model_tid,
                    });
                    let cod = self.signature.push_func(Func {
                        parents: parents.to_vec(),
                        domain: vec![mor_tid],
                        codomain: model_tid,
                    });
                    self.signature.model_decls.insert(
                        id,
                        ModelIds {
                            type_: model_tid,
                            mor: mor_tid,
                            dom,
                            cod,
                        },
                    );
                    let body = self.ast.model_decl(id).body.clone();
                    let mut new_parents = parents.to_vec();
                    new_parents.push(model_tid);
                    self.populate_types(&body, &new_parents);
                }
                Decl::Pred(_) | Decl::Func(_) | Decl::Const(_) | Decl::Rule(_) => {}
            }
        }
    }

    /// Pushes a [`Type`] with the given kind and parents and, when
    /// `parents` is non-empty (i.e. the type lives inside a model),
    /// registers the corresponding `mor_app` [`Func`] for it.
    fn push_member_type(&mut self, kind: TypeKind, parents: &[TypeId]) -> TypeId {
        let tid = self.signature.push_type(Type {
            kind,
            parents: parents.to_vec(),
        });
        for (parent_index, &parent_model) in parents.iter().enumerate() {
            let parent_mor = self
                .signature
                .model_decls
                .values()
                .find_map(|ids| (ids.type_ == parent_model).then_some(ids.mor))
                .expect("enclosing model registered before its body is walked");
            let fid = self.signature.push_func(Func {
                parents: parents[..parent_index].to_vec(),
                domain: vec![parent_mor, tid],
                codomain: tid,
            });
            self.signature.mor_app_funcs.insert(
                MorphismMemberTypes {
                    morphism_type: parent_mor,
                    member_type: tid,
                },
                fid,
            );
        }
        tid
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
                        let pid = self.signature.push_pred(Pred {
                            parents: parents.to_vec(),
                            arity,
                        });
                        self.signature.pred_decls.insert(id, pid);
                    }
                }
                Decl::Func(id) => {
                    let FuncDecl { args, result, .. } = *self.ast.func_decl(id);
                    let domain = self.resolve_arg_types(args);
                    let codomain = self.resolve_signature_type_expr(result);
                    if let (Some(domain), Some(codomain)) = (domain, codomain) {
                        let fid = self.signature.push_func(Func {
                            parents: parents.to_vec(),
                            domain,
                            codomain,
                        });
                        self.signature.func_decls.insert(id, fid);
                    }
                }
                Decl::Const(id) => {
                    let result = self.ast.const_decl(id).result;
                    if let Some(codomain) = self.resolve_signature_type_expr(result) {
                        let fid = self.signature.push_func(Func {
                            parents: parents.to_vec(),
                            domain: Vec::new(),
                            codomain,
                        });
                        self.signature.const_decls.insert(id, fid);
                    }
                }
                Decl::Enum(id) => {
                    let codomain = self.signature.type_for_enum_decl(id);
                    let ctors = self.ast.enum_decl(id).ctors.clone();
                    for ctor in ctors {
                        let args = self.ast.ctor_decl(ctor).args;
                        if let Some(domain) = self.resolve_arg_types(args) {
                            let fid = self.signature.push_func(Func {
                                parents: parents.to_vec(),
                                domain,
                                codomain,
                            });
                            self.signature.ctor_decls.insert(ctor, fid);
                        }
                    }
                }
                Decl::Model(id) => {
                    let model_tid = self.signature.ids_for_model_decl(id).type_;
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
                    Some(Symbol::Model(md)) => Some(self.signature.ids_for_model_decl(md).type_),
                    Some(other) => {
                        // Sig-position ambient accepts type, enum or model.
                        // Mirror eqlog.eql's `should_be_symbol_3(name, type_kind, enum_kind, model_kind, ...)`
                        // by reporting `type` as the primary expected kind.
                        self.emit_wrong_kind(name, other, SymbolKind::Type, used_at);
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
                    Some(Symbol::Model(md)) => Some(self.signature.ids_for_model_decl(md).mor),
                    Some(other) => {
                        // Mirrors eqlog.eql's `should_be_symbol(model_ty_ident, model_kind, ...)`
                        // for sig-position mor type expressions.
                        self.emit_wrong_kind(name, other, SymbolKind::Model, used_at);
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
        expected: SymbolKind,
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
                // kind. Mirror that to avoid fabricating a SymbolKind
                // that doesn't exist for variables.
                self.errors
                    .push(CompileError::UndeclaredSymbol { name, used_at });
            }
        }
    }
}

fn symbol_kind_case(sym: Symbol) -> Option<SymbolKind> {
    Some(match sym {
        Symbol::Type(_) => SymbolKind::Type,
        Symbol::Pred(_) => SymbolKind::Pred,
        Symbol::Func(_) => SymbolKind::Func,
        Symbol::Const(_) => SymbolKind::Const,
        Symbol::Enum(_) => SymbolKind::Enum,
        Symbol::Ctor(_) => SymbolKind::Ctor,
        Symbol::Model(_) => SymbolKind::Model,
        Symbol::Rule(_) => SymbolKind::Rule,
        Symbol::Arg(_) | Symbol::Var(_) => return None,
    })
}

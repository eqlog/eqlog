//! Dependent signatures: types, predicates and functions, parameterised by
//! enclosing model types.
//!
//! Following the AST conventions of the rest of the crate, ids ([`TypeId`],
//! [`PredId`], [`FuncId`]) are opaque indices into flat `Vec`s on
//! [`Signature`]. The data structs ([`Type`], [`Pred`], [`Func`]) hold the
//! algebraic shape only and carry no source-name information; downstream
//! callers needing names can keep their own side tables keyed by id.
//!
//! [`build_signature`] walks an [`Ast`] and produces the corresponding
//! [`Signature`]. It is currently unused; callers will appear when the new
//! algebra pipeline is wired in.

use std::collections::BTreeMap;

use crate::ast::*;

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

#[derive(Clone, Debug)]
pub struct Type {
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
    pub codomain: TypeId,
}

#[derive(Clone, Debug, Default)]
pub struct Signature {
    types: Vec<Type>,
    preds: Vec<Pred>,
    funcs: Vec<Func>,
}

impl Signature {
    pub fn type_(&self, id: TypeId) -> &Type {
        &self.types[id.0 as usize]
    }

    pub fn pred(&self, id: PredId) -> &Pred {
        &self.preds[id.0 as usize]
    }

    pub fn func(&self, id: FuncId) -> &Func {
        &self.funcs[id.0 as usize]
    }

    pub fn types(&self) -> impl Iterator<Item = (TypeId, &Type)> {
        self.types
            .iter()
            .enumerate()
            .map(|(i, t)| (TypeId(i as u32), t))
    }

    pub fn preds(&self) -> impl Iterator<Item = (PredId, &Pred)> {
        self.preds
            .iter()
            .enumerate()
            .map(|(i, p)| (PredId(i as u32), p))
    }

    pub fn funcs(&self) -> impl Iterator<Item = (FuncId, &Func)> {
        self.funcs
            .iter()
            .enumerate()
            .map(|(i, f)| (FuncId(i as u32), f))
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

/// Walks `ast` rooted at `module` and produces a [`Signature`] with one entry
/// per type, enum, model, predicate, function and constructor declaration.
/// Each model declaration also contributes an auto-generated `Mor` companion
/// type.
///
/// Assumes the AST has already passed [`crate::syntactic`] (member type
/// expressions are not allowed in signature positions) and that every type
/// name referenced from a signature resolves in the surrounding model /
/// module chain. Violations panic.
pub fn build_signature(ast: &Ast, module: ModuleId) -> Signature {
    let mut builder = Builder {
        signature: Signature::default(),
        scopes: Vec::new(),
        mor_types: BTreeMap::new(),
    };
    let decls = ast.module(module).decls.clone();
    builder.walk_scope(ast, &decls, &[]);
    builder.signature
}

struct Builder {
    signature: Signature,
    /// Stack of `name -> TypeId` maps, one per active model body (innermost
    /// last); the bottom is the module level. Lookup walks outward.
    scopes: Vec<BTreeMap<String, TypeId>>,
    /// Mor companion type for each model type. Populated as model types are
    /// registered.
    mor_types: BTreeMap<TypeId, TypeId>,
}

impl Builder {
    fn walk_scope(&mut self, ast: &Ast, decls: &[DeclId], parents: &[TypeId]) {
        self.scopes.push(BTreeMap::new());

        // Phase 1: register every type declared at this scope, including the
        // mor companion of each model. Forward references within a scope are
        // legal, so all type names must be known before pred/func arities can
        // be resolved.
        let mut models: Vec<(ModelDeclId, TypeId)> = Vec::new();
        for decl in decls {
            match *ast.decl(*decl) {
                Decl::Type(id) => {
                    let name = ast.type_decl(id).name.clone();
                    let tid = self.signature.push_type(Type {
                        kind: TypeKind::Plain,
                        parents: parents.to_vec(),
                    });
                    self.bind_type(name, tid);
                }
                Decl::Enum(id) => {
                    let name = ast.enum_decl(id).name.clone();
                    let tid = self.signature.push_type(Type {
                        kind: TypeKind::Enum,
                        parents: parents.to_vec(),
                    });
                    self.bind_type(name, tid);
                }
                Decl::Model(id) => {
                    let name = ast.model_decl(id).name.clone();
                    let tid = self.signature.push_type(Type {
                        kind: TypeKind::Model,
                        parents: parents.to_vec(),
                    });
                    self.bind_type(name, tid);
                    let mor_tid = self.signature.push_type(Type {
                        kind: TypeKind::Mor(tid),
                        parents: parents.to_vec(),
                    });
                    self.mor_types.insert(tid, mor_tid);
                    models.push((id, tid));
                }
                Decl::Pred(_) | Decl::Func(_) | Decl::Rule(_) => {}
            }
        }

        // Phase 2: register pred/func/ctor at this scope.
        for decl in decls {
            match *ast.decl(*decl) {
                Decl::Pred(id) => {
                    let args = ast.pred_decl(id).args;
                    let arity = self.resolve_arg_types(ast, args);
                    self.signature.push_pred(Pred {
                        parents: parents.to_vec(),
                        arity,
                    });
                }
                Decl::Func(id) => {
                    let FuncDecl { args, result, .. } = *ast.func_decl(id);
                    let domain = self.resolve_arg_types(ast, args);
                    let codomain = self.resolve_signature_type_expr(ast, result);
                    self.signature.push_func(Func {
                        parents: parents.to_vec(),
                        domain,
                        codomain,
                    });
                }
                Decl::Enum(id) => {
                    let enum_name = ast.enum_decl(id).name.clone();
                    let enum_tid = self
                        .lookup_type(&enum_name)
                        .expect("enum type was registered in phase 1");
                    let ctors = ast.enum_decl(id).ctors.clone();
                    for ctor in ctors {
                        let ctor_args = ast.ctor_decl(ctor).args;
                        let domain = self.resolve_arg_types(ast, ctor_args);
                        self.signature.push_func(Func {
                            parents: parents.to_vec(),
                            domain,
                            codomain: enum_tid,
                        });
                    }
                }
                Decl::Type(_) | Decl::Model(_) | Decl::Rule(_) => {}
            }
        }

        // Phase 3: recurse into model bodies with the model added to the
        // parent chain.
        for (model_id, model_tid) in models {
            let body = ast.model_decl(model_id).body.clone();
            let mut new_parents = parents.to_vec();
            new_parents.push(model_tid);
            self.walk_scope(ast, &body, &new_parents);
        }

        self.scopes.pop();
    }

    fn bind_type(&mut self, name: String, tid: TypeId) {
        self.scopes.last_mut().unwrap().insert(name, tid);
    }

    fn lookup_type(&self, name: &str) -> Option<TypeId> {
        for scope in self.scopes.iter().rev() {
            if let Some(&tid) = scope.get(name) {
                return Some(tid);
            }
        }
        None
    }

    fn resolve_arg_types(&self, ast: &Ast, args: ArgDeclListId) -> Vec<TypeId> {
        ast.arg_decl_list(args)
            .args
            .iter()
            .map(|&arg| {
                let typ_expr = ast.arg_decl(arg).typ;
                self.resolve_signature_type_expr(ast, typ_expr)
            })
            .collect()
    }

    fn resolve_signature_type_expr(&self, ast: &Ast, type_expr: TypeExprId) -> TypeId {
        match *ast.type_expr(type_expr) {
            TypeExpr::Ambient(id) => {
                let name = &ast.ambient_type_expr(id).name;
                self.lookup_type(name)
                    .unwrap_or_else(|| panic!("unresolved type name `{name}`"))
            }
            TypeExpr::Mor(id) => {
                let name = &ast.mor_type_expr(id).name;
                let model_tid = self
                    .lookup_type(name)
                    .unwrap_or_else(|| panic!("unresolved model name `{name}`"));
                *self
                    .mor_types
                    .get(&model_tid)
                    .expect("mor companion was registered with the model")
            }
            TypeExpr::Member(_) => {
                panic!("member type expression in signature position");
            }
        }
    }
}

use std::collections::BTreeMap;

use eqlog_eqlog::{
    EnumDeclNode, Eqlog, Func, FuncDeclNode, ModelDeclNode, Pred, PredDeclNode, Rel, RelCase,
    SymbolScope, Type, TypeDeclNode,
};

use crate::algebra::signature::{FuncId, PredId, Signature, TypeId};
use crate::ast::{CtorDeclId, EnumDeclId, FuncDeclId, ModelDeclId, PredDeclId, TypeDeclId};
use crate::ast_to_eqlog::EqlogAstMaps;
use crate::flat_eqlog::{FlatInRel, FlatRel};

/// Maps local algebra ids to ids in the generated Eqlog metadata.
///
/// `Signature` ids are local to the algebra pass. The Rust generator consumes
/// generated Eqlog ids for types, predicates, functions, and relations. This
/// helper keeps that translation in one place.
pub(crate) struct EqlogIds<'a> {
    eqlog: &'a Eqlog,
    signature: &'a Signature,
    types: BTreeMap<TypeId, Type>,
    preds: BTreeMap<PredId, Pred>,
    funcs: BTreeMap<FuncId, Func>,
}

impl<'a> EqlogIds<'a> {
    pub(crate) fn new(eqlog: &'a Eqlog, signature: &'a Signature, maps: &EqlogAstMaps) -> Self {
        let mut types = BTreeMap::new();
        for (decl, typ) in signature.iter_type_decls() {
            types.insert(typ, eqlog_type_decl_type(eqlog, maps, decl));
        }
        for (decl, typ) in signature.iter_enum_decls() {
            types.insert(typ, eqlog_enum_decl_type(eqlog, maps, decl));
        }
        for (decl, ids) in signature.iter_model_decls() {
            let model_type = eqlog_model_decl_type(eqlog, maps, decl);
            let mor_type = eqlog
                .mor_type(model_type)
                .expect("Eqlog metadata should define model morphism type");
            types.insert(ids.type_, model_type);
            types.insert(ids.mor, mor_type);
        }

        let mut preds = BTreeMap::new();
        for (decl, pred) in signature.iter_pred_decls() {
            preds.insert(pred, eqlog_pred_decl_pred(eqlog, maps, decl));
        }

        let mut funcs = BTreeMap::new();
        for (decl, func) in signature.iter_func_decls() {
            funcs.insert(func, eqlog_func_decl_func(eqlog, maps, decl));
        }
        for (decl, func) in signature.iter_ctor_decls() {
            funcs.insert(func, eqlog_ctor_decl_func(eqlog, maps, decl));
        }
        for (_decl, ids) in signature.iter_model_decls() {
            let mor_type = types[&ids.mor];
            funcs.insert(
                ids.dom,
                eqlog
                    .mor_type_dom_func(mor_type)
                    .expect("Eqlog metadata should define dom function"),
            );
            funcs.insert(
                ids.cod,
                eqlog
                    .mor_type_cod_func(mor_type)
                    .expect("Eqlog metadata should define cod function"),
            );
        }
        for (member_type, func) in signature.iter_mor_app_funcs() {
            funcs.insert(
                func,
                eqlog
                    .mor_app_func(types[&member_type])
                    .expect("Eqlog metadata should define morphism application function"),
            );
        }

        Self {
            eqlog,
            signature,
            types,
            preds,
            funcs,
        }
    }

    pub(crate) fn eqlog(&self) -> &Eqlog {
        self.eqlog
    }

    pub(crate) fn signature(&self) -> &Signature {
        self.signature
    }

    pub(crate) fn typ(&self, typ: TypeId) -> Type {
        self.types[&typ]
    }

    pub(crate) fn pred(&self, pred: PredId) -> Pred {
        self.preds[&pred]
    }

    pub(crate) fn func(&self, func: FuncId) -> Func {
        self.funcs[&func]
    }

    pub(crate) fn type_id(&self, typ: Type) -> Option<TypeId> {
        self.types
            .iter()
            .find_map(|(&type_id, &typ0)| self.eqlog.are_equal_type(typ0, typ).then_some(type_id))
    }

    pub(crate) fn pred_id(&self, pred: Pred) -> Option<PredId> {
        self.preds.iter().find_map(|(&pred_id, &pred0)| {
            self.eqlog.are_equal_pred(pred0, pred).then_some(pred_id)
        })
    }

    pub(crate) fn func_id(&self, func: Func) -> Option<FuncId> {
        self.funcs.iter().find_map(|(&func_id, &func0)| {
            self.eqlog.are_equal_func(func0, func).then_some(func_id)
        })
    }

    pub(crate) fn pred_rel(&self, pred: PredId) -> Rel {
        self.eqlog
            .pred_rel(self.pred(pred))
            .expect("Eqlog metadata should define predicate relation")
    }

    pub(crate) fn func_rel(&self, func: FuncId) -> Rel {
        self.eqlog
            .func_rel(self.func(func))
            .expect("Eqlog metadata should define function relation")
    }

    pub(crate) fn model_member_rel(&self, member_type: TypeId) -> Rel {
        let pred = self
            .eqlog
            .model_member_pred(self.typ(member_type))
            .expect("Eqlog metadata should define model member predicate");
        self.eqlog
            .pred_rel(pred)
            .expect("Eqlog metadata should define model member relation")
    }

    pub(crate) fn is_model_member_rel(&self, rel: Rel) -> bool {
        self.eqlog.iter_model_member_pred().any(|(_, member_pred)| {
            let member_rel = self
                .eqlog
                .pred_rel(member_pred)
                .expect("model member predicate should have relation");
            self.eqlog.are_equal_rel(member_rel, rel)
        })
    }

    pub(crate) fn flat_rel(&self, rel: FlatRel) -> Rel {
        match rel {
            FlatRel::Pred(pred) => self.pred_rel(pred),
            FlatRel::Func(func) => self.func_rel(func),
            FlatRel::ModelMember(member_type) => self.model_member_rel(member_type),
        }
    }

    pub(crate) fn rel_id(&self, rel: Rel) -> Option<FlatRel> {
        match self.eqlog.rel_case(rel) {
            RelCase::PredRel(pred) => {
                if self.is_model_member_rel(rel) {
                    self.eqlog
                        .iter_model_member_pred()
                        .find_map(|(typ, pred0)| {
                            self.eqlog
                                .are_equal_pred(pred0, pred)
                                .then(|| self.type_id(typ).map(FlatRel::ModelMember))
                        })
                        .flatten()
                } else {
                    self.pred_id(pred).map(FlatRel::Pred)
                }
            }
            RelCase::FuncRel(func) => self.func_id(func).map(FlatRel::Func),
        }
    }

    pub(crate) fn flat_in_rel(&self, rel: Rel) -> Option<FlatInRel> {
        self.rel_id(rel).map(FlatInRel::Rel)
    }

    pub(crate) fn type_set(&self, typ: Type) -> Option<FlatInRel> {
        self.type_id(typ).map(FlatInRel::TypeSet)
    }
}

fn eqlog_type_decl_type(eqlog: &Eqlog, maps: &EqlogAstMaps, decl: TypeDeclId) -> Type {
    let node = maps.type_decl_nodes[&decl];
    let ident = eqlog
        .iter_type_decl()
        .find_map(|(node0, ident)| eqlog.are_equal_type_decl_node(node0, node).then_some(ident))
        .expect("type declaration node should be populated in Eqlog metadata");
    let scope = decl_scope_for_type_decl(eqlog, node);
    eqlog
        .semantic_type(scope, ident)
        .expect("type declaration should have semantic type")
}

fn eqlog_enum_decl_type(eqlog: &Eqlog, maps: &EqlogAstMaps, decl: EnumDeclId) -> Type {
    let node = maps.enum_decl_nodes[&decl];
    let ident = eqlog
        .iter_enum_decl()
        .find_map(|(node0, ident, _)| eqlog.are_equal_enum_decl_node(node0, node).then_some(ident))
        .expect("enum declaration node should be populated in Eqlog metadata");
    let scope = decl_scope_for_enum_decl(eqlog, node);
    eqlog
        .semantic_type(scope, ident)
        .expect("enum declaration should have semantic type")
}

fn eqlog_model_decl_type(eqlog: &Eqlog, maps: &EqlogAstMaps, decl: ModelDeclId) -> Type {
    let node = maps.model_decl_nodes[&decl];
    let ident = eqlog
        .iter_model_decl()
        .find_map(|(node0, ident, _)| {
            eqlog
                .are_equal_model_decl_node(node0, node)
                .then_some(ident)
        })
        .expect("model declaration node should be populated in Eqlog metadata");
    let scope = decl_scope_for_model_decl(eqlog, node);
    eqlog
        .semantic_type(scope, ident)
        .expect("model declaration should have semantic type")
}

fn eqlog_pred_decl_pred(eqlog: &Eqlog, maps: &EqlogAstMaps, decl: PredDeclId) -> Pred {
    let node = maps.pred_decl_nodes[&decl];
    let ident = eqlog
        .iter_pred_decl()
        .find_map(|(node0, ident, _)| eqlog.are_equal_pred_decl_node(node0, node).then_some(ident))
        .expect("predicate declaration node should be populated in Eqlog metadata");
    let scope = decl_scope_for_pred_decl(eqlog, node);
    eqlog
        .semantic_pred(scope, ident)
        .expect("predicate declaration should have semantic predicate")
}

fn eqlog_func_decl_func(eqlog: &Eqlog, maps: &EqlogAstMaps, decl: FuncDeclId) -> Func {
    let node = maps.func_decl_nodes[&decl];
    let ident = eqlog
        .iter_func_decl()
        .find_map(|(node0, ident, _, _)| {
            eqlog.are_equal_func_decl_node(node0, node).then_some(ident)
        })
        .expect("function declaration node should be populated in Eqlog metadata");
    let scope = decl_scope_for_func_decl(eqlog, node);
    eqlog
        .semantic_func(scope, ident)
        .expect("function declaration should have semantic function")
}

fn eqlog_ctor_decl_func(eqlog: &Eqlog, maps: &EqlogAstMaps, decl: CtorDeclId) -> Func {
    let node = maps.ctor_decl_nodes[&decl];
    let ident = eqlog
        .iter_ctor_decl()
        .find_map(|(node0, ident, _)| eqlog.are_equal_ctor_decl_node(node0, node).then_some(ident))
        .expect("constructor declaration node should be populated in Eqlog metadata");
    let scope = eqlog
        .ctor_symbol_scope(node)
        .expect("constructor declaration should have symbol scope");
    eqlog
        .semantic_func(scope, ident)
        .expect("constructor declaration should have semantic function")
}

fn decl_scope_for_type_decl(eqlog: &Eqlog, node: TypeDeclNode) -> SymbolScope {
    let decl = eqlog
        .iter_decl_node_type()
        .find_map(|(decl, node0)| eqlog.are_equal_type_decl_node(node0, node).then_some(decl))
        .expect("type declaration should have parent declaration node");
    eqlog
        .decl_symbol_scope(decl)
        .expect("declaration node should have symbol scope")
}

fn decl_scope_for_pred_decl(eqlog: &Eqlog, node: PredDeclNode) -> SymbolScope {
    let decl = eqlog
        .iter_decl_node_pred()
        .find_map(|(decl, node0)| eqlog.are_equal_pred_decl_node(node0, node).then_some(decl))
        .expect("predicate declaration should have parent declaration node");
    eqlog
        .decl_symbol_scope(decl)
        .expect("declaration node should have symbol scope")
}

fn decl_scope_for_func_decl(eqlog: &Eqlog, node: FuncDeclNode) -> SymbolScope {
    let decl = eqlog
        .iter_decl_node_func()
        .find_map(|(decl, node0)| eqlog.are_equal_func_decl_node(node0, node).then_some(decl))
        .expect("function declaration should have parent declaration node");
    eqlog
        .decl_symbol_scope(decl)
        .expect("declaration node should have symbol scope")
}

fn decl_scope_for_enum_decl(eqlog: &Eqlog, node: EnumDeclNode) -> SymbolScope {
    let decl = eqlog
        .iter_decl_node_enum()
        .find_map(|(decl, node0)| eqlog.are_equal_enum_decl_node(node0, node).then_some(decl))
        .expect("enum declaration should have parent declaration node");
    eqlog
        .decl_symbol_scope(decl)
        .expect("declaration node should have symbol scope")
}

fn decl_scope_for_model_decl(eqlog: &Eqlog, node: ModelDeclNode) -> SymbolScope {
    let decl = eqlog
        .iter_decl_node_model()
        .find_map(|(decl, node0)| eqlog.are_equal_model_decl_node(node0, node).then_some(decl))
        .expect("model declaration should have parent declaration node");
    eqlog
        .decl_symbol_scope(decl)
        .expect("declaration node should have symbol scope")
}

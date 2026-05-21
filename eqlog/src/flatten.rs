use std::collections::{BTreeMap, BTreeSet};
use std::sync::Arc;

use convert_case::{Case::Snake, Casing as _};
use eqlog_eqlog::{Eqlog, Func, Ident, Pred, Rel, SymbolScope, Type};

use crate::algebra::populate::{MorphismKind, RuleStructures};
use crate::algebra::signature::{FuncId, PredId, Signature, TypeId};
use crate::algebra::structure::{ConcreteType, ElId, FuncApp, PredApp, Structure, StructureId};
use crate::ast::*;
use crate::ast_to_eqlog::EqlogAstMaps;
use crate::eqlog_util::display_rel;
use crate::flat_eqlog::*;

type FlatElKey = (StructureId, ElId);

pub(crate) struct FlattenCtx<'a> {
    ast: &'a Ast,
    module: ModuleId,
    signature: &'a Signature,
    rule_structures: &'a BTreeMap<RuleDeclId, RuleStructures>,
    /// Eqlog-backed facts currently consumed by flat lowering and index selection.
    eqlog: &'a Eqlog,
    eqlog_ast_maps: &'a EqlogAstMaps,
    identifiers: &'a BTreeMap<Ident, String>,
}

impl<'a> FlattenCtx<'a> {
    pub(crate) fn new(
        ast: &'a Ast,
        module: ModuleId,
        signature: &'a Signature,
        rule_structures: &'a BTreeMap<RuleDeclId, RuleStructures>,
        eqlog: &'a Eqlog,
        eqlog_ast_maps: &'a EqlogAstMaps,
        identifiers: &'a BTreeMap<Ident, String>,
    ) -> Self {
        Self {
            ast,
            module,
            signature,
            rule_structures,
            eqlog,
            eqlog_ast_maps,
            identifiers,
        }
    }

    pub(crate) fn eqlog(&self) -> &Eqlog {
        self.eqlog
    }
}

#[derive(Clone, Debug)]
struct RuleMorphism {
    src: StructureId,
    tgt: StructureId,
    kind: MorphismKind,
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
struct FlatRelApp {
    rel: Rel,
    args: Vec<ElId>,
}

struct EqlogBridge<'a> {
    eqlog: &'a Eqlog,
    types: BTreeMap<TypeId, Type>,
    preds: BTreeMap<PredId, Pred>,
    funcs: BTreeMap<FuncId, Func>,
}

impl<'a> EqlogBridge<'a> {
    fn new(ctx: &'a FlattenCtx<'_>) -> Self {
        let eqlog = ctx.eqlog;
        let signature = ctx.signature;
        let maps = ctx.eqlog_ast_maps;
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
            types,
            preds,
            funcs,
        }
    }

    fn typ(&self, typ: TypeId) -> Type {
        self.types[&typ]
    }

    fn func(&self, func: FuncId) -> Func {
        self.funcs[&func]
    }

    fn pred_rel(&self, pred: PredId) -> Rel {
        self.eqlog
            .pred_rel(self.preds[&pred])
            .expect("Eqlog metadata should define predicate relation")
    }

    fn func_rel(&self, func: FuncId) -> Rel {
        self.eqlog
            .func_rel(self.func(func))
            .expect("Eqlog metadata should define function relation")
    }

    fn model_member_rel(&self, member_type: TypeId) -> Rel {
        let pred = self
            .eqlog
            .model_member_pred(self.typ(member_type))
            .expect("Eqlog metadata should define model member predicate");
        self.eqlog
            .pred_rel(pred)
            .expect("Eqlog metadata should define model member relation")
    }

    fn is_model_member_rel(&self, rel: Rel) -> bool {
        self.eqlog.iter_model_member_pred().any(|(_, member_pred)| {
            let member_rel = self
                .eqlog
                .pred_rel(member_pred)
                .expect("model member predicate should have relation");
            self.eqlog.are_equal_rel(member_rel, rel)
        })
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

fn decl_scope_for_type_decl(eqlog: &Eqlog, node: eqlog_eqlog::TypeDeclNode) -> SymbolScope {
    let decl = eqlog
        .iter_decl_node_type()
        .find_map(|(decl, node0)| eqlog.are_equal_type_decl_node(node0, node).then_some(decl))
        .expect("type declaration should have parent declaration node");
    eqlog
        .decl_symbol_scope(decl)
        .expect("declaration node should have symbol scope")
}

fn decl_scope_for_pred_decl(eqlog: &Eqlog, node: eqlog_eqlog::PredDeclNode) -> SymbolScope {
    let decl = eqlog
        .iter_decl_node_pred()
        .find_map(|(decl, node0)| eqlog.are_equal_pred_decl_node(node0, node).then_some(decl))
        .expect("predicate declaration should have parent declaration node");
    eqlog
        .decl_symbol_scope(decl)
        .expect("declaration node should have symbol scope")
}

fn decl_scope_for_func_decl(eqlog: &Eqlog, node: eqlog_eqlog::FuncDeclNode) -> SymbolScope {
    let decl = eqlog
        .iter_decl_node_func()
        .find_map(|(decl, node0)| eqlog.are_equal_func_decl_node(node0, node).then_some(decl))
        .expect("function declaration should have parent declaration node");
    eqlog
        .decl_symbol_scope(decl)
        .expect("declaration node should have symbol scope")
}

fn decl_scope_for_enum_decl(eqlog: &Eqlog, node: eqlog_eqlog::EnumDeclNode) -> SymbolScope {
    let decl = eqlog
        .iter_decl_node_enum()
        .find_map(|(decl, node0)| eqlog.are_equal_enum_decl_node(node0, node).then_some(decl))
        .expect("enum declaration should have parent declaration node");
    eqlog
        .decl_symbol_scope(decl)
        .expect("declaration node should have symbol scope")
}

fn decl_scope_for_model_decl(eqlog: &Eqlog, node: eqlog_eqlog::ModelDeclNode) -> SymbolScope {
    let decl = eqlog
        .iter_decl_node_model()
        .find_map(|(decl, node0)| eqlog.are_equal_model_decl_node(node0, node).then_some(decl))
        .expect("model declaration should have parent declaration node");
    eqlog
        .decl_symbol_scope(decl)
        .expect("declaration node should have symbol scope")
}

fn flatten_morphisms(rule: &RuleStructures) -> Vec<RuleMorphism> {
    let mut morphisms = rule.morphism_kinds.clone();

    for &target in rule.branch_block_starts.values() {
        let source = incoming_source(rule, target);
        morphisms
            .entry((source, target))
            .or_insert(MorphismKind::Noop);
    }
    for &target in rule.match_after_scrutinee.values() {
        let source = incoming_source(rule, target);
        morphisms
            .entry((source, target))
            .or_insert(MorphismKind::If);
    }
    for &target in rule.match_case_starts.values() {
        let source = incoming_source(rule, target);
        morphisms
            .entry((source, target))
            .or_insert(MorphismKind::If);
    }

    let mut result: Vec<RuleMorphism> = morphisms
        .into_iter()
        .map(|((src, tgt), kind)| RuleMorphism { src, tgt, kind })
        .collect();
    result.sort_by_key(|m| (m.tgt, m.src));
    result
}

fn incoming_source(rule: &RuleStructures, target: StructureId) -> StructureId {
    rule.cat
        .morphisms
        .keys()
        .find_map(|&(src, tgt)| (tgt == target).then_some(src))
        .expect("auxiliary structure should have an incoming morphism")
}

/// Assigns compatible [FlatVar]s to elements in morphism codomains.
///
/// If a morphism maps an already-assigned source element to a target element,
/// the target reuses that variable. Remaining target elements receive fresh
/// variables.
fn assign_el_vars(
    ctx: &FlattenCtx<'_>,
    rule: &RuleStructures,
    morphisms: &[RuleMorphism],
    bridge: &EqlogBridge<'_>,
) -> BTreeMap<FlatElKey, FlatVar> {
    let mut el_vars: BTreeMap<FlatElKey, FlatVar> = BTreeMap::new();
    let mut available_vars = 0..;

    assign_structure_el_vars(
        ctx,
        rule,
        StructureId(0),
        bridge,
        &mut el_vars,
        &mut available_vars,
    );

    for morphism in morphisms {
        let src_st = &rule.cat.structures[morphism.src.0];
        let tgt_st = &rule.cat.structures[morphism.tgt.0];
        let elmap = rule
            .cat
            .morphisms
            .get(&(morphism.src, morphism.tgt))
            .expect("flattened morphism should exist");

        for (&preimage, &image) in elmap {
            let preimage = src_st.unification.root_const(preimage);
            let image = tgt_st.unification.root_const(image);
            if let Some(var) = el_vars.get(&(morphism.src, preimage)).cloned() {
                el_vars.insert((morphism.tgt, image), var);
            }
        }

        assign_structure_el_vars(
            ctx,
            rule,
            morphism.tgt,
            bridge,
            &mut el_vars,
            &mut available_vars,
        );
    }

    el_vars
}

fn assign_structure_el_vars(
    ctx: &FlattenCtx<'_>,
    rule: &RuleStructures,
    structure: StructureId,
    bridge: &EqlogBridge<'_>,
    el_vars: &mut BTreeMap<FlatElKey, FlatVar>,
    available_vars: &mut impl Iterator<Item = usize>,
) {
    let st = &rule.cat.structures[structure.0];
    for &el in st.els.keys() {
        let el = st.unification.root_const(el);
        el_vars.entry((structure, el)).or_insert_with(|| {
            let typ = bridge.typ(concrete_type_of(rule, structure, el).typ);
            let base_name = el_base_name(ctx, rule, structure, el);
            let name: Arc<str> = format!("{base_name}{}", available_vars.next().unwrap()).into();
            FlatVar { name, typ }
        });
    }
}

fn el_base_name(
    ctx: &FlattenCtx<'_>,
    rule: &RuleStructures,
    structure: StructureId,
    el: ElId,
) -> String {
    let st = &rule.cat.structures[structure.0];
    let root = st.unification.root_const(el);
    if let Some(name) = st.var_els.iter().find_map(|(name, &var_el)| {
        (st.unification.root_const(var_el) == root).then(|| name.clone())
    }) {
        return name;
    }

    rule.semantic_els[structure.0]
        .iter()
        .find_map(|(&term, &term_el)| {
            if st.unification.root_const(term_el) != root {
                return None;
            }
            match *ctx.ast.term(term) {
                Term::Var(var) => Some(ctx.ast.var_term(var).name.clone()),
                Term::Wildcard | Term::App(_) | Term::Dom(_) | Term::Cod(_) | Term::MorApp(_) => {
                    None
                }
            }
        })
        .unwrap_or_else(|| "el".into())
}

fn concrete_type_of(rule: &RuleStructures, structure: StructureId, el: ElId) -> ConcreteType {
    let st = &rule.cat.structures[structure.0];
    let root = st.unification.root_const(el);
    let types = st
        .els
        .get(&root)
        .expect("flattening requires every element to have a type");
    let mut types = types.iter();
    let concrete_type = types
        .next()
        .cloned()
        .expect("flattening requires every element to have a type");
    assert!(
        types.next().is_none(),
        "flattening requires every element to have a unique concrete type"
    );
    concrete_type
}

fn flat_rel_apps(
    rule: &RuleStructures,
    structure: StructureId,
    bridge: &EqlogBridge<'_>,
) -> BTreeSet<FlatRelApp> {
    let st = &rule.cat.structures[structure.0];
    let mut apps = BTreeSet::new();

    for app in &st.pred_apps {
        let rel = bridge.pred_rel(app.pred);
        let args = flat_pred_args(st, app);
        apps.insert(FlatRelApp { rel, args });
    }

    for (app, &result) in &st.func_apps {
        let rel = bridge.func_rel(app.func);
        let mut args = flat_func_domain_args(st, app);
        args.push(flat_el(st, result));
        apps.insert(FlatRelApp { rel, args });
    }

    for &el in st.els.keys() {
        let el = flat_el(st, el);
        let concrete_type = concrete_type_of(rule, structure, el);
        let Some(&parent) = concrete_type.parents.last() else {
            // Parentless types are lowered through their type sets, not
            // through model-member relations.
            continue;
        };
        let rel = bridge.model_member_rel(concrete_type.typ);
        let args = vec![flat_el(st, parent), el];
        apps.insert(FlatRelApp { rel, args });
    }

    for app in &apps {
        assert_eq!(
            app.args.len(),
            app.rel_arity_len(bridge),
            "lowered relation app should match Eqlog metadata arity"
        );
    }

    apps
}

impl FlatRelApp {
    fn rel_arity_len(&self, bridge: &EqlogBridge<'_>) -> usize {
        crate::eqlog_util::type_list_vec(
            bridge
                .eqlog
                .arity(self.rel)
                .expect("Eqlog metadata should define relation arity"),
            bridge.eqlog,
        )
        .len()
    }
}

fn flat_pred_args(st: &Structure, app: &PredApp) -> Vec<ElId> {
    flat_args(st, &app.parents, &app.args)
}

fn flat_func_domain_args(st: &Structure, app: &FuncApp) -> Vec<ElId> {
    flat_args(st, &app.parents, &app.args)
}

fn flat_args(st: &Structure, parents: &[ElId], args: &[ElId]) -> Vec<ElId> {
    let mut flat_args = Vec::with_capacity(args.len() + usize::from(!parents.is_empty()));
    if let Some(&parent) = parents.last() {
        flat_args.push(flat_el(st, parent));
    }
    flat_args.extend(args.iter().map(|&arg| flat_el(st, arg)));
    flat_args
}

fn flat_el(st: &Structure, el: ElId) -> ElId {
    assert_eq!(
        st.unification.root_const(el),
        el,
        "flattening requires closed structures to store canonical elements"
    );
    el
}

fn constrained_els(st: &Structure) -> BTreeSet<ElId> {
    let mut constrained = BTreeSet::new();
    for app in &st.pred_apps {
        constrained.extend(app.args.iter().map(|&arg| st.unification.root_const(arg)));
    }
    for (app, &result) in &st.func_apps {
        constrained.extend(app.args.iter().map(|&arg| st.unification.root_const(arg)));
        constrained.insert(st.unification.root_const(result));
    }
    constrained
}

fn image_els(rule: &RuleStructures, morphism: &RuleMorphism) -> BTreeSet<ElId> {
    let tgt_st = &rule.cat.structures[morphism.tgt.0];
    rule.cat.morphisms[&(morphism.src, morphism.tgt)]
        .values()
        .map(|&image| tgt_st.unification.root_const(image))
        .collect()
}

fn mapped_rel_apps(
    rule: &RuleStructures,
    morphism: &RuleMorphism,
    bridge: &EqlogBridge<'_>,
) -> BTreeSet<FlatRelApp> {
    let src_apps = flat_rel_apps(rule, morphism.src, bridge);
    let src_st = &rule.cat.structures[morphism.src.0];
    let tgt_st = &rule.cat.structures[morphism.tgt.0];
    let map = &rule.cat.morphisms[&(morphism.src, morphism.tgt)];

    src_apps
        .into_iter()
        .map(|app| {
            let args = app
                .args
                .into_iter()
                .map(|arg| {
                    let arg = src_st.unification.root_const(arg);
                    let image = map
                        .get(&arg)
                        .copied()
                        .expect("morphism should be defined on relation arguments");
                    tgt_st.unification.root_const(image)
                })
                .collect();
            FlatRelApp { rel: app.rel, args }
        })
        .collect()
}

fn kernel_pairs(rule: &RuleStructures, morphism: &RuleMorphism) -> Vec<(ElId, ElId)> {
    let src_st = &rule.cat.structures[morphism.src.0];
    let tgt_st = &rule.cat.structures[morphism.tgt.0];
    let mut fibers: BTreeMap<ElId, BTreeSet<ElId>> = BTreeMap::new();
    for (&src, &tgt) in &rule.cat.morphisms[&(morphism.src, morphism.tgt)] {
        fibers
            .entry(tgt_st.unification.root_const(tgt))
            .or_default()
            .insert(src_st.unification.root_const(src));
    }

    let mut pairs = Vec::new();
    for fiber in fibers.values() {
        let els: Vec<ElId> = fiber.iter().copied().collect();
        for i in 0..els.len() {
            for j in i + 1..els.len() {
                pairs.push((els[i], els[j]));
            }
        }
    }
    pairs
}

/// Returns if statements matching the delta of `morphism` with arbitrary data.
fn flatten_if_arbitrary(
    rule: &RuleStructures,
    morphism: &RuleMorphism,
    bridge: &EqlogBridge<'_>,
    el_vars: &BTreeMap<FlatElKey, FlatVar>,
) -> Vec<FlatIfStmt> {
    let mut stmts = Vec::new();
    let src = morphism.src;
    let tgt = morphism.tgt;

    for (el0, el1) in kernel_pairs(rule, morphism) {
        let lhs = el_vars[&(src, el0)].clone();
        let rhs = el_vars[&(src, el1)].clone();
        assert_eq!(lhs.typ, rhs.typ);
        stmts.push(FlatIfStmt {
            rel: FlatInRel::Equality(lhs.typ),
            args: vec![lhs, rhs],
            age: QueryAge::All,
        });
    }

    let cod_apps = flat_rel_apps(rule, tgt, bridge);
    let img_apps = mapped_rel_apps(rule, morphism, bridge);
    let cod_st = &rule.cat.structures[tgt.0];
    let constrained = constrained_els(cod_st);

    for app in cod_apps {
        if img_apps.contains(&app) {
            continue;
        }
        if bridge.is_model_member_rel(app.rel) {
            assert_eq!(app.args.len(), 2, "model member predicates have arity 2");
            if constrained.contains(&app.args[1]) {
                continue;
            }
        }

        let args = app
            .args
            .iter()
            .map(|&el| el_vars[&(tgt, el)].clone())
            .collect();
        stmts.push(FlatIfStmt {
            rel: FlatInRel::EqlogRel(app.rel),
            args,
            age: QueryAge::All,
        });
    }

    let image = image_els(rule, morphism);
    for &el in cod_st.els.keys() {
        let el = cod_st.unification.root_const(el);
        if image.contains(&el) || constrained.contains(&el) {
            continue;
        }

        let concrete_type = concrete_type_of(rule, tgt, el);
        if !concrete_type.parents.is_empty() {
            continue;
        }

        stmts.push(FlatIfStmt {
            rel: FlatInRel::TypeSet(bridge.typ(concrete_type.typ)),
            args: vec![el_vars[&(tgt, el)].clone()],
            age: QueryAge::All,
        });
    }

    stmts
}

/// Emits a then block corresponding to the lift against a surjective morphism.
fn flatten_surj_then(
    rule: &RuleStructures,
    morphism: &RuleMorphism,
    bridge: &EqlogBridge<'_>,
    el_vars: &BTreeMap<FlatElKey, FlatVar>,
) -> Vec<FlatThenStmt> {
    let mut stmts = Vec::new();
    let src = morphism.src;
    let tgt = morphism.tgt;

    for (el0, el1) in kernel_pairs(rule, morphism) {
        let lhs = el_vars[&(src, el0)].clone();
        let rhs = el_vars[&(src, el1)].clone();
        assert_eq!(lhs.typ, rhs.typ);
        stmts.push(FlatThenStmt {
            rel: FlatOutRel::Equality(lhs.typ),
            args: vec![lhs, rhs],
        });
    }

    let img_apps = mapped_rel_apps(rule, morphism, bridge);
    for app in flat_rel_apps(rule, tgt, bridge) {
        if img_apps.contains(&app) {
            continue;
        }
        let args = app
            .args
            .iter()
            .map(|&el| el_vars[&(tgt, el)].clone())
            .collect();
        stmts.push(FlatThenStmt {
            rel: FlatOutRel::EqlogRel(app.rel),
            args,
        });
    }

    let image = image_els(rule, morphism);
    let cod_st = &rule.cat.structures[tgt.0];
    assert!(
        cod_st
            .els
            .keys()
            .all(|&el| image.contains(&cod_st.unification.root_const(el))),
        "morphism should be surjective"
    );

    stmts
}

/// Emits the pair of statements needed for a non-surjective then morphism.
fn flatten_non_surj_then(
    rule: &RuleStructures,
    morphism: &RuleMorphism,
    bridge: &EqlogBridge<'_>,
    el_vars: &BTreeMap<FlatElKey, FlatVar>,
) -> Option<(FlatIfStmt, FlatThenStmt)> {
    let tgt = morphism.tgt;
    let cod_st = &rule.cat.structures[tgt.0];
    let cod_els: BTreeSet<ElId> = cod_st
        .els
        .keys()
        .map(|&el| cod_st.unification.root_const(el))
        .collect();
    let img_els = image_els(rule, morphism);

    let mut new_els = cod_els.difference(&img_els).copied();
    let new_el = new_els.next()?;
    assert!(
        new_els.next().is_none(),
        "There should be at most one new element in the codomain"
    );

    let (app, _result) = cod_st
        .func_apps
        .iter()
        .find(|(_, &result)| cod_st.unification.root_const(result) == new_el)
        .expect("new element should be the result of a function application");

    let flat_func_args = flat_func_domain_args(cod_st, app);
    assert!(
        flat_func_args.iter().all(|arg| img_els.contains(arg)),
        "Arguments to obtain new element should be in image"
    );

    let func = bridge.func(app.func);
    let rel = bridge.func_rel(app.func);

    let flat_func_args: Vec<FlatVar> = flat_func_args
        .iter()
        .map(|&el| el_vars[&(tgt, el)].clone())
        .collect();
    let result_var = el_vars[&(tgt, new_el)].clone();

    let then_stmt = FlatThenStmt {
        rel: FlatOutRel::FuncDomain(func),
        args: flat_func_args.clone(),
    };
    let if_stmt = FlatIfStmt {
        rel: FlatInRel::EqlogRel(rel),
        args: flat_func_args.into_iter().chain([result_var]).collect(),
        age: QueryAge::All,
    };

    Some((if_stmt, then_stmt))
}

fn initial_matching_stmts(
    rule: &RuleStructures,
    bridge: &EqlogBridge<'_>,
    el_vars: &BTreeMap<FlatElKey, FlatVar>,
) -> Vec<FlatIfStmt> {
    let structure = StructureId(0);
    let st = &rule.cat.structures[structure.0];
    let mut stmts = Vec::new();

    for app in flat_rel_apps(rule, structure, bridge) {
        let args = app
            .args
            .iter()
            .map(|&el| el_vars[&(structure, el)].clone())
            .collect();
        stmts.push(FlatIfStmt {
            rel: FlatInRel::EqlogRel(app.rel),
            args,
            age: QueryAge::All,
        });
    }

    for &el in st.els.keys() {
        let el = st.unification.root_const(el);
        let concrete_type = concrete_type_of(rule, structure, el);
        if !concrete_type.parents.is_empty() {
            continue;
        }
        stmts.push(FlatIfStmt {
            rel: FlatInRel::TypeSet(bridge.typ(concrete_type.typ)),
            args: vec![el_vars[&(structure, el)].clone()],
            age: QueryAge::All,
        });
    }

    stmts
}

/// Compiles an Eqlog rule declaration into a set of [FlatRule]s.
fn flatten_rule(
    ctx: &FlattenCtx<'_>,
    rule_id: RuleDeclId,
    anonymous_index: usize,
    rule: &RuleStructures,
    bridge: &EqlogBridge<'_>,
) -> FlatRuleGroup {
    let name = ctx
        .ast
        .rule_decl(rule_id)
        .name
        .clone()
        .unwrap_or_else(|| format!("anonymous_rule_{anonymous_index}"));

    let morphisms = flatten_morphisms(rule);
    let el_vars = assign_el_vars(ctx, rule, &morphisms, bridge);

    let mut rules: Vec<FlatRule> = Vec::new();
    let mut matching_stmts: BTreeMap<StructureId, Vec<FlatIfStmt>> = BTreeMap::new();
    matching_stmts.insert(
        StructureId(0),
        initial_matching_stmts(rule, bridge, &el_vars),
    );

    for morphism in &morphisms {
        let dom_matching_stmts = matching_stmts
            .get(&morphism.src)
            .unwrap_or_else(|| panic!("missing matching statements for {:?}", morphism.src))
            .clone();

        let cod_matching_stmts = match morphism.kind {
            MorphismKind::If => dom_matching_stmts
                .iter()
                .cloned()
                .chain(flatten_if_arbitrary(rule, morphism, bridge, &el_vars))
                .collect(),
            MorphismKind::SurjThen => {
                let rule_name = format!("{name}_{}", rules.len());
                let conclusion = flatten_surj_then(rule, morphism, bridge, &el_vars);
                rules.push(FlatRule {
                    name: rule_name,
                    premise: dom_matching_stmts.clone(),
                    conclusion,
                });
                dom_matching_stmts
            }
            MorphismKind::NonSurjThen => {
                let rule_name = format!("{name}_{}", rules.len());
                let mut cod_matching_stmts = dom_matching_stmts.clone();
                if let Some((if_stmt, then_stmt)) =
                    flatten_non_surj_then(rule, morphism, bridge, &el_vars)
                {
                    rules.push(FlatRule {
                        name: rule_name,
                        premise: dom_matching_stmts,
                        conclusion: vec![then_stmt],
                    });
                    cod_matching_stmts.push(if_stmt);
                }
                cod_matching_stmts
            }
            MorphismKind::Noop => dom_matching_stmts,
        };

        let prev = matching_stmts.insert(morphism.tgt, cod_matching_stmts);
        assert!(
            prev.is_none(),
            "flatten traversal should visit each codomain once"
        );
    }

    FlatRuleGroup { name, rules }
}

pub fn flatten(ctx: &FlattenCtx<'_>) -> Vec<FlatRuleGroup> {
    let bridge = EqlogBridge::new(ctx);
    let mut groups: Vec<FlatRuleGroup> = Vec::new();

    groups.extend(ctx.signature.iter_funcs().map(|func_id| {
        let func = bridge.func(func_id);
        let rel = bridge.func_rel(func_id);
        let rel_snake = display_rel(rel, ctx.eqlog, ctx.identifiers)
            .to_string()
            .to_case(Snake);
        let rule = semi_naive_functionality(func, ctx.eqlog);
        FlatRuleGroup {
            name: format!("functionality_{rel_snake}"),
            rules: vec![rule],
        }
    }));

    let mut rule_ids = Vec::new();
    collect_rule_ids(ctx.ast, &ctx.ast.module(ctx.module).decls, &mut rule_ids);
    groups.extend(
        rule_ids
            .into_iter()
            .enumerate()
            .map(|(anonymous_index, rule_id)| {
                let rule = ctx
                    .rule_structures
                    .get(&rule_id)
                    .expect("rule structure should be built for every rule");
                postprocess_rule_group(flatten_rule(ctx, rule_id, anonymous_index, rule, &bridge))
            }),
    );

    groups
}

fn collect_rule_ids(ast: &Ast, decls: &[DeclId], out: &mut Vec<RuleDeclId>) {
    for &decl in decls {
        match *ast.decl(decl) {
            Decl::Rule(rule) => out.push(rule),
            Decl::Model(model) => collect_rule_ids(ast, &ast.model_decl(model).body, out),
            Decl::Type(_) | Decl::Pred(_) | Decl::Func(_) | Decl::Enum(_) => {}
        }
    }
}

fn postprocess_rule_group(mut group: FlatRuleGroup) -> FlatRuleGroup {
    group.rules = group
        .rules
        .iter()
        .flat_map(|rule| to_semi_naive(&eliminate_equalities_ifs(rule)))
        .map(|mut rule| {
            use_rels_with_diagonals(&mut rule);
            sort_premise(&mut rule);
            rule
        })
        .collect();
    group
}

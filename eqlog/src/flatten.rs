use std::collections::{BTreeMap, BTreeSet};
use std::sync::Arc;

use convert_case::{Case::Snake, Casing as _};

use crate::algebra::populate::{MorphismKind, RuleStructures};
use crate::algebra::signature::{FuncId, Signature};
use crate::algebra::structure::{ConcreteType, ElId, FuncApp, PredApp, Structure, StructureId};
use crate::ast::*;
use crate::flat_eqlog::*;

type FlatElKey = (StructureId, ElId);

pub(crate) struct FlattenCtx<'a> {
    ast: &'a Ast,
    module: ModuleId,
    signature: &'a Signature,
    rule_structures: &'a BTreeMap<RuleDeclId, RuleStructures>,
}

impl<'a> FlattenCtx<'a> {
    pub(crate) fn new(
        ast: &'a Ast,
        module: ModuleId,
        signature: &'a Signature,
        rule_structures: &'a BTreeMap<RuleDeclId, RuleStructures>,
    ) -> Self {
        Self {
            ast,
            module,
            signature,
            rule_structures,
        }
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
    rel: FlatRel,
    args: Vec<ElId>,
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
) -> BTreeMap<FlatElKey, FlatVar> {
    let mut el_vars: BTreeMap<FlatElKey, FlatVar> = BTreeMap::new();
    let mut available_vars = 0..;

    assign_structure_el_vars(ctx, rule, StructureId(0), &mut el_vars, &mut available_vars);

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

        assign_structure_el_vars(ctx, rule, morphism.tgt, &mut el_vars, &mut available_vars);
    }

    el_vars
}

fn assign_structure_el_vars(
    ctx: &FlattenCtx<'_>,
    rule: &RuleStructures,
    structure: StructureId,
    el_vars: &mut BTreeMap<FlatElKey, FlatVar>,
    available_vars: &mut impl Iterator<Item = usize>,
) {
    let st = &rule.cat.structures[structure.0];
    for &el in st.els.keys() {
        let el = st.unification.root_const(el);
        el_vars.entry((structure, el)).or_insert_with(|| {
            let typ = concrete_type_of(rule, structure, el).typ;
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
    signature: &Signature,
) -> BTreeSet<FlatRelApp> {
    let st = &rule.cat.structures[structure.0];
    let mut apps = BTreeSet::new();

    for app in &st.pred_apps {
        let rel = FlatRel::Pred(app.pred);
        let args = flat_pred_args(st, app);
        apps.insert(FlatRelApp { rel, args });
    }

    for (app, &result) in &st.func_apps {
        let rel = FlatRel::Func(app.func);
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
        let rel = FlatRel::ModelMember(concrete_type.typ);
        let args = vec![flat_el(st, parent), el];
        apps.insert(FlatRelApp { rel, args });
    }

    for app in &apps {
        assert_eq!(
            app.args.len(),
            app.rel_arity_len(signature),
            "lowered relation app should match signature arity"
        );
    }

    apps
}

impl FlatRelApp {
    fn rel_arity_len(&self, signature: &Signature) -> usize {
        self.rel.arity(signature).len()
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
    signature: &Signature,
) -> BTreeSet<FlatRelApp> {
    let src_apps = flat_rel_apps(rule, morphism.src, signature);
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
    signature: &Signature,
    rule: &RuleStructures,
    morphism: &RuleMorphism,
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

    let cod_apps = flat_rel_apps(rule, tgt, signature);
    let img_apps = mapped_rel_apps(rule, morphism, signature);
    let cod_st = &rule.cat.structures[tgt.0];
    let constrained = constrained_els(cod_st);

    for app in cod_apps {
        if img_apps.contains(&app) {
            continue;
        }
        if app.rel.is_model_membership_relation() {
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
            rel: FlatInRel::Rel(app.rel),
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
            rel: FlatInRel::TypeSet(concrete_type.typ),
            args: vec![el_vars[&(tgt, el)].clone()],
            age: QueryAge::All,
        });
    }

    stmts
}

/// Emits a then block corresponding to the lift against a surjective morphism.
fn flatten_surj_then(
    signature: &Signature,
    rule: &RuleStructures,
    morphism: &RuleMorphism,
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

    let img_apps = mapped_rel_apps(rule, morphism, signature);
    for app in flat_rel_apps(rule, tgt, signature) {
        if img_apps.contains(&app) {
            continue;
        }
        let args = app
            .args
            .iter()
            .map(|&el| el_vars[&(tgt, el)].clone())
            .collect();
        stmts.push(FlatThenStmt {
            rel: FlatOutRel::Rel(app.rel),
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

    let flat_func_args: Vec<FlatVar> = flat_func_args
        .iter()
        .map(|&el| el_vars[&(tgt, el)].clone())
        .collect();
    let result_var = el_vars[&(tgt, new_el)].clone();

    let then_stmt = FlatThenStmt {
        rel: FlatOutRel::FuncDomain(app.func),
        args: flat_func_args.clone(),
    };
    let if_stmt = FlatIfStmt {
        rel: FlatInRel::Rel(FlatRel::Func(app.func)),
        args: flat_func_args.into_iter().chain([result_var]).collect(),
        age: QueryAge::All,
    };

    Some((if_stmt, then_stmt))
}

fn initial_matching_stmts(
    signature: &Signature,
    rule: &RuleStructures,
    el_vars: &BTreeMap<FlatElKey, FlatVar>,
) -> Vec<FlatIfStmt> {
    let structure = StructureId(0);
    let st = &rule.cat.structures[structure.0];
    let mut stmts = Vec::new();

    for app in flat_rel_apps(rule, structure, signature) {
        let args = app
            .args
            .iter()
            .map(|&el| el_vars[&(structure, el)].clone())
            .collect();
        stmts.push(FlatIfStmt {
            rel: FlatInRel::Rel(app.rel),
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
            rel: FlatInRel::TypeSet(concrete_type.typ),
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
) -> FlatRuleGroup {
    let name = ctx
        .ast
        .rule_decl(rule_id)
        .name
        .clone()
        .unwrap_or_else(|| format!("anonymous_rule_{anonymous_index}"));

    let morphisms = flatten_morphisms(rule);
    let el_vars = assign_el_vars(ctx, rule, &morphisms);

    let mut rules: Vec<FlatRule> = Vec::new();
    let mut matching_stmts: BTreeMap<StructureId, Vec<FlatIfStmt>> = BTreeMap::new();
    matching_stmts.insert(
        StructureId(0),
        initial_matching_stmts(ctx.signature, rule, &el_vars),
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
                .chain(flatten_if_arbitrary(
                    ctx.signature,
                    rule,
                    morphism,
                    &el_vars,
                ))
                .collect(),
            MorphismKind::SurjThen => {
                let rule_name = format!("{name}_{}", rules.len());
                let conclusion = flatten_surj_then(ctx.signature, rule, morphism, &el_vars);
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
                if let Some((if_stmt, then_stmt)) = flatten_non_surj_then(rule, morphism, &el_vars)
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
    let mut groups: Vec<FlatRuleGroup> = Vec::new();

    groups.extend(ctx.signature.iter_funcs().map(|func_id| {
        let rel_snake = func_base_name(ctx, func_id).to_case(Snake);
        let rule_name = format!("functionality_{rel_snake}");
        let rule = semi_naive_functionality(func_id, ctx.signature, rule_name.clone());
        FlatRuleGroup {
            name: rule_name,
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
                postprocess_rule_group(flatten_rule(ctx, rule_id, anonymous_index, rule))
            }),
    );

    groups
}

fn func_base_name(ctx: &FlattenCtx<'_>, func: FuncId) -> String {
    if let Some((decl, _)) = ctx
        .signature
        .iter_func_decls()
        .find(|(_, func0)| *func0 == func)
    {
        return ctx.ast.func_decl(decl).name.clone();
    }
    if let Some((decl, _)) = ctx
        .signature
        .iter_ctor_decls()
        .find(|(_, func0)| *func0 == func)
    {
        return ctx.ast.ctor_decl(decl).name.clone();
    }
    if let Some((decl, ids)) = ctx
        .signature
        .iter_model_decls()
        .find(|(_, ids)| ids.dom == func || ids.cod == func)
    {
        let model_name = &ctx.ast.model_decl(decl).name;
        let suffix = if ids.dom == func { "dom" } else { "cod" };
        return format!("{model_name}_mor_{suffix}");
    }
    if let Some((member_type, _)) = ctx
        .signature
        .iter_mor_app_funcs()
        .find(|(_, func0)| *func0 == func)
    {
        return format!("{}_mor_app", ctx.signature.type_name(ctx.ast, member_type));
    }
    format!("func_{}", func.as_usize())
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

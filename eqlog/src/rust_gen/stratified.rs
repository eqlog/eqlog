use convert_case::{Case, Casing};
use itertools::Itertools;
use std::collections::{BTreeMap, BTreeSet};
use std::fmt::Display;

use indoc::writedoc;

use super::indices::{projection, source_relation};
use super::native_indices;
use super::{
    display_all_index_field_name, display_index_field_name, display_index_type,
    display_module_env_struct_name, display_morphism_components, display_out_set_field_name,
    display_type, module_env_in_rels, module_env_out_rels, RustGenCtx,
};
use crate::algebra::signature::TypeId;
use crate::flat_eqlog::{
    FlatInRel, IndexAge, IndexSelection, IndexSpec, Schedule, StratifiedPlan, Stratum,
};
use crate::fmt_util::FmtFn;
use crate::ram::{IndexPreparation, NativeIndexPreparation, RamModule, RamProgram};

pub struct Codegen<'s> {
    strata: &'s [Stratum],
    body: &'s Schedule,
    models: BTreeMap<TypeId, usize>,
    inputs: BTreeMap<FlatInRel, usize>,
    indices: BTreeMap<(FlatInRel, IndexSpec), usize>,
    old_indices: BTreeSet<(FlatInRel, IndexSpec)>,
    preparations: &'s [IndexPreparation],
    native_indices: &'s [NativeIndexPreparation],
    model_preparations: &'s BTreeMap<TypeId, IndexPreparation>,
}

fn input_key(rel: FlatInRel, mut index: IndexSpec) -> (FlatInRel, IndexSpec) {
    index.age = IndexAge::Old;
    (rel, index)
}

impl<'s> Codegen<'s> {
    fn has_stable_inputs(&self, s: usize) -> bool {
        self.preparations[s]
            .indices
            .iter()
            .any(|(rel, _)| self.strata[s].stable_inputs.contains(&source_relation(rel)))
    }

    pub fn loop_input_types<'a>(
        &'a self,
        selection: &'a IndexSelection,
        ctx: &'a RustGenCtx<'a>,
    ) -> impl Display + 'a {
        FmtFn(move |f| {
            for (s, stratum) in self.strata.iter().enumerate() {
                let mut fields = BTreeMap::new();
                for (rel, index) in &self.preparations[s].indices {
                    let source = source_relation(rel);
                    if !stratum.stable_inputs.contains(&source) {
                        continue;
                    }
                    let i = self.inputs[&source];
                    fields.insert(format!("input_{i}"), source);
                    if let Some(id) = native_indices::find(self.native_indices, rel, index) {
                        fields.insert(format!("native_input_{id}"), rel.clone());
                    } else if !selection.is_primary(rel, index) {
                        let key = input_key(rel.clone(), index.clone());
                        if self.old_indices.contains(&key) {
                            let j = self.indices[&key];
                            fields.insert(format!("index_{j}"), rel.clone());
                        }
                    }
                }
                if fields.is_empty() {
                    continue;
                }
                writeln!(f, "#[derive(Default)] struct __StableInputs{s} {{")?;
                if self.preparations[s].stable.is_some() {
                    writeln!(f, "propagated: bool,")?;
                }
                for (name, rel) in fields {
                    let typ = display_index_type(&rel, ctx);
                    writeln!(f, "{name}: Option<{typ}>,")?;
                }
                writeln!(f, "}}")?;
            }
            Ok(())
        })
    }

    fn scoped_histories(
        &self,
        ctx: &RustGenCtx<'_>,
        selection: &IndexSelection,
    ) -> BTreeMap<String, (usize, usize)> {
        let mut fields = BTreeMap::new();
        for (s, stratum) in self.strata.iter().enumerate() {
            let Some(model) = stratum.model else {
                continue;
            };
            for (rel, index) in &self.preparations[s].indices {
                let source = source_relation(rel);
                let i = self.inputs[&source];
                let count = scope_prefix(&source, model, ctx);
                if count == 0 {
                    continue;
                }
                let arity = source.arity(ctx.signature()).len() - count;
                fields.insert(format!("__scope_input_{i}_{count}"), (count, arity));
                let arity = rel.arity(ctx.signature()).len() - scope_prefix(rel, model, ctx);
                if let Some(id) = native_indices::find(self.native_indices, rel, index) {
                    fields.insert(format!("__scope_native_{id}_{count}"), (count, arity));
                } else if !selection.is_primary(rel, index) {
                    let key = input_key(rel.clone(), index.clone());
                    if self.old_indices.contains(&key) {
                        let j = self.indices[&key];
                        fields.insert(format!("__scope_index_{j}_{count}"), (count, arity));
                    }
                }
            }
        }
        fields
    }

    pub fn new(plan: &'s StratifiedPlan, program: &'s RamProgram) -> Self {
        let indices: BTreeSet<_> = program
            .preparations
            .iter()
            .flat_map(|plan| plan.indices.iter().cloned())
            .collect();
        let old_indices = indices
            .iter()
            .filter(|(_, index)| index.age == IndexAge::Old)
            .cloned()
            .collect();
        let inputs: BTreeSet<_> = indices
            .iter()
            .map(|(rel, _)| source_relation(rel))
            .collect();
        Self {
            strata: &plan.strata,
            body: &plan.body,
            models: program
                .model_preparations
                .keys()
                .copied()
                .enumerate()
                .map(|(i, model)| (model, i))
                .collect(),
            preparations: &program.preparations,
            native_indices: &program.native_indices,
            model_preparations: &program.model_preparations,
            old_indices,
            inputs: inputs
                .into_iter()
                .enumerate()
                .map(|(i, key)| (key, i))
                .collect(),
            indices: indices
                .into_iter()
                .map(|(rel, index)| input_key(rel, index))
                .collect::<BTreeSet<_>>()
                .into_iter()
                .enumerate()
                .map(|(i, key)| (key, i))
                .collect(),
        }
    }

    pub fn fields<'a>(
        &'a self,
        ctx: &'a RustGenCtx<'a>,
        selection: &'a IndexSelection,
    ) -> impl Display + 'a {
        FmtFn(move |f| {
            let count = self.strata.len();
            writeln!(f, "__stratum_initialized: [bool; {count}],")?;
            writeln!(f, "__model_owners_changed: bool,")?;
            for (s, stratum) in self.strata.iter().enumerate() {
                if let Some(model) = stratum.model {
                    let count = ctx.signature().type_(model).parents.len() + 1;
                    writeln!(
                        f,
                        "__stratum_{s}_initialized: std::collections::BTreeSet<[u32; {count}]>,"
                    )?;
                }
            }
            for (field, (count, arity)) in self.scoped_histories(ctx, selection) {
                writeln!(f, "{field}: std::collections::BTreeMap<[u32; {count}], eqlog_runtime::__private::RelationVersions<PrefixTree{arity}, (usize, Vec<u32>)>>,")?;
            }
            for (rel, i) in &self.inputs {
                let typ = display_index_type(rel, ctx);
                writeln!(
                    f,
                    "__rule_input_{i}: eqlog_runtime::__private::RelationVersions<{typ}, (usize, Vec<u32>)>,"
                )?;
            }
            for ((rel, index), i) in &self.indices {
                if selection.is_primary(rel, index)
                    || native_indices::find(self.native_indices, rel, index).is_some()
                {
                    continue;
                }
                let source = source_relation(rel);
                let source_type = display_index_type(&source, ctx);
                let target = display_index_type(rel, ctx);
                writeln!(f, "__rule_index_{i}: eqlog_runtime::__private::IndexSeed<{source_type}, {target}>,")?;
                if self.old_indices.contains(&(rel.clone(), index.clone())) {
                    writeln!(f, "__rule_index_{i}_versions: eqlog_runtime::__private::RelationVersions<{target}, (usize, Vec<u32>)>,")?;
                }
            }
            Ok(())
        })
    }

    pub fn init<'a>(
        &'a self,
        selection: &'a IndexSelection,
        ctx: &'a RustGenCtx<'a>,
    ) -> impl Display + 'a {
        FmtFn(move |f| {
            let count = self.strata.len();
            writeln!(f, "__stratum_initialized: [false; {count}],")?;
            writeln!(f, "__model_owners_changed: false,")?;
            for (s, stratum) in self.strata.iter().enumerate() {
                if stratum.model.is_some() {
                    writeln!(
                        f,
                        "__stratum_{s}_initialized: std::collections::BTreeSet::new(),"
                    )?;
                }
            }
            for field in self.scoped_histories(ctx, selection).keys() {
                writeln!(f, "{field}: std::collections::BTreeMap::new(),")?;
            }
            for i in self.inputs.values() {
                writeln!(
                    f,
                    "__rule_input_{i}: eqlog_runtime::__private::RelationVersions::new(),"
                )?;
            }
            for ((rel, index), i) in &self.indices {
                if selection.is_primary(rel, index)
                    || native_indices::find(self.native_indices, rel, index).is_some()
                {
                    continue;
                }
                writeln!(
                    f,
                    "__rule_index_{i}: eqlog_runtime::__private::IndexSeed::new(),"
                )?;
                if self.old_indices.contains(&(rel.clone(), index.clone())) {
                    writeln!(
                        f,
                        "__rule_index_{i}_versions: eqlog_runtime::__private::RelationVersions::new(),"
                    )?;
                }
            }
            Ok(())
        })
    }

    pub fn methods<'a>(
        &'a self,
        modules: &'a [RamModule],
        ctx: &'a RustGenCtx<'a>,
        selection: &'a IndexSelection,
    ) -> impl Display + 'a {
        FmtFn(move |f| {
            for (s, stratum) in self.strata.iter().enumerate() {
                let inputs: BTreeSet<_> = self.preparations[s]
                    .indices
                    .iter()
                    .map(|(rel, _)| source_relation(rel))
                    .collect();
                let stable = if self.has_stable_inputs(s) {
                    format!("stable: &mut __StableInputs{s}, ")
                } else {
                    String::new()
                };
                if let Some(model) = stratum.model {
                    let count = ctx.signature().type_(model).parents.len() + 1;
                    let retain = if !self.preparations[s].reads_descendants() {
                        ""
                    } else {
                        "retain_own: bool, "
                    };
                    writedoc! {f, "
                        fn __run_stratum_{s}_at(&mut self, owners: [u32; {count}], {retain}{stable}delta: &mut ModelDelta) -> bool {{
                            let mut dirty = !self.__stratum_{s}_initialized.contains(&owners);
                    "}?;
                } else {
                    writedoc! {f, "
                        fn __run_stratum_{s}(&mut self, {stable}delta: &mut ModelDelta) -> bool {{
                            #[allow(unused_mut)]
                            let mut dirty = !self.__stratum_initialized[{s}];
                    "}?;
                }
                if let Some(plan) = &self.preparations[s].stable {
                    writeln!(f, "if !stable.propagated {{")?;
                    if stratum.model.is_none() {
                        writeln!(f, "self.recompute_model_indices_stratum_stable_{s}();")?;
                    } else if !plan.descendants.is_empty() {
                        writeln!(
                            f,
                            "self.__prepare_descendants_stable_{s}(owners, retain_own);"
                        )?;
                    }
                    for (rel, index) in &plan.support_indices {
                        write!(f, "{}", super::indices::prepare(rel, index, selection, ctx))?;
                    }
                    writeln!(f, "stable.propagated = true; }}")?;
                }
                if !self.preparations[s].descendants.is_empty() {
                    writeln!(f, "self.__prepare_descendants_{s}(owners, retain_own);")?;
                }
                if stratum.model.is_none() && !self.preparations[s].propagation.relations.is_empty()
                {
                    writeln!(f, "self.recompute_model_indices_stratum_{s}();")?;
                }
                for rel in inputs {
                    let i = self.inputs[&rel];
                    let stable = stratum.stable_inputs.contains(&rel);
                    if stable {
                        begin_stable_input(f, &format!("input_{i}"), &rel, ctx)?;
                    }
                    let old = display_all_index_field_name(
                        &rel,
                        selection.primary(&rel, IndexAge::Old),
                        ctx,
                    );
                    let new = display_all_index_field_name(
                        &rel,
                        selection.primary(&rel, IndexAge::New),
                        ctx,
                    );
                    if ctx.has_shared_indices(&rel) {
                        writeln!(
                            f,
                            "self.__rule_input_{i}.publish_shared(&self.{old}.union(&self.{new}));"
                        )?;
                    } else {
                        writeln!(
                            f,
                            "self.__rule_input_{i}.publish(&self.{old}, &self.{new});"
                        )?;
                    }
                    if let Some(model) = stratum.model {
                        consume_scoped(
                            f,
                            &format!("__scope_input_{i}"),
                            &format!("self.__rule_input_{i}.current()"),
                            &format!("__rule_input_{i}"),
                            &format!("input_{i}"),
                            &rel,
                            model,
                            s,
                            true,
                            true,
                            ctx,
                        )?;
                    } else {
                        writeln!(
                            f,
                            "let input_{i} = self.__rule_input_{i}.consume(({s}, Vec::new()));"
                        )?;
                    }
                    if stable {
                        end_stable_input(
                            f,
                            &format!("input_{i}"),
                            &format!("self.__rule_input_{i}.current()"),
                            &rel,
                            stratum.model,
                            ctx,
                        )?;
                    }
                    writeln!(f, "dirty |= !input_{i}.new.is_empty();")?;
                }
                writeln!(f, "if !dirty {{ return false; }}")?;
                if stratum.model.is_some() {
                    writeln!(f, "self.__stratum_{s}_initialized.insert(owners);")?;
                } else {
                    writeln!(f, "self.__stratum_initialized[{s}] = true;")?;
                }
                writeln!(f, "{{")?;
                for (rel, index) in &self.preparations[s].support_indices {
                    write!(f, "{}", super::indices::prepare(rel, index, selection, ctx))?;
                }
                for id in &self.preparations[s].native_indices {
                    let rel = &self.native_indices[*id].rel;
                    let stable = stratum.stable_inputs.contains(&source_relation(rel));
                    if stable {
                        begin_stable_input(f, &format!("native_input_{id}"), rel, ctx)?;
                    }
                    if stratum.model.is_some() {
                        writeln!(f, "self.__extend_native_index_{id}();")?;
                    } else {
                        writeln!(f, "self.__prepare_native_index_{id}();")?;
                    }
                    if let Some(model) = stratum.model {
                        consume_scoped(
                            f,
                            &format!("__scope_native_{id}"),
                            &format!("self.__native_input_{id}.current()"),
                            &format!("__native_input_{id}"),
                            &format!("native_input_{id}"),
                            &self.native_indices[*id].rel,
                            model,
                            s,
                            true,
                            true,
                            ctx,
                        )?;
                    } else {
                        writeln!(
                            f,
                            "let native_input_{id} = self.__native_input_{id}.consume({s});"
                        )?;
                    }
                    if stable {
                        end_stable_input(
                            f,
                            &format!("native_input_{id}"),
                            &format!("self.__native_input_{id}.current()"),
                            rel,
                            stratum.model,
                            ctx,
                        )?;
                    }
                }
                let required_indices: BTreeSet<_> = self.preparations[s]
                    .indices
                    .iter()
                    .cloned()
                    .map(|(rel, index)| input_key(rel, index))
                    .collect();
                for (rel, index) in &required_indices {
                    if native_indices::find(self.native_indices, rel, index).is_some() {
                        continue;
                    }
                    if selection.is_primary(rel, index) {
                        continue;
                    }
                    let source = source_relation(rel);
                    let i = self.inputs[&source];
                    let j = self.indices[&input_key(rel.clone(), index.clone())];
                    let primary = selection.primary(&source, IndexAge::Old);
                    let project = projection(rel, index, primary);
                    let stable = stratum.stable_inputs.contains(&source);
                    if self.old_indices.contains(&(rel.clone(), index.clone())) {
                        if stable {
                            begin_stable_input(f, &format!("index_{j}"), rel, ctx)?;
                        }
                        let old = self.preparations[s]
                            .indices
                            .contains(&(rel.clone(), index.clone()));
                        let new = self.preparations[s].indices.contains(&(
                            rel.clone(),
                            IndexSpec {
                                age: IndexAge::New,
                                order: index.order.clone(),
                            },
                        ));
                        writedoc! {f, "
                            let index_{j} = self.__rule_index_{j}.update(self.__rule_input_{i}.current(), {project});
                            self.__rule_index_{j}_versions.publish_shared(&index_{j});
                        "}?;
                        if let Some(model) = stratum.model {
                            consume_scoped(
                                f,
                                &format!("__scope_index_{j}"),
                                &format!("&index_{j}"),
                                &format!("__rule_index_{j}_versions"),
                                &format!("index_{j}"),
                                rel,
                                model,
                                s,
                                old,
                                new,
                                ctx,
                            )?;
                        } else {
                            writeln!(f, "let index_{j} = self.__rule_index_{j}_versions.consume_required::<{old}, {new}>(({s}, Vec::new()));")?;
                        }
                        if stable {
                            end_stable_input(
                                f,
                                &format!("index_{j}"),
                                &format!("self.__rule_index_{j}_versions.current()"),
                                rel,
                                stratum.model,
                                ctx,
                            )?;
                        }
                    } else {
                        // A delta-only reader does not need the full relation reordered.
                        if stable {
                            let typ = display_index_type(rel, ctx);
                            writeln!(f, "let index_{j} = if input_{i}.new.is_empty() {{ {typ}::new() }} else {{ self.__rule_index_{j}.update(&input_{i}.new, {project}) }};")?;
                        } else {
                            writeln!(f, "let index_{j} = self.__rule_index_{j}.update(&input_{i}.new, {project});")?;
                        }
                    }
                }
                for &m in &stratum.groups {
                    let module = &modules[m];
                    let env = display_module_env_struct_name(module);
                    let name = &module.name;
                    writeln!(f, "let env = {env} {{ phantom: std::marker::PhantomData,")?;
                    if stratum.model.is_some() {
                        writeln!(f, "__owners: owners,")?;
                    }
                    for (rel, index) in module_env_in_rels(module) {
                        let field = display_index_field_name(&rel, &index, ctx);
                        let age = match index.age {
                            IndexAge::Old => "old",
                            IndexAge::New => "new",
                        };
                        let i = self.inputs[&source_relation(&rel)];
                        if let Some(id) = native_indices::find(self.native_indices, &rel, &index) {
                            writeln!(f, "{field}: &native_input_{id}.{age},")?;
                        } else if selection.is_primary(&rel, &index) {
                            writeln!(f, "{field}: &input_{i}.{age},")?;
                        } else {
                            let key = input_key(rel.clone(), index.clone());
                            let j = self.indices[&key];
                            if self.old_indices.contains(&key) {
                                writeln!(f, "{field}: &index_{j}.{age},")?;
                            } else {
                                writeln!(f, "{field}: &index_{j},")?;
                            }
                        }
                    }
                    for rel in module_env_out_rels(module) {
                        let field = display_out_set_field_name(&rel, ctx);
                        writeln!(f, "{field}: &mut delta.{field},")?;
                    }
                    writeln!(f, "}}; {name}(env);")?;
                }
                writeln!(f, "}}")?;
                writedoc! {f, "
                        self.move_new_to_old();
                        delta.apply_equalities(self);
                        self.__canonicalize_relations();
                        delta.apply_tuples(self);
                        true
                    }}
                "}?;
            }
            for (&model, &m) in &self.models {
                let plan = &self.model_preparations[&model];
                for &model in &plan.propagation.models {
                    let name = display_type(model, ctx).to_string().to_case(Case::Snake);
                    let count = ctx.signature().type_(model).parents.len();
                    writedoc! {f, "
                    fn __transport_component_{m}_{name}(&mut self, parents: [u32; {count}], morphisms: &[MorphismWithSignature], retain_own: bool) -> bool {{
                        if morphisms.is_empty() {{ return false; }}
                        let mut changed = false;
                "}?;
                    fold_primary_ages(f, plan, ctx, selection)?;
                    writeln!(f, "for morphism in morphisms {{ changed |= self.__propagate_{name}_morphism_model_{m}(parents, morphism, retain_own); }}")?;
                    for (rel, index) in &plan.support_indices {
                        write!(f, "{}", super::indices::prepare(rel, index, selection, ctx))?;
                    }
                    for id in &plan.native_indices {
                        let native = &self.native_indices[*id];
                        if let Some(level) = native.models.iter().position(|&typ| typ == model) {
                            writedoc! {f, "
                            self.__extend_native_index_{id}();
                            let mut index = self.__native_input_{id}.current().clone();
                            for morphism in morphisms {{ changed |= self.__native_{id}_morphism_{level}(parents, morphism, &mut index, retain_own); }}
                            self.__native_input_{id}.publish_shared(&index);
                        "}?;
                        }
                    }
                    writeln!(f, "changed }}")?;
                }
            }
            for (s, stratum) in self.strata.iter().enumerate() {
                let preparation = &self.preparations[s];
                let plans = std::iter::once((s.to_string(), preparation)).chain(
                    preparation
                        .stable
                        .iter()
                        .map(|plan| (format!("stable_{s}"), plan.as_ref())),
                );
                for (suffix, plan) in plans {
                    if plan.descendants.is_empty() {
                        continue;
                    }
                    let model = stratum
                        .model
                        .expect("descendant preparation needs a bound owner");
                    let count = ctx.signature().type_(model).parents.len() + 1;
                    writeln!(f, "fn __prepare_descendants_{suffix}(&mut self, owners: [u32; {count}], retain_own: bool) {{")?;
                    fold_primary_ages(f, plan, ctx, selection)?;
                    for &child in &plan.descendants {
                        let name = display_type(child, ctx).to_string().to_case(Case::Snake);
                        writeln!(
                            f,
                            "self.__propagate_{name}_morphisms_stratum_{suffix}(owners, retain_own);"
                        )?;
                    }
                    for (rel, index) in &plan.support_indices {
                        write!(f, "{}", super::indices::prepare(rel, index, selection, ctx))?;
                    }
                    for id in &plan.native_indices {
                        if plan
                            .stable
                            .as_ref()
                            .is_some_and(|stable| stable.native_indices.contains(id))
                        {
                            continue;
                        }
                        let native = &self.native_indices[*id];
                        if native
                            .models
                            .get(count)
                            .is_some_and(|child| plan.descendants.contains(child))
                        {
                            writedoc! {f, "
                                self.__extend_native_index_{id}();
                                let mut index = self.__native_input_{id}.current().clone();
                                self.__native_{id}_model_{count}(owners, &mut index, retain_own);
                                self.__native_input_{id}.publish_shared(&index);
                            "}?;
                        }
                    }
                    writeln!(f, "}}")?;
                }
            }
            writedoc! {f, "
                fn __refresh_model_consumers(&mut self) {{
                    if !self.__model_owners_changed {{ return; }}
                    self.__model_owners_changed = false;
            "}?;
            for (s, stratum) in self.strata.iter().enumerate() {
                if stratum.model.is_some() {
                    writeln!(f, "self.__stratum_{s}_initialized.clear();")?;
                }
            }
            for field in self.scoped_histories(ctx, selection).keys() {
                writeln!(f, "self.{field}.clear();")?;
            }
            for i in self.inputs.values() {
                writeln!(
                    f,
                    "self.__rule_input_{i}.retain_consumers(|(_, owners)| owners.is_empty());"
                )?;
            }
            for ((rel, index), i) in &self.indices {
                if self.old_indices.contains(&(rel.clone(), index.clone()))
                    && !selection.is_primary(rel, index)
                    && native_indices::find(self.native_indices, rel, index).is_none()
                {
                    writeln!(f, "self.__rule_index_{i}_versions.retain_consumers(|(_, owners)| owners.is_empty());")?;
                }
            }
            writeln!(f, "}}")?;
            Ok(())
        })
    }

    pub fn close<'a>(
        &'a self,
        ctx: &'a RustGenCtx<'a>,
        selection: &'a IndexSelection,
    ) -> impl Display + 'a {
        FmtFn(move |f| {
            writedoc! {f, "
                /// Closes the model until the condition holds or all rules are satisfied.
                /// Depending on the axioms, this may run indefinitely.
                #[allow(dead_code)]
                pub fn close_until(&mut self, condition: impl Fn(&Self) -> bool) -> bool {{
                    self.__close_until(Some(&condition))
                }}

                fn __close_until(&mut self, condition: Option<&dyn Fn(&Self) -> bool>) -> bool {{
                    self.__canonicalize_relations();
                    if self.__check_condition(condition) {{ return true; }}
                    let mut delta = std::mem::replace(&mut self.__pending_delta, ModelDelta::new());
                    loop {{
            "}?;
            emit_schedule(
                f, self.body, None, 0, None, None, "false", self, ctx, selection,
            )?;
            writedoc! {f, "
                        self.move_new_to_old();
                        delta.apply_func_defs(self);
                        if !self.is_dirty() {{
                            self.__pending_delta = delta;
                            self.canonicalize();
                            return false;
                        }}
                        self.__canonicalize_relations();
                        if self.__check_condition(condition) {{
                            self.__pending_delta = delta;
                            return true;
                        }}
                    }}
                }}
            "}
        })
    }
}

fn begin_stable_input(
    f: &mut std::fmt::Formatter<'_>,
    name: &str,
    rel: &FlatInRel,
    ctx: &RustGenCtx<'_>,
) -> std::fmt::Result {
    let typ = display_index_type(rel, ctx);
    writedoc! {f, "
        let {name} = if let Some(current) = &stable.{name} {{
            eqlog_runtime::__private::RelationView {{ old: current.clone(), new: {typ}::new() }}
        }} else {{
    "}
}

fn end_stable_input(
    f: &mut std::fmt::Formatter<'_>,
    name: &str,
    source: &str,
    rel: &FlatInRel,
    model: Option<TypeId>,
    ctx: &RustGenCtx<'_>,
) -> std::fmt::Result {
    let prefix = model.map_or(0, |model| scope_prefix(rel, model, ctx));
    let arity = rel.arity(ctx.signature()).len();
    let mut current = format!("({source})");
    for i in 0..prefix {
        let dim = arity - i - 1;
        current = format!("{current}.get(owners[{i}]).unwrap_or_else(|| PrefixTree{dim}::empty())");
    }
    writeln!(f, "let full = {current}.clone();")?;
    for i in (0..prefix).rev() {
        let dim = arity - i;
        writeln!(f, "let full = {{ let mut tree = PrefixTree{dim}::new(); tree.insert_restriction(owners[{i}], full); tree }};")?;
    }
    writeln!(f, "stable.{name} = Some(full); {name} }};")
}

fn emit_loop_inputs(
    f: &mut std::fmt::Formatter<'_>,
    schedule: &Schedule,
    codegen: &Codegen<'_>,
) -> std::fmt::Result {
    match schedule {
        Schedule::Rules(id) => {
            let s = id.0;
            if codegen.has_stable_inputs(s) {
                writeln!(f, "let mut stable_{s} = __StableInputs{s}::default();")?;
            }
        }
        Schedule::Sequence(children) | Schedule::Independent(children) => {
            for child in children {
                emit_loop_inputs(f, child, codegen)?;
            }
        }
        Schedule::Saturate(_) | Schedule::ModelComponents { .. } => {}
    }
    Ok(())
}

fn scope_prefix(rel: &FlatInRel, model: TypeId, ctx: &RustGenCtx<'_>) -> usize {
    let parent = match rel {
        FlatInRel::Rel(rel) | FlatInRel::RelWithDiagonals { rel, .. } => {
            rel.parent_model_type(ctx.signature())
        }
        FlatInRel::TypeSet(_) | FlatInRel::Equality(_) => None,
    };
    parent.map_or(0, |parent| {
        assert!(
            parent == model
                || ctx.signature().type_(model).parents.contains(&parent)
                || ctx.signature().type_(parent).parents.contains(&model)
        );
        (ctx.signature().type_(parent).parents.len() + 1)
            .min(ctx.signature().type_(model).parents.len() + 1)
    })
}

fn consume_scoped(
    f: &mut std::fmt::Formatter<'_>,
    field: &str,
    source: &str,
    global: &str,
    name: &str,
    rel: &FlatInRel,
    model: TypeId,
    stratum: usize,
    old: bool,
    new: bool,
    ctx: &RustGenCtx<'_>,
) -> std::fmt::Result {
    let arity = rel.arity(ctx.signature()).len();
    let prefix = scope_prefix(rel, model, ctx);
    if prefix == 0 {
        return writeln!(f, "let {name} = self.{global}.consume_required::<{old}, {new}>(({stratum}, owners.to_vec()));");
    }
    let field = format!("{field}_{prefix}");
    let key = (0..prefix).map(|i| format!("owners[{i}]")).join(", ");
    let mut current = format!("({source})");
    for i in 0..prefix {
        let dim = arity - i - 1;
        current = format!("{current}.get(owners[{i}]).unwrap_or_else(|| PrefixTree{dim}::empty())");
    }
    writedoc! {f, "
        let {name} = {{
            let current = {current};
            let history = self.{field}.entry([{key}]).or_insert_with(eqlog_runtime::__private::RelationVersions::new);
            history.publish_shared(current);
            let view = history.consume_required::<{old}, {new}>(({stratum}, owners.to_vec()));
    "}?;
    for age in ["old", "new"] {
        writeln!(f, "let {age} = view.{age};")?;
        for i in (0..prefix).rev() {
            let dim = arity - i;
            writeln!(f, "let {age} = {{ let mut tree = PrefixTree{dim}::new(); tree.insert_restriction(owners[{i}], {age}); tree }};")?;
        }
    }
    writedoc! {f, "
            eqlog_runtime::__private::RelationView {{ old, new }}
        }};
    "}
}

fn fold_primary_ages(
    f: &mut std::fmt::Formatter<'_>,
    plan: &IndexPreparation,
    ctx: &RustGenCtx<'_>,
    selection: &IndexSelection,
) -> std::fmt::Result {
    for &rel in &plan.propagation.relations {
        let rel = FlatInRel::Rel(rel);
        let old = display_all_index_field_name(&rel, selection.primary(&rel, IndexAge::Old), ctx);
        let new = display_all_index_field_name(&rel, selection.primary(&rel, IndexAge::New), ctx);
        writeln!(
            f,
            "self.{new} = self.{old}.union(&self.{new}); self.{old}.clear();"
        )?;
    }
    Ok(())
}

fn emit_schedule(
    f: &mut std::fmt::Formatter<'_>,
    schedule: &Schedule,
    active: Option<usize>,
    depth: usize,
    scope: Option<TypeId>,
    root: Option<TypeId>,
    retain_own: &str,
    codegen: &Codegen<'_>,
    ctx: &RustGenCtx<'_>,
    selection: &IndexSelection,
) -> std::fmt::Result {
    match schedule {
        Schedule::Sequence(children) | Schedule::Independent(children) => {
            for child in children {
                emit_schedule(
                    f, child, active, depth, scope, root, retain_own, codegen, ctx, selection,
                )?;
            }
        }
        Schedule::Rules(id) => {
            let s = id.0;
            let stable = if codegen.has_stable_inputs(s) {
                format!("&mut stable_{s}, ")
            } else {
                String::new()
            };
            if scope.is_some() {
                let retain = if !codegen.preparations[s].reads_descendants() {
                    String::new()
                } else {
                    format!("{retain_own}, ")
                };
                writeln!(
                    f,
                    "if self.__run_stratum_{s}_at(owners, {retain}{stable}&mut delta) {{"
                )?;
            } else {
                writeln!(f, "if self.__run_stratum_{s}({stable}&mut delta) {{")?;
            }
            if let Some(active) = active {
                writeln!(f, "active_{active} = true;")?;
            }
            writedoc! {f, "
                if self.__check_condition(condition) {{
                    self.__pending_delta = delta;
                    return true;
                }}
            }}
            "}?;
        }
        Schedule::Saturate(body) => {
            writeln!(f, "{{")?;
            emit_loop_inputs(f, body, codegen)?;
            writeln!(f, "loop {{ let mut active_{depth} = false;")?;
            emit_schedule(
                f,
                body,
                Some(depth),
                depth + 1,
                scope,
                root,
                retain_own,
                codegen,
                ctx,
                selection,
            )?;
            writeln!(f, "if !active_{depth} {{ break; }}")?;
            if let Some(active) = active {
                writeln!(f, "active_{active} = true;")?;
            }
            writeln!(f, "}} }}")?;
        }
        Schedule::ModelComponents { model, body } => {
            writeln!(f, "{{")?;
            if root.is_none() {
                let m = codegen.models[model];
                let plan = &codegen.model_preparations[model];
                writeln!(f, "self.__refresh_model_consumers(); self.recompute_model_indices_model_{m}(); let parents = [];")?;
                for (rel, index) in &plan.support_indices {
                    write!(f, "{}", super::indices::prepare(rel, index, selection, ctx))?;
                }
                for id in &plan.native_indices {
                    writeln!(f, "self.__prepare_native_index_{id}();")?;
                }
            } else {
                writeln!(f, "let parents = owners;")?;
            }
            emit_components(
                f,
                *model,
                root.unwrap_or(*model),
                body,
                active,
                depth,
                retain_own,
                codegen,
                ctx,
                selection,
            )?;
            writeln!(f, "}}")?;
        }
    }
    Ok(())
}

fn emit_components(
    f: &mut std::fmt::Formatter<'_>,
    model: TypeId,
    root: TypeId,
    body: &Schedule,
    active: Option<usize>,
    depth: usize,
    retain_own: &str,
    codegen: &Codegen<'_>,
    ctx: &RustGenCtx<'_>,
    selection: &IndexSelection,
) -> std::fmt::Result {
    let m = codegen.models[&root];
    let name = display_type(model, ctx).to_string().to_case(Case::Snake);
    let parent_count = ctx.signature().type_(model).parents.len();
    let plan = &codegen.model_preparations[&root];
    for (rel, index) in plan
        .propagation
        .graph_indices
        .get(&model)
        .into_iter()
        .flatten()
    {
        write!(f, "{}", super::indices::prepare(rel, index, selection, ctx))?;
    }
    // Transport in an enclosing cycle can change this graph between visits.
    write!(
        f,
        "{}",
        display_morphism_components(model, ctx, selection, true)
    )?;
    writeln!(f, "for component in components {{")?;
    writeln!(f, "#[allow(unused_variables)] let retain_component_{depth} = {retain_own} || !component.internal.is_empty();")?;
    writedoc! {f, "
            loop {{
                let mut active_{depth} = false;
                for &object in &component.objects {{
    "}?;
    let owners = (0..parent_count)
        .map(|i| format!("parents[{i}]"))
        .chain(std::iter::once("object".to_string()))
        .join(", ");
    writeln!(f, "let owners = [{owners}];")?;
    emit_schedule(
        f,
        body,
        Some(depth),
        depth + 1,
        Some(model),
        Some(root),
        &format!("retain_component_{depth}"),
        codegen,
        ctx,
        selection,
    )?;
    writedoc! {f, "
                }}
                active_{depth} |= self.__transport_component_{m}_{name}(parents, &component.internal, true);
    "}?;
    if let Some(active) = active {
        writeln!(f, "active_{active} |= active_{depth};")?;
    }
    writeln!(
        f,
        "if component.internal.is_empty() || !active_{depth} {{ break; }} }}"
    )?;
    if let Some(active) = active {
        write!(f, "active_{active} |= ")?;
    }
    writeln!(
        f,
        "self.__transport_component_{m}_{name}(parents, &component.outgoing, {retain_own}); }}"
    )
}

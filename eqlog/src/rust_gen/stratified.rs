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
    FlatInRel, FlatOutRel, IndexAge, IndexSelection, IndexSpec, RuleSchedule, Schedule, Stratum,
};
use crate::fmt_util::FmtFn;
use crate::ram::{
    IndexPreparation, NativeIndexPreparation, NativePreparation, RamModule, RamProgram,
};

pub struct Codegen<'s> {
    strata: &'s [Stratum],
    body: &'s Schedule,
    models: BTreeMap<TypeId, usize>,
    inputs: BTreeMap<FlatInRel, usize>,
    indices: BTreeMap<(FlatInRel, IndexSpec), usize>,
    old_indices: BTreeSet<(FlatInRel, IndexSpec)>,
    preparations: &'s [IndexPreparation],
    native_indices: &'s [NativeIndexPreparation],
    model_preparations: &'s BTreeMap<TypeId, NativePreparation>,
}

fn input_key(rel: FlatInRel, mut index: IndexSpec) -> (FlatInRel, IndexSpec) {
    index.age = IndexAge::Old;
    (rel, index)
}

impl<'s> Codegen<'s> {
    pub fn tracks_owner(&self, typ: TypeId, ctx: &RustGenCtx<'_>) -> bool {
        self.strata
            .iter()
            .filter_map(|stratum| stratum.model)
            .any(|model| typ == model || ctx.signature().type_(model).parents.contains(&typ))
    }

    fn stratum_inputs(&self, s: usize) -> BTreeSet<FlatInRel> {
        self.preparations[s]
            .indices
            .iter()
            .map(|(rel, _)| source_relation(rel))
            .collect()
    }

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
                if let Some(model) = stratum.model {
                    writeln!(f, "struct __OwnerInputs{s} {{")?;
                    for rel in self.stratum_inputs(s) {
                        let i = self.inputs[&rel];
                        let arity =
                            rel.arity(ctx.signature()).len() - scope_prefix(&rel, model, ctx);
                        writeln!(f, "input_{i}: PrefixTree{arity},")?;
                    }
                    writeln!(f, "}}")?;
                }
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
    ) -> BTreeMap<String, (Vec<TypeId>, usize)> {
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
                let owners: Vec<_> = ctx
                    .signature()
                    .type_(model)
                    .parents
                    .iter()
                    .copied()
                    .chain(std::iter::once(model))
                    .take(count)
                    .collect();
                let arity = source.arity(ctx.signature()).len() - count;
                fields.insert(
                    format!("__scope_input_{i}_{count}"),
                    (owners.clone(), arity),
                );
                let arity = rel.arity(ctx.signature()).len() - scope_prefix(rel, model, ctx);
                if let Some(id) = native_indices::find(self.native_indices, rel, index) {
                    fields.insert(
                        format!("__scope_native_{id}_{count}"),
                        (owners.clone(), arity),
                    );
                } else if !selection.is_primary(rel, index) {
                    let key = input_key(rel.clone(), index.clone());
                    if self.old_indices.contains(&key) {
                        let j = self.indices[&key];
                        fields.insert(
                            format!("__scope_index_{j}_{count}"),
                            (owners.clone(), arity),
                        );
                    }
                }
            }
        }
        fields
    }

    pub fn new(plan: &'s RuleSchedule, program: &'s RamProgram) -> Self {
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
            for (_, ids) in ctx
                .signature()
                .iter_model_decls()
                .filter(|(_, ids)| self.tracks_owner(ids.type_, ctx))
            {
                let name = display_type(ids.type_, ctx)
                    .to_string()
                    .to_case(Case::Snake);
                writeln!(f, "__merged_{name}: std::collections::BTreeSet<u32>,")?;
            }
            for (s, stratum) in self.strata.iter().enumerate() {
                if let Some(model) = stratum.model {
                    let count = ctx.signature().type_(model).parents.len() + 1;
                    writeln!(
                        f,
                        "__owner_inputs_{s}: std::collections::BTreeMap<[u32; {count}], __OwnerInputs{s}>,"
                    )?;
                }
            }
            for (field, (owners, arity)) in self.scoped_histories(ctx, selection) {
                let count = owners.len();
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
            for (_, ids) in ctx
                .signature()
                .iter_model_decls()
                .filter(|(_, ids)| self.tracks_owner(ids.type_, ctx))
            {
                let name = display_type(ids.type_, ctx)
                    .to_string()
                    .to_case(Case::Snake);
                writeln!(f, "__merged_{name}: std::collections::BTreeSet::new(),")?;
            }
            for (s, stratum) in self.strata.iter().enumerate() {
                if stratum.model.is_some() {
                    writeln!(f, "__owner_inputs_{s}: std::collections::BTreeMap::new(),")?;
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
                let inputs = self.stratum_inputs(s);
                let stable = if self.has_stable_inputs(s) {
                    format!("stable: &mut __StableInputs{s}, ")
                } else {
                    String::new()
                };
                writeln!(f, "#[allow(unused_variables)]")?;
                if let Some(model) = stratum.model {
                    let count = ctx.signature().type_(model).parents.len() + 1;
                    let retain = if !self.preparations[s].reads_descendants() {
                        ""
                    } else {
                        "retain_own: bool, "
                    };
                    writedoc! {f, "
                        fn __run_stratum_{s}_at(&mut self, owners: [u32; {count}], {retain}{stable}delta: &mut ModelDelta) -> bool {{
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
                    if plan.descendants.is_empty() {
                        for (rel, index) in &plan.support_indices {
                            write!(f, "{}", super::indices::prepare(rel, index, selection, ctx))?;
                        }
                    }
                    writeln!(f, "stable.propagated = true; }}")?;
                }
                let native = &self.preparations[s].native;
                if !native.descendants.is_empty() {
                    writeln!(f, "self.__prepare_descendants_{s}(owners, retain_own);")?;
                }
                if stratum.model.is_none() && !native.propagation.relations.is_empty() {
                    writeln!(f, "self.recompute_model_indices_stratum_{s}();")?;
                }
                if let Some(model) = stratum.model {
                    // Most owners have no new input on an incremental visit.
                    // Comparing roots avoids constructing their consumer views.
                    let mut unchanged = vec!["true".to_owned()];
                    let mut snapshots = Vec::new();
                    for rel in &inputs {
                        let i = self.inputs[rel];
                        let field =
                            display_all_index_field_name(rel, selection.current_primary(rel), ctx);
                        let source = scoped_tree(&format!("&self.{field}"), rel, model, ctx);
                        writeln!(f, "let input_{i} = {source};")?;
                        unchanged.push(format!("eqlog_runtime::__private::SnapshotSet::shares_root(input_{i}, &_previous.input_{i})"));
                        snapshots.push(format!("input_{i}: input_{i}.clone()"));
                    }
                    let unchanged = unchanged.join(" && ");
                    let snapshots = snapshots.join(", ");
                    writedoc! {f, "
                        let previous = self.__owner_inputs_{s}.get(&owners);
                        #[allow(unused_mut)]
                        let mut dirty = previous.is_none();
                        if previous.is_some_and(|_previous| {unchanged}) {{
                            return false;
                        }}
                        let checkpoint = __OwnerInputs{s} {{ {snapshots} }};
                        self.__owner_inputs_{s}.insert(owners, checkpoint);
                    "}?;
                    let possible: BTreeSet<_> = stratum
                        .groups
                        .iter()
                        .flat_map(|&m| &modules[m].routines)
                        .map(|routine| {
                            let sources: BTreeSet<_> = routine
                                .input_indices()
                                .iter()
                                .map(|(rel, _)| self.inputs[&source_relation(rel)])
                                .collect();
                            if sources.is_empty() {
                                "true".to_owned()
                            } else {
                                sources
                                    .iter()
                                    .map(|i| format!("!input_{i}.is_empty()"))
                                    .join(" && ")
                            }
                        })
                        .collect();
                    if !possible.contains("true") {
                        let possible = if possible.is_empty() {
                            "false".to_owned()
                        } else {
                            possible.iter().map(|expr| format!("({expr})")).join(" || ")
                        };
                        writeln!(f, "if !({possible}) {{ return false; }}")?;
                    }
                }
                for rel in inputs {
                    let i = self.inputs[&rel];
                    let old = self.preparations[s].indices.iter().any(|(input, index)| {
                        input == &rel
                            && index.age == IndexAge::Old
                            && selection.is_primary(input, index)
                    });
                    let stable = stratum.stable_inputs.contains(&rel);
                    if stable {
                        begin_stable_input(f, &format!("input_{i}"), &rel, ctx)?;
                    }
                    let current =
                        display_all_index_field_name(&rel, selection.current_primary(&rel), ctx);
                    writeln!(f, "self.__rule_input_{i}.publish(&self.{current});")?;
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
                            old,
                            true,
                            ctx,
                        )?;
                    } else {
                        writeln!(
                            f,
                            "let input_{i} = self.__rule_input_{i}.consume_required::<{old}, true>(({s}, Vec::new()));"
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
                if stratum.model.is_none() {
                    writeln!(f, "self.__stratum_initialized[{s}] = true;")?;
                }
                writeln!(f, "{{")?;
                if native.descendants.is_empty() {
                    for (rel, index) in &native.support_indices {
                        write!(f, "{}", super::indices::prepare(rel, index, selection, ctx))?;
                    }
                }
                for id in self.preparations[s].native_indices() {
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
                    let primary = selection.current_primary(&source);
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
                            self.__rule_index_{j}_versions.publish(&index_{j});
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
                let outputs: BTreeSet<_> = stratum
                    .groups
                    .iter()
                    .flat_map(|&m| module_env_out_rels(&modules[m]))
                    .collect();
                let mut equalities = Vec::new();
                for output in &outputs {
                    match output {
                        FlatOutRel::Equality(typ) => {
                            let name = display_type(*typ, ctx).to_string().to_case(Case::Snake);
                            writedoc! {f, "
                                for [lhs, rhs] in delta.new_{name}_equalities.drain(..) {{
                                    self.__equate_{name}(lhs.into(), rhs.into());
                                }}
                            "}?;
                            equalities.push(format!("!self.{name}_uprooted.is_empty()"));
                        }
                        FlatOutRel::Rel(_) | FlatOutRel::FuncDomain(_) => {}
                    }
                }
                if !equalities.is_empty() {
                    let changed = equalities.join(" || ");
                    writeln!(f, "if {changed} {{ self.__canonicalize_relations(); }}")?;
                }
                for output in &outputs {
                    match output {
                        FlatOutRel::Rel(rel) => {
                            let field = display_out_set_field_name(output, ctx);
                            let insert = ctx.internal_insert_name(*rel);
                            let args = (0..rel.arity(ctx.signature()).len())
                                .map(|i| format!("arg{i}"))
                                .collect::<Vec<_>>();
                            let converted =
                                args.iter().map(|arg| format!("{arg}.into()")).join(", ");
                            let args = args.join(", ");
                            writeln!(f, "for [{args}] in delta.{field}.drain(..) {{ self.{insert}({converted}); }}")?;
                        }
                        FlatOutRel::Equality(_) | FlatOutRel::FuncDomain(_) => {}
                    }
                }
                writeln!(f, "true }}")?;
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
                            self.__native_input_{id}.publish(&index);
                        "}?;
                        }
                    }
                    writeln!(f, "changed }}")?;
                }
            }
            for (s, stratum) in self.strata.iter().enumerate() {
                let preparation = &self.preparations[s];
                let plans = std::iter::once((s.to_string(), &preparation.native)).chain(
                    preparation
                        .stable
                        .iter()
                        .map(|plan| (format!("stable_{s}"), plan)),
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
                                self.__native_input_{id}.publish(&index);
                            "}?;
                        }
                    }
                    writeln!(f, "}}")?;
                }
            }
            writedoc! {f, "
                #[allow(unused_variables)]
                fn __refresh_model_consumers(&mut self) {{
                    if !self.__model_owners_changed {{ return; }}
                    self.__model_owners_changed = false;
            "}?;
            for (_, ids) in ctx
                .signature()
                .iter_model_decls()
                .filter(|(_, ids)| self.tracks_owner(ids.type_, ctx))
            {
                let name = display_type(ids.type_, ctx)
                    .to_string()
                    .to_case(Case::Snake);
                writeln!(
                    f,
                    "#[allow(unused_variables)] let merged_{name} = &self.__merged_{name};"
                )?;
            }
            writeln!(f, "let retain_consumer = |(stratum, owners): &(usize, Vec<u32>)| {{ match *stratum {{")?;
            for (s, stratum) in self.strata.iter().enumerate() {
                if let Some(model) = stratum.model {
                    let owners: Vec<_> = ctx
                        .signature()
                        .type_(model)
                        .parents
                        .iter()
                        .copied()
                        .chain(std::iter::once(model))
                        .collect();
                    let retain = retain_owners(&owners, ctx);
                    writeln!(f, "{s} => {retain},")?;
                }
            }
            writeln!(f, "_ => true, }} }};")?;
            for (s, stratum) in self.strata.iter().enumerate() {
                if let Some(model) = stratum.model {
                    let owners: Vec<_> = ctx
                        .signature()
                        .type_(model)
                        .parents
                        .iter()
                        .copied()
                        .chain(std::iter::once(model))
                        .collect();
                    let retain = retain_owners(&owners, ctx);
                    writeln!(f, "self.__owner_inputs_{s}.retain(|owners, _| {retain});")?;
                }
            }
            for (field, (owners, _)) in self.scoped_histories(ctx, selection) {
                let retain = retain_owners(&owners, ctx);
                writedoc! {f, "
                    self.{field}.retain(|owners, history| {{
                        history.retain_consumers(&retain_consumer);
                        {retain}
                    }});
                "}?;
            }
            for i in self.inputs.values() {
                writeln!(
                    f,
                    "self.__rule_input_{i}.retain_consumers(&retain_consumer);"
                )?;
            }
            for ((rel, index), i) in &self.indices {
                if self.old_indices.contains(&(rel.clone(), index.clone()))
                    && !selection.is_primary(rel, index)
                    && native_indices::find(self.native_indices, rel, index).is_none()
                {
                    writeln!(
                        f,
                        "self.__rule_index_{i}_versions.retain_consumers(&retain_consumer);"
                    )?;
                }
            }
            for (_, ids) in ctx
                .signature()
                .iter_model_decls()
                .filter(|(_, ids)| self.tracks_owner(ids.type_, ctx))
            {
                let name = display_type(ids.type_, ctx)
                    .to_string()
                    .to_case(Case::Snake);
                writeln!(f, "self.__merged_{name}.clear();")?;
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
                    if self.__closed {{
                        return condition.is_some_and(|condition| condition(self));
                    }}
                    self.__canonicalize_relations();
                    if self.__check_condition(condition) {{ return true; }}
                    let mut delta = std::mem::replace(&mut self.__pending_delta, ModelDelta::new());
                    loop {{
            "}?;
            emit_schedule(f, self.body, None, 0, None, "false", self, ctx, selection)?;
            writedoc! {f, "
                        self.__allocated = false;
                        delta.apply_func_defs(self);
                        if !self.__allocated {{
                            std::mem::swap(&mut self.__pending_delta, &mut delta);
                            self.canonicalize();
                            self.__closed = true;
                            return false;
                        }}
                        self.__canonicalize_relations();
                    }}
                }}
            "}
        })
    }
}

fn retain_owners(owners: &[TypeId], ctx: &RustGenCtx<'_>) -> String {
    owners
        .iter()
        .enumerate()
        .map(|(i, &model)| {
            let name = display_type(model, ctx).to_string().to_case(Case::Snake);
            format!("!merged_{name}.contains(&owners[{i}])")
        })
        .join(" && ")
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
    let current = model.map_or_else(
        || source.to_owned(),
        |model| scoped_tree(source, rel, model, ctx),
    );
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

fn scoped_tree(source: &str, rel: &FlatInRel, model: TypeId, ctx: &RustGenCtx<'_>) -> String {
    let arity = rel.arity(ctx.signature()).len();
    if scope_prefix(rel, model, ctx) == 0 {
        return source.to_owned();
    }
    let mut current = format!("({source})");
    for i in 0..scope_prefix(rel, model, ctx) {
        let dim = arity - i - 1;
        current = format!("{current}.get(owners[{i}]).unwrap_or_else(|| PrefixTree{dim}::empty())");
    }
    current
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
    let current = scoped_tree(source, rel, model, ctx);
    writedoc! {f, "
        let {name} = {{
            let current = {current};
            let history = self.{field}.entry([{key}]).or_insert_with(eqlog_runtime::__private::RelationVersions::new);
            history.publish(current);
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

fn emit_schedule(
    f: &mut std::fmt::Formatter<'_>,
    schedule: &Schedule,
    active: Option<usize>,
    depth: usize,
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
                    f, child, active, depth, root, retain_own, codegen, ctx, selection,
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
            if codegen.strata[s].model.is_some() {
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
            // Moving the full delta at each exit makes debug stack frames grow
            // with the number of strata; swapping only passes references.
            writedoc! {f, "
                if self.__check_condition(condition) {{
                    std::mem::swap(&mut self.__pending_delta, &mut delta);
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

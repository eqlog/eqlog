use std::collections::{BTreeMap, BTreeSet};
use std::fmt::Display;

use indoc::writedoc;

use super::indices::{projection, source_relation};
use super::native_indices;
use super::{
    display_all_index_field_name, display_index_field_name, display_index_type,
    display_module_env_struct_name, display_out_set_field_name, module_env_in_rels,
    module_env_out_rels, RustGenCtx,
};
use crate::flat_eqlog::{FlatInRel, IndexAge, IndexSelection, IndexSpec, Stratum};
use crate::fmt_util::FmtFn;
use crate::ram::{IndexPreparation, NativeIndexPreparation, RamModule, RamProgram};

pub struct Codegen<'s> {
    strata: &'s [Stratum],
    inputs: BTreeMap<FlatInRel, usize>,
    indices: BTreeMap<(FlatInRel, IndexSpec), usize>,
    old_indices: BTreeSet<(FlatInRel, IndexSpec)>,
    preparations: &'s [IndexPreparation],
    native_indices: &'s [NativeIndexPreparation],
}

fn input_key(rel: FlatInRel, mut index: IndexSpec) -> (FlatInRel, IndexSpec) {
    index.age = IndexAge::Old;
    (rel, index)
}

impl<'s> Codegen<'s> {
    pub fn new(strata: &'s [Stratum], program: &'s RamProgram) -> Self {
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
            strata,
            preparations: &program.preparations,
            native_indices: &program.native_indices,
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
            for (rel, i) in &self.inputs {
                let typ = display_index_type(rel, ctx);
                writeln!(
                    f,
                    "__rule_input_{i}: eqlog_runtime::__private::RelationVersions<{typ}>,"
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
                    writeln!(f, "__rule_index_{i}_versions: eqlog_runtime::__private::RelationVersions<{target}>,")?;
                }
            }
            Ok(())
        })
    }

    pub fn init<'a>(&'a self, selection: &'a IndexSelection) -> impl Display + 'a {
        FmtFn(move |f| {
            let count = self.strata.len();
            writeln!(f, "__stratum_initialized: [false; {count}],")?;
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
                writedoc! {f, "
                    fn __run_stratum_{s}(&mut self, delta: &mut ModelDelta) -> bool {{
                        #[allow(unused_mut)]
                        let mut dirty = !self.__stratum_initialized[{s}];
                "}?;
                if !self.preparations[s].propagation.relations.is_empty() {
                    writeln!(f, "self.recompute_model_indices_stratum_{s}();")?;
                }
                for rel in inputs {
                    let i = self.inputs[&rel];
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
                    writedoc! {f, "
                        self.__rule_input_{i}.publish(&self.{old}, &self.{new});
                        let input_{i} = self.__rule_input_{i}.consume({s});
                        dirty |= !input_{i}.new.is_empty();
                    "}?;
                }
                writedoc! {f, "
                    if !dirty {{ return false; }}
                    self.__stratum_initialized[{s}] = true;
                "}?;
                writeln!(f, "{{")?;
                for (rel, index) in &self.preparations[s].support_indices {
                    write!(f, "{}", super::indices::prepare(rel, index, selection, ctx))?;
                }
                for id in &self.preparations[s].native_indices {
                    writeln!(f, "self.__prepare_native_index_{id}();")?;
                    writeln!(
                        f,
                        "let native_input_{id} = self.__native_input_{id}.consume({s});"
                    )?;
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
                    if self.old_indices.contains(&(rel.clone(), index.clone())) {
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
                            let index_{j} = self.__rule_index_{j}_versions.consume_required::<{old}, {new}>({s});
                        "}?;
                    } else {
                        // A delta-only reader does not need the full relation reordered.
                        writeln!(f, "let index_{j} = self.__rule_index_{j}.update(&input_{i}.new, {project});")?;
                    }
                }
                for &m in &stratum.groups {
                    let module = &modules[m];
                    let env = display_module_env_struct_name(module);
                    let name = &module.name;
                    writeln!(f, "let env = {env} {{ phantom: std::marker::PhantomData,")?;
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
            Ok(())
        })
    }

    pub fn close(&self) -> impl Display + '_ {
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
            for (s, stratum) in self.strata.iter().enumerate() {
                if stratum.recursive {
                    writeln!(f, "while self.__run_stratum_{s}(&mut delta) {{")?;
                } else {
                    writeln!(f, "if self.__run_stratum_{s}(&mut delta) {{")?;
                }
                writedoc! {f, "
                    if self.__check_condition(condition) {{
                        self.__pending_delta = delta;
                        return true;
                    }}
                }}
                "}?;
            }
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

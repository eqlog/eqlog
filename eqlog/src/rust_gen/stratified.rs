use std::collections::{BTreeMap, BTreeSet};
use std::fmt::Display;

use indoc::writedoc;

use super::{
    display_index_field_name, display_index_type, display_module_env_struct_name,
    display_out_set_field_name, module_env_in_rels, module_env_out_rels, RustGenCtx,
};
use crate::flat_eqlog::{FlatInRel, IndexAge, IndexSpec, Stratum};
use crate::fmt_util::FmtFn;
use crate::options::ModelMode;
use crate::ram::RamModule;

pub struct Codegen<'s> {
    strata: &'s [Stratum],
    inputs: BTreeMap<(FlatInRel, IndexSpec), usize>,
}

fn input_key(rel: FlatInRel, mut index: IndexSpec) -> (FlatInRel, IndexSpec) {
    index.age = IndexAge::Old;
    (rel, index)
}

impl<'s> Codegen<'s> {
    pub fn new(strata: &'s [Stratum], modules: &[RamModule]) -> Self {
        let inputs: BTreeSet<_> = modules
            .iter()
            .flat_map(module_env_in_rels)
            .map(|(rel, index)| input_key(rel, index))
            .collect();
        Self {
            strata,
            inputs: inputs
                .into_iter()
                .enumerate()
                .map(|(i, key)| (key, i))
                .collect(),
        }
    }

    pub fn fields<'a>(&'a self, ctx: &'a RustGenCtx<'a>) -> impl Display + 'a {
        FmtFn(move |f| {
            let count = self.strata.len();
            writeln!(f, "__stratum_initialized: [bool; {count}],")?;
            for ((rel, _), i) in &self.inputs {
                let typ = display_index_type(rel, ctx);
                writeln!(
                    f,
                    "__rule_input_{i}: eqlog_runtime::__private::RelationVersions<{typ}>,"
                )?;
            }
            Ok(())
        })
    }

    pub fn init(&self) -> impl Display + '_ {
        FmtFn(move |f| {
            let count = self.strata.len();
            writeln!(f, "__stratum_initialized: [false; {count}],")?;
            for i in self.inputs.values() {
                writeln!(
                    f,
                    "__rule_input_{i}: eqlog_runtime::__private::RelationVersions::new(),"
                )?;
            }
            Ok(())
        })
    }

    pub fn methods<'a>(
        &'a self,
        modules: &'a [RamModule],
        ctx: &'a RustGenCtx<'a>,
    ) -> impl Display + 'a {
        FmtFn(move |f| {
            writeln!(f, "fn __publish_rule_inputs(&mut self) {{")?;
            for ((rel, old_index), i) in &self.inputs {
                let new_index = IndexSpec {
                    order: old_index.order.clone(),
                    age: IndexAge::New,
                };
                let old = display_index_field_name(rel, old_index, ctx);
                let new = display_index_field_name(rel, &new_index, ctx);
                let suffix = if ctx.has_shared_indices(rel) {
                    "_all"
                } else {
                    ""
                };
                writeln!(
                    f,
                    "self.__rule_input_{i}.publish(&self.{old}{suffix}, &self.{new}{suffix});"
                )?;
            }
            writeln!(f, "}}")?;
            for (s, stratum) in self.strata.iter().enumerate() {
                let inputs: BTreeSet<_> = stratum
                    .groups
                    .iter()
                    .flat_map(|&i| module_env_in_rels(&modules[i]))
                    .map(|(rel, index)| self.inputs[&input_key(rel, index)])
                    .collect();
                writedoc! {f, "
                    fn __run_stratum_{s}(&mut self, delta: &mut ModelDelta) -> bool {{
                        #[allow(unused_mut)]
                        let mut dirty = !self.__stratum_initialized[{s}];
                "}?;
                for i in inputs {
                    writedoc! {f, "
                        let input_{i} = self.__rule_input_{i}.consume({s});
                        dirty |= !input_{i}.new.is_empty();
                    "}?;
                }
                writedoc! {f, "
                    if !dirty {{ return false; }}
                    self.__stratum_initialized[{s}] = true;
                "}?;
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
                        let i = self.inputs[&input_key(rel.clone(), index.clone())];
                        writeln!(f, "{field}: &input_{i}.{age},")?;
                    }
                    for rel in module_env_out_rels(module) {
                        let field = display_out_set_field_name(&rel, ctx);
                        writeln!(f, "{field}: &mut delta.{field},")?;
                    }
                    writeln!(f, "}}; {name}(env);")?;
                }
                let propagate = match ctx.model_mode() {
                    ModelMode::Native => "self.recompute_model_indices();",
                    ModelMode::Desugared => "",
                };
                writedoc! {f, "
                        self.move_new_to_old();
                        delta.apply_equalities(self);
                        self.__canonicalize_relations();
                        delta.apply_tuples(self);
                        {propagate}
                        self.__publish_rule_inputs();
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
                pub fn close_until(&mut self, condition: impl Fn(&Self) -> bool) -> bool {{
                    self.canonicalize();
                    self.__publish_rule_inputs();
                    if condition(self) {{ return true; }}
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
                    if condition(self) {{
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
                            return false;
                        }}
                        self.canonicalize();
                        self.__publish_rule_inputs();
                        if condition(self) {{
                            self.__pending_delta = delta;
                            return true;
                        }}
                    }}
                }}
            "}
        })
    }
}

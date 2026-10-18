//! Rust emission for desugared models, which store every fact in mutable
//! indexed tables.
//!
//! Rows are stamped with their position in their table's insertion log. A
//! stratum remembers how far it has read each input table, so its old rows
//! are those stamped before that position and its new rows are the rest.

use convert_case::{Case, Casing};
use indoc::{formatdoc, writedoc};
use itertools::Itertools;
use std::collections::{BTreeMap, BTreeSet};
use std::fmt::Display;
use std::sync::Arc;

use super::indices::source_relation;
use super::{
    display_index_field_name, display_module_env_struct_name, display_out_set_field_name,
    display_out_set_type, display_rel, display_type, display_type_fields,
    display_weight_static_name, module_env_in_rels, module_env_out_rels, ElVar, RustGenCtx,
};
use crate::algebra::signature::{FuncId, Signature, TypeId};
use crate::flat_eqlog::{
    iter_flat_rels, FlatInRel, FlatOutRel, FlatRel, IndexAge, IndexSelection, IndexSpec, QuerySpec,
    Schedule,
};
use crate::fmt_util::FmtFn;
use crate::ram::{RamModule, RamProgram};

fn table_indices(
    selection: &IndexSelection,
) -> BTreeMap<FlatInRel, Vec<(FlatInRel, Arc<[usize]>)>> {
    let mut indices: BTreeMap<FlatInRel, Vec<(FlatInRel, Arc<[usize]>)>> = BTreeMap::new();
    for (rel, index) in selection.current_indices() {
        let entry = indices.entry(source_relation(rel)).or_default();
        let key = (rel.clone(), index.order.clone());
        if !entry.contains(&key) {
            entry.push(key);
        }
    }
    indices
}

/// Assigns every index of the selection to a table holding its source relation.
pub(super) struct Tables {
    indices: BTreeMap<FlatInRel, Vec<(FlatInRel, Arc<[usize]>)>>,
    // Indices that rules read through trie views rather than only as deltas.
    viewed: BTreeSet<(FlatInRel, Arc<[usize]>)>,
}

impl Tables {
    pub(super) fn new(
        selection: &IndexSelection,
        program: &RamProgram,
        signature: &Signature,
    ) -> Self {
        let indices = table_indices(selection);
        let viewed = program
            .modules
            .iter()
            .flat_map(module_env_in_rels)
            .filter(|(_, index)| match index.age {
                IndexAge::Old | IndexAge::All => true,
                IndexAge::New => false,
            })
            .map(|(rel, index)| (rel, index.order))
            .chain(signature.iter_funcs().map(|func| {
                let rel = FlatInRel::Rel(FlatRel::Func(func));
                let query = QuerySpec::eval_func(func, signature);
                let order = selection.current_query(&rel, query).order.clone();
                (rel, order)
            }))
            .collect();
        Tables { indices, viewed }
    }

    fn sources(&self) -> impl Iterator<Item = &FlatInRel> {
        self.indices.keys()
    }

    /// The position of an index within the table of its source relation.
    fn position(&self, rel: &FlatInRel, order: &[usize]) -> usize {
        self.indices[&source_relation(rel)]
            .iter()
            .position(|(other, other_order)| other == rel && &other_order[..] == order)
            .expect("every selected index belongs to a table")
    }

    fn init(&self, source: &FlatInRel, ctx: &RustGenCtx<'_>) -> String {
        let specs = self.indices[source]
            .iter()
            .map(|(rel, order)| {
                let (columns, equal): (Vec<usize>, Vec<(usize, usize)>) = match rel {
                    FlatInRel::Rel(_) | FlatInRel::TypeSet(_) => (order.to_vec(), Vec::new()),
                    FlatInRel::RelWithDiagonals { equalities, .. } => {
                        let kept: Vec<usize> = equalities
                            .iter()
                            .enumerate()
                            .filter_map(|(i, &j)| (i == j).then_some(i))
                            .collect();
                        let columns = order.iter().map(|&column| kept[column]).collect();
                        let equal = equalities
                            .iter()
                            .enumerate()
                            .filter_map(|(i, &j)| (i != j).then_some((i, j)))
                            .collect();
                        (columns, equal)
                    }
                    FlatInRel::Equality(_) => unreachable!("equalities have no tuple indices"),
                };
                let columns = columns.iter().join(", ");
                let equal = equal.iter().map(|(i, j)| format!("({i}, {j})")).join(", ");
                let viewed = self.viewed.contains(&(rel.clone(), order.clone()));
                format!("(&[{columns}], &[{equal}], {viewed})")
            })
            .join(", ");
        let arity = source.arity(ctx.signature()).len();
        let constructor = match source {
            FlatInRel::Rel(FlatRel::Func(_)) => "function",
            FlatInRel::Rel(FlatRel::Pred(_) | FlatRel::ModelMember(_))
            | FlatInRel::TypeSet(_)
            | FlatInRel::RelWithDiagonals { .. }
            | FlatInRel::Equality(_) => "new",
        };
        format!("eqlog_runtime::IndexedTable::<{arity}>::{constructor}(&[{specs}])")
    }
}

/// Types whose elements can be equated because a function has two results.
fn function_codomains(ctx: &RustGenCtx<'_>) -> BTreeSet<TypeId> {
    ctx.signature()
        .iter_funcs()
        .map(|func| ctx.signature().func(func).codomain)
        .collect()
}

fn type_snake(typ: TypeId, ctx: &RustGenCtx<'_>) -> String {
    display_type(typ, ctx).to_string().to_case(Case::Snake)
}

/// The field holding the table of a relation or of the elements of a type.
pub(super) fn table_field(source: &FlatInRel, ctx: &RustGenCtx<'_>) -> String {
    match source {
        FlatInRel::Rel(rel) => {
            let rel_snake = display_rel(*rel, ctx).to_case(Case::Snake);
            format!("{rel_snake}_table")
        }
        FlatInRel::TypeSet(typ) => {
            // Element creation and merges address this field by its primary
            // index name.
            let type_snake = display_type(*typ, ctx).to_string().to_case(Case::Snake);
            format!("{type_snake}_order_0")
        }
        FlatInRel::RelWithDiagonals { .. } | FlatInRel::Equality(_) => {
            unreachable!("only relations and types have tables")
        }
    }
}

/// The tables and rule inputs read by one stratum.
struct StratumInputs {
    sources: Vec<FlatInRel>,
    // Rule input and its source position in `sources`.
    reads: Vec<((FlatInRel, IndexSpec), usize)>,
}

/// The output buffers of a stratum's rule modules: each module writes its
/// own buffer per output relation so that modules can run concurrently.
fn output_buffers(groups: &[usize], modules: &[RamModule]) -> Vec<(usize, FlatOutRel)> {
    groups
        .iter()
        .enumerate()
        .flat_map(|(i, &m)| {
            module_env_out_rels(&modules[m])
                .into_iter()
                .map(move |rel| (i, rel))
        })
        .collect()
}

fn stratum_inputs(groups: &[usize], modules: &[RamModule]) -> StratumInputs {
    let reads: BTreeSet<(FlatInRel, IndexSpec)> = groups
        .iter()
        .flat_map(|&m| module_env_in_rels(&modules[m]))
        .collect();
    let sources: Vec<FlatInRel> = reads
        .iter()
        .map(|(rel, _)| source_relation(rel))
        .collect::<BTreeSet<_>>()
        .into_iter()
        .collect();
    let reads = reads
        .into_iter()
        .map(|(rel, index)| {
            let source = sources
                .iter()
                .position(|other| *other == source_relation(&rel))
                .expect("sources contain every read relation");
            ((rel, index), source)
        })
        .collect();
    StratumInputs { sources, reads }
}

pub(super) fn display_struct<'a>(
    name: &'a str,
    ctx: &'a RustGenCtx<'a>,
    tables: &'a Tables,
    program: &'a RamProgram,
) -> impl Display + 'a {
    FmtFn(move |f| {
        let table_fields = tables
            .sources()
            .map(|source| {
                let field = table_field(source, ctx);
                let arity = source.arity(ctx.signature()).len();
                format!("{field}: eqlog_runtime::IndexedTable<{arity}>,")
            })
            .join("\n");
        let element_index_fields = ctx
            .signature()
            .iter_types()
            .map(|typ| {
                let field = occurrences_field(typ, ctx);
                format!("{field}: eqlog_runtime::Occurrences,")
            })
            .join("\n");
        let type_fields = ctx
            .signature()
            .iter_types()
            .map(|typ| display_type_fields(typ, ctx))
            .format("\n");
        let functional_fields = function_codomains(ctx)
            .into_iter()
            .map(|typ| {
                let name = type_snake(typ, ctx);
                format!("__functional_{name}: Vec<[u32; 2]>,")
            })
            .join("\n");
        let strata = &program.schedule.strata;
        let count = strata.len();
        let since_fields = strata
            .iter()
            .enumerate()
            .map(|(s, stratum)| {
                let len = stratum_inputs(&stratum.groups, &program.modules)
                    .sources
                    .len();
                format!("__since_{s}: [u32; {len}],")
            })
            .join("\n");
        let output_fields = strata
            .iter()
            .enumerate()
            .flat_map(|(s, stratum)| {
                output_buffers(&stratum.groups, &program.modules)
                    .into_iter()
                    .map(move |(i, rel)| {
                        let field = display_out_set_field_name(&rel, ctx);
                        let typ = display_out_set_type(&rel, ctx);
                        format!("__out_{s}_{i}_{field}: {typ},")
                    })
            })
            .join("\n");
        writedoc! {f, "
            /// A model of the `{name}` theory.
            pub struct {name} {{
                {table_fields}
                {element_index_fields}
                {type_fields}
                __allocated: bool,
                __closed: bool,
                __pending_delta: ModelDelta,
                {functional_fields}
                __stratum_initialized: [bool; {count}],
                {since_fields}
                {output_fields}
            }}
            type Model = {name};
        "}
    })
}

pub(super) fn display_new_fn<'a>(
    ctx: &'a RustGenCtx<'a>,
    tables: &'a Tables,
    program: &'a RamProgram,
) -> impl Display + 'a {
    FmtFn(move |f| {
        let tables_init = tables
            .sources()
            .map(|source| {
                let field = table_field(source, ctx);
                let init = tables.init(source, ctx);
                format!("{field}: {init},")
            })
            .join("\n");
        let element_indices = ctx
            .signature()
            .iter_types()
            .map(|typ| {
                let field = occurrences_field(typ, ctx);
                format!("{field}: eqlog_runtime::Occurrences::default(),")
            })
            .join("\n");
        let types = ctx
            .signature()
            .iter_types()
            .map(|typ| {
                let type_snake = display_type(typ, ctx).to_string().to_case(Case::Snake);
                format!(
                    "{type_snake}_equalities: Unification::new(),\n{type_snake}_weights: Vec::new(),\n{type_snake}_uprooted: Vec::new(),"
                )
            })
            .join("\n");
        let functional = function_codomains(ctx)
            .into_iter()
            .map(|typ| {
                let name = type_snake(typ, ctx);
                format!("__functional_{name}: Vec::new(),")
            })
            .join("\n");
        let strata = &program.schedule.strata;
        let count = strata.len();
        let since = strata
            .iter()
            .enumerate()
            .map(|(s, stratum)| {
                let len = stratum_inputs(&stratum.groups, &program.modules)
                    .sources
                    .len();
                format!("__since_{s}: [0; {len}],")
            })
            .join("\n");
        let outputs = strata
            .iter()
            .enumerate()
            .flat_map(|(s, stratum)| {
                output_buffers(&stratum.groups, &program.modules)
                    .into_iter()
                    .map(move |(i, rel)| {
                        let field = display_out_set_field_name(&rel, ctx);
                        format!("__out_{s}_{i}_{field}: Vec::new(),")
                    })
            })
            .join("\n");
        writedoc! {f, "
            /// Creates an empty model.
            #[allow(dead_code)]
            pub fn new() -> Self {{
                Self {{
                    {tables_init}
                    {element_indices}
                    {types}
                    __allocated: false,
                    __closed: false,
                    __pending_delta: ModelDelta::new(),
                    {functional}
                    __stratum_initialized: [false; {count}],
                    {since}
                    {outputs}
                }}
            }}
        "}
    })
}

pub(super) fn display_strata<'a>(
    program: &'a RamProgram,
    tables: &'a Tables,
    ctx: &'a RustGenCtx<'a>,
) -> impl Display + 'a {
    FmtFn(move |f| {
        let fields: Vec<_> = tables
            .sources()
            .map(|source| table_field(source, ctx))
            .collect();
        let sync_tasks = fields
            .iter()
            .map(|field| format!("work += self.{field}.sync_tasks(&mut tasks);"))
            .join("\n");
        let finish_sync = fields
            .iter()
            .map(|field| format!("self.{field}.finish_sync();"))
            .join("\n");
        let set_deferred = fields
            .iter()
            .map(|field| format!("self.{field}.set_deferred(deferred);"))
            .join("\n");
        writedoc! {f, "
            /// Brings the tries of all tables up to date, one task per trie.
            #[allow(unused_mut)]
            fn __sync_tables(&mut self) {{
                {{
                    let mut tasks: Vec<eqlog_runtime::Task<'_>> = Vec::new();
                    let mut work = 0;
                    {sync_tasks}
                    eqlog_runtime::run_tasks(work, tasks);
                }}
                {finish_sync}
            }}

            /// Closing defers trie updates to the synchronization before
            /// each stratum; outside, tries are updated row by row.
            #[allow(unused_variables)]
            fn __set_tables_deferred(&mut self, deferred: bool) {{
                self.__sync_tables();
                {set_deferred}
            }}
        "}?;
        let modules = &program.modules;
        for (s, stratum) in program.schedule.strata.iter().enumerate() {
            let inputs = stratum_inputs(&stratum.groups, modules);
            writedoc! {f, "
                #[allow(unused_variables)]
                #[inline(never)]
                fn __run_stratum_{s}(&mut self, delta: &mut ModelDelta) -> bool {{
                    let since = self.__since_{s};
            "}?;
            let now = inputs
                .sources
                .iter()
                .map(|source| {
                    let field = table_field(source, ctx);
                    format!("self.{field}.log_len()")
                })
                .join(", ");
            writeln!(f, "let now: [u32; {}] = [{now}];", inputs.sources.len())?;
            let changed = inputs
                .sources
                .iter()
                .enumerate()
                .map(|(i, source)| {
                    let field = table_field(source, ctx);
                    format!("|| (since[{i}] < now[{i}] && self.{field}.changed_since(since[{i}]))")
                })
                .join(" ");
            writedoc! {f, "
                if !(!self.__stratum_initialized[{s}] {changed}) {{
                    return false;
                }}
                self.__stratum_initialized[{s}] = true;
                self.__since_{s} = now;
                self.__sync_tables();
                let work: usize = now.iter().zip(&since).map(|(now, since)| (now - since) as usize).sum();
            "}?;
            let deltas: Vec<_> = inputs
                .reads
                .iter()
                .enumerate()
                .filter(|(_, ((_, index), _))| match index.age {
                    IndexAge::New => true,
                    IndexAge::Old | IndexAge::All => false,
                })
                .collect();
            for (k, ((_, index), _)) in &deltas {
                let width = index.order.len();
                writeln!(f, "let mut delta_{k}: Vec<[u32; {width}]> = Vec::new();")?;
            }
            if !deltas.is_empty() {
                writeln!(
                    f,
                    "{{ let mut tasks: Vec<eqlog_runtime::Task<'_>> = Vec::new();"
                )?;
                for (k, ((rel, index), source)) in &deltas {
                    let field = table_field(&inputs.sources[*source], ctx);
                    let position = tables.position(rel, &index.order);
                    let width = index.order.len();
                    writedoc! {f, "
                        if since[{source}] < now[{source}] {{
                            let (table, delta, since) = (&self.{field}, &mut delta_{k}, since[{source}]);
                            tasks.push(Box::new(move || *delta = table.delta::<{width}>({position}, since)));
                        }}
                    "}?;
                }
                writeln!(f, "eqlog_runtime::run_tasks(work, tasks); }}")?;
            }
            let buffers = output_buffers(&stratum.groups, modules);
            for (i, rel) in &buffers {
                let field = display_out_set_field_name(rel, ctx);
                writeln!(
                    f,
                    "let mut __out_{i}_{field} = std::mem::take(&mut self.__out_{s}_{i}_{field});"
                )?;
            }
            let count = stratum.groups.len();
            writedoc! {f, "
                {{
                let mut tasks: Vec<eqlog_runtime::Task<'_>> = Vec::with_capacity({count});
            "}?;
            for (i, &m) in stratum.groups.iter().enumerate() {
                let module = &modules[m];
                let env = display_module_env_struct_name(module);
                let name = &module.name;
                writeln!(f, "let env = {env} {{ phantom: std::marker::PhantomData,")?;
                for (rel, index) in module_env_in_rels(module) {
                    let env_field = display_index_field_name(&rel, &index, ctx);
                    let k = inputs
                        .reads
                        .iter()
                        .position(|(read, _)| read.0 == rel && read.1 == index)
                        .expect("stratum inputs contain module inputs");
                    let source = inputs.reads[k].1;
                    let field = table_field(&inputs.sources[source], ctx);
                    let position = tables.position(&rel, &index.order);
                    match index.age {
                        IndexAge::Old => writeln!(
                            f,
                            "{env_field}: self.{field}.view_before({position}, since[{source}]),"
                        )?,
                        IndexAge::All => {
                            writeln!(f, "{env_field}: self.{field}.view({position}),")?
                        }
                        IndexAge::New => {
                            writeln!(f, "{env_field}: eqlog_runtime::RowsView::new(&delta_{k}),")?
                        }
                    }
                }
                for rel in module_env_out_rels(module) {
                    let field = display_out_set_field_name(&rel, ctx);
                    writeln!(f, "{field}: &mut __out_{i}_{field},")?;
                }
                writeln!(f, "}}; tasks.push(Box::new(move || {name}(env)));")?;
            }
            writeln!(f, "eqlog_runtime::run_tasks(work, tasks);")?;
            writeln!(f, "}}")?;
            let outputs: BTreeSet<_> = buffers.iter().map(|(_, rel)| rel).collect();
            let producers = |output: &FlatOutRel| -> Vec<usize> {
                buffers
                    .iter()
                    .filter(|(_, rel)| rel == output)
                    .map(|(i, _)| *i)
                    .collect()
            };
            let mut equalities = Vec::new();
            for &output in &outputs {
                match output {
                    FlatOutRel::Equality(typ) => {
                        let name = display_type(*typ, ctx).to_string().to_case(Case::Snake);
                        let field = display_out_set_field_name(output, ctx);
                        for i in producers(output) {
                            writedoc! {f, "
                                for [lhs, rhs] in __out_{i}_{field}.drain(..) {{
                                    self.__equate_{name}(lhs.into(), rhs.into());
                                }}
                            "}?;
                        }
                        equalities.push(format!("!self.{name}_uprooted.is_empty()"));
                    }
                    FlatOutRel::Rel(_) | FlatOutRel::FuncDomain(_) => {}
                }
            }
            if !equalities.is_empty() {
                let changed = equalities.join(" || ");
                writeln!(f, "if {changed} {{ self.__canonicalize_relations(); }}")?;
            }
            for &output in &outputs {
                let field = display_out_set_field_name(output, ctx);
                match output {
                    FlatOutRel::Rel(rel) => {
                        let insert = ctx.internal_insert_name(*rel);
                        let args = (0..rel.arity(ctx.signature()).len())
                            .map(|i| format!("arg{i}"))
                            .collect::<Vec<_>>();
                        let converted = args.iter().map(|arg| format!("{arg}.into()")).join(", ");
                        let args = args.join(", ");
                        let table = table_field(&FlatInRel::Rel(*rel), ctx);
                        for i in producers(output) {
                            // Tables only hold canonical rows, so a row found as
                            // derived needs no canonicalization before skipping it.
                            writedoc! {f, "
                                for [{args}] in __out_{i}_{field}.drain(..) {{
                                    if !self.{table}.contains([{args}]) {{ self.{insert}({converted}); }}
                                }}
                            "}?;
                        }
                    }
                    // Functions are defined at the next allocation barrier.
                    FlatOutRel::FuncDomain(_) => {
                        for i in producers(output) {
                            writeln!(f, "delta.{field}.append(&mut __out_{i}_{field});")?;
                        }
                    }
                    FlatOutRel::Equality(_) => {}
                }
            }
            for (i, rel) in &buffers {
                let field = display_out_set_field_name(rel, ctx);
                writeln!(f, "self.__out_{s}_{i}_{field} = __out_{i}_{field};")?;
            }
            writeln!(f, "self.__normalize_functions();")?;
            writeln!(f, "true }}")?;
        }
        Ok(())
    })
}

fn emit_schedule(
    f: &mut std::fmt::Formatter<'_>,
    schedule: &Schedule,
    active: Option<usize>,
    depth: usize,
) -> std::fmt::Result {
    match schedule {
        Schedule::Sequence(children) | Schedule::Independent(children) => {
            for child in children {
                emit_schedule(f, child, active, depth)?;
            }
        }
        Schedule::Rules(id) => {
            let s = id.0;
            writeln!(f, "if self.__run_stratum_{s}(&mut delta) {{")?;
            if let Some(active) = active {
                writeln!(f, "active_{active} = true;")?;
            }
            writedoc! {f, "
                if self.__check_condition(condition) {{
                    std::mem::swap(&mut self.__pending_delta, &mut delta);
                    return true;
                }}
            }}
            "}?;
        }
        Schedule::Saturate(body) => {
            writeln!(f, "loop {{ let mut active_{depth} = false;")?;
            emit_schedule(f, body, Some(depth), depth + 1)?;
            writeln!(f, "if !active_{depth} {{ break; }}")?;
            if let Some(active) = active {
                writeln!(f, "active_{active} = true;")?;
            }
            writeln!(f, "}}")?;
        }
        Schedule::ModelComponents { .. } => {
            unreachable!("desugared models have no model-scoped strata")
        }
    }
    Ok(())
}

pub(super) fn display_close<'a>(
    program: &'a RamProgram,
    ctx: &'a RustGenCtx<'a>,
) -> impl Display + 'a {
    FmtFn(move |f| {
        let codomains = function_codomains(ctx);
        let equate = codomains
            .iter()
            .map(|&typ| {
                let name = type_snake(typ, ctx);
                format!(
                    "for [lhs, rhs] in std::mem::take(&mut self.__functional_{name}) {{ pending = true; self.__equate_{name}(lhs.into(), rhs.into()); }}"
                )
            })
            .join("\n");
        let uprooted = codomains
            .iter()
            .map(|&typ| {
                let name = type_snake(typ, ctx);
                format!("|| !self.{name}_uprooted.is_empty()")
            })
            .join(" ");
        writedoc! {f, "
            /// Equates the results that a function has for the same arguments
            /// until all function graphs are functional again. Returns whether
            /// this merged any elements.
            #[allow(unused_mut)]
            fn __normalize_functions(&mut self) -> bool {{
                let mut changed = false;
                loop {{
                    let mut pending = false;
                    {equate}
                    if !pending {{
                        return changed;
                    }}
                    if false {uprooted} {{
                        changed = true;
                        self.__canonicalize_relations();
                    }}
                }}
            }}
        "}?;
        writedoc! {f, "
            /// Closes the model until the condition holds or all rules are satisfied.
            /// Depending on the axioms, this may run indefinitely.
            #[allow(dead_code)]
            pub fn close_until(&mut self, condition: impl Fn(&Self) -> bool) -> bool {{
                self.__close_until(Some(&condition))
            }}

            fn __close_until(&mut self, condition: Option<&dyn Fn(&Self) -> bool>) -> bool {{
                self.__set_tables_deferred(true);
                let result = self.__close_until_deferred(condition);
                self.__set_tables_deferred(false);
                result
            }}

            fn __close_until_deferred(&mut self, condition: Option<&dyn Fn(&Self) -> bool>) -> bool {{
                if self.__closed {{
                    return condition.is_some_and(|condition| condition(self));
                }}
                self.__canonicalize_relations();
                self.__normalize_functions();
                if self.__check_condition(condition) {{ return true; }}
                let mut delta = std::mem::replace(&mut self.__pending_delta, ModelDelta::new());
                loop {{
        "}?;
        emit_schedule(f, &program.schedule.body, None, 0)?;
        writedoc! {f, "
                    self.__allocated = false;
                    // Defining functions evaluates them through the tries.
                    self.__set_tables_deferred(false);
                    delta.apply_func_defs(self);
                    self.__set_tables_deferred(true);
                    let normalized = self.__normalize_functions();
                    if !self.__allocated && !normalized {{
                        std::mem::swap(&mut self.__pending_delta, &mut delta);
                        self.canonicalize();
                        self.__closed = true;
                        return false;
                    }}
                    self.__canonicalize_relations();
                    self.__normalize_functions();
                }}
            }}
        "}
    })
}

/// The tag that occurrence entries carry for rows of a relation.
fn relation_tag(rel: FlatRel, ctx: &RustGenCtx<'_>) -> usize {
    iter_flat_rels(ctx.signature())
        .position(|other| other == rel)
        .expect("relations are flat relations of the signature")
}

/// The field listing, for each element of a type, the rows it occurs in.
pub(super) fn occurrences_field(typ: TypeId, ctx: &RustGenCtx<'_>) -> String {
    let name = type_snake(typ, ctx);
    format!("__occurrences_{name}")
}

/// Binds `occurrence` to the entry of the row just inserted into a table.
pub(super) fn display_occurrence(rel: FlatRel, ctx: &RustGenCtx<'_>) -> String {
    let field = table_field(&FlatInRel::Rel(rel), ctx);
    let tag = relation_tag(rel, ctx);
    format!("let occurrence = u64::from(self.{field}.log_len() - 1) | ({tag} << 32);")
}

/// Rows of a relation in which `arg{position}` occurs, including rows that
/// have since been rewritten.
pub(super) fn display_occurrence_rows(
    rel: FlatRel,
    typ: TypeId,
    position: usize,
    ctx: &RustGenCtx<'_>,
) -> String {
    let occurrences = occurrences_field(typ, ctx);
    let field = table_field(&FlatInRel::Rel(rel), ctx);
    let tag = relation_tag(rel, ctx);
    format!(
        "self.{occurrences}.iter(arg{position}.0).filter(|&entry| entry >> 32 == {tag}).map(|entry| self.{field}.row_at(entry as u32))"
    )
}

pub(super) fn display_canonicalize_fn<'a>(ctx: &'a RustGenCtx<'a>) -> impl Display + 'a {
    FmtFn(move |f| {
        let rewrite_types = ctx
            .signature()
            .iter_types()
            .map(|typ| {
                let name = type_snake(typ, ctx);
                let occurrences = occurrences_field(typ, ctx);
                formatdoc! {"
                    for el in std::mem::take(&mut self.{name}_uprooted) {{
                        rewritten = true;
                        let mut list = self.{occurrences}.take(el.0);
                        while let Some(entry) = self.{occurrences}.pop(&mut list) {{
                            self.__rewrite_row(entry);
                        }}
                    }}
                "}
            })
            .join("\n");
        let arms = iter_flat_rels(ctx.signature())
            .map(|rel| {
                let tag = relation_tag(rel, ctx);
                let name = display_rel(rel, ctx).to_case(Case::Snake);
                format!("{tag} => self.__rewrite_{name}(stamp),")
            })
            .join("\n");
        writedoc! {f, "
            /// Rewrites facts using the current equality representatives without running rules.
            /// Consumer checkpoints retain pending matches after equality replacement.
            /// Element handles remain valid, and repeated calls preserve pending work.
            #[allow(dead_code)]
            pub fn canonicalize(&mut self) {{
                self.__canonicalize_relations();
                self.__sync_tables();
            }}

            #[allow(unused_mut)]
            fn __canonicalize_relations(&mut self) {{
                loop {{
                    let mut rewritten = false;
                    {rewrite_types}
                    if !rewritten {{
                        return;
                    }}
                }}
            }}

            /// Replaces a row by its canonical form unless it was removed since
            /// the occurrence was recorded.
            #[inline(never)]
            #[allow(unused_variables)]
            fn __rewrite_row(&mut self, entry: u64) {{
                let stamp = entry as u32;
                match entry >> 32 {{
                    {arms}
                    _ => unreachable!(\"occurrence tags name relations\"),
                }}
            }}
        "}?;
        for rel in iter_flat_rels(ctx.signature()) {
            let name = display_rel(rel, ctx).to_case(Case::Snake);
            let field = table_field(&FlatInRel::Rel(rel), ctx);
            let supported_insert = ctx.supported_insert_name(rel);
            let arity = rel.arity(ctx.signature());
            let args = (0..arity.len()).map(ElVar::from).collect::<Vec<_>>();
            let reduce_weights = arity
                .iter()
                .enumerate()
                .map(|(i, &typ)| {
                    let type_snake = type_snake(typ, ctx);
                    let weight = display_weight_static_name(rel, ctx);
                    format!(
                        "let weight{i}: &mut usize = &mut self.{type_snake}_weights[el{i} as usize];\n*weight{i} = weight{i}.saturating_sub({weight});"
                    )
                })
                .join("\n");
            let insert_args = args
                .iter()
                .zip(arity.iter())
                .map(|(arg, &typ)| {
                    let type_camel = display_type(typ, ctx).to_string().to_case(Case::UpperCamel);
                    format!("{type_camel}({arg})")
                })
                .join(", ");
            let args = args.iter().join(", ");
            writedoc! {f, "
                #[inline(never)]
                #[allow(unused_variables)]
                fn __rewrite_{name}(&mut self, stamp: u32) {{
                    let Some([{args}]) = self.{field}.remove_stamped(stamp) else {{
                        return;
                    }};
                    {reduce_weights}
                    self.{supported_insert}(true, {insert_args});
                }}
            "}?;
        }
        Ok(())
    })
}

/// The table operations of an internal insertion: unpacked arguments must be
/// canonical, and the statements return early if the row is present.
pub(super) fn display_insert_rows<'a>(
    rel: FlatRel,
    args: &'a [ElVar],
    ctx: &'a RustGenCtx<'a>,
) -> impl Display + 'a {
    FmtFn(move |f| {
        let field = table_field(&FlatInRel::Rel(rel), ctx);
        let row = args.iter().join(", ");
        match rel {
            FlatRel::Func(func) => {
                let codomain = type_snake(ctx.signature().func(func).codomain, ctx);
                let result = args.last().expect("a function graph has a result column");
                writedoc! {f, "
                    match self.{field}.insert_function([{row}]) {{
                        eqlog_runtime::FunctionInsert::Present => return,
                        eqlog_runtime::FunctionInsert::Inserted => {{}}
                        eqlog_runtime::FunctionInsert::Conflict(other) => {{
                            self.__functional_{codomain}.push([{result}, other]);
                        }}
                    }}
                "}
            }
            FlatRel::Pred(_) | FlatRel::ModelMember(_) => writedoc! {f, "
                if !self.{field}.insert([{row}]) {{
                    return;
                }}
            "},
        }
    })
}

/// Statements inserting an imported `row` into its table.
pub(super) fn display_import_row(rel: FlatRel, ctx: &RustGenCtx<'_>) -> String {
    let field = table_field(&FlatInRel::Rel(rel), ctx);
    match rel {
        FlatRel::Func(func) => {
            let codomain = type_snake(ctx.signature().func(func).codomain, ctx);
            let result = rel.arity(ctx.signature()).len() - 1;
            formatdoc! {"
                match self.{field}.insert_function(row) {{
                    eqlog_runtime::FunctionInsert::Present | eqlog_runtime::FunctionInsert::Inserted => {{}}
                    eqlog_runtime::FunctionInsert::Conflict(other) => {{
                        self.__functional_{codomain}.push([row[{result}], other]);
                    }}
                }}
            "}
        }
        FlatRel::Pred(_) | FlatRel::ModelMember(_) => format!("self.{field}.insert(row);"),
    }
}

pub(super) fn display_holds_expr(rel: FlatRel, ctx: &RustGenCtx<'_>) -> String {
    let field = table_field(&FlatInRel::Rel(rel), ctx);
    let args = (0..rel.arity(ctx.signature()).len())
        .map(|i| format!("arg{i}.0"))
        .join(", ");
    format!("self.{field}.contains([{args}])")
}

/// Statements binding `result` to the value of a function on `arg{i}`.
pub(super) fn display_eval_body(
    func: FuncId,
    selection: &IndexSelection,
    ctx: &RustGenCtx<'_>,
) -> String {
    let rel = FlatInRel::Rel(FlatRel::Func(func));
    let index = selection.current_query(&rel, QuerySpec::eval_func(func, ctx.signature()));
    let field = table_field(&rel, ctx);
    let position = table_indices(selection)[&rel]
        .iter()
        .position(|(other, order)| *other == rel && *order == index.order)
        .expect("the evaluation index belongs to the function's table");
    let gets = index.order[..index.order.len() - 1]
        .iter()
        .map(|i| format!("let set = set.get(arg{i}.0)?;"))
        .join("\n");
    format!(
        "let set = self.{field}.view({position});\n{gets}\nlet (result, _) = set.iter_restrictions().next()?;"
    )
}

/// The table whose `iter` yields the rows of a relation in sorted order.
pub(super) fn display_iter_expr(rel: FlatRel, ctx: &RustGenCtx<'_>) -> String {
    let field = table_field(&FlatInRel::Rel(rel), ctx);
    format!("self.{field}")
}

/// Rows of the membership relation of `member_type` whose member is `arg`,
/// as tuples of their parents.
pub(super) fn display_member_parent_rows(
    member_type: TypeId,
    arg: &ElVar,
    ctx: &RustGenCtx<'_>,
) -> String {
    let rel = FlatInRel::Rel(FlatRel::ModelMember(member_type));
    let field = table_field(&rel, ctx);
    let parent_types = &ctx.signature().type_(member_type).parents;
    let member = parent_types.len();
    let unpack = (0..parent_types.len())
        .map(|i| format!("parent{i}"))
        .chain(std::iter::once("_".to_string()))
        .join(", ");
    let parents = parent_types
        .iter()
        .enumerate()
        .map(|(i, &typ)| {
            let type_name = display_type(typ, ctx).to_string().to_case(Case::UpperCamel);
            format!("{type_name}::from(parent{i})")
        })
        .join(", ");
    format!(
        "self.{field}.iter().filter(move |row| row[{member}] == {arg}.0).map(|[{unpack}]| ({parents}))"
    )
}

//! Rust emission for desugared models, which store every fact in mutable
//! indexed tables.
//!
//! Rows are stamped with their position in their table's insertion log. A
//! stratum remembers how far it has read each input table, so its old rows
//! are those stamped before that position and its new rows are the rest.

use convert_case::{Case, Casing};
use indoc::writedoc;
use itertools::Itertools;
use std::collections::{BTreeMap, BTreeSet};
use std::fmt::Display;
use std::sync::Arc;

use super::indices::source_relation;
use super::{
    display_element_index_field_name, display_index_field_name, display_module_env_struct_name,
    display_out_set_field_name, display_rel, display_type, display_type_fields,
    display_weight_static_name, module_env_in_rels, module_env_out_rels, ElVar, RustGenCtx,
};
use crate::algebra::signature::TypeId;
use crate::flat_eqlog::{
    iter_flat_rels, FlatInRel, FlatOutRel, FlatRel, IndexAge, IndexSelection, IndexSpec, QuerySpec,
    Schedule,
};
use crate::fmt_util::FmtFn;
use crate::ram::{RamModule, RamProgram};

/// Assigns every index of the selection to a table holding its source relation.
pub(super) struct Tables {
    indices: BTreeMap<FlatInRel, Vec<(FlatInRel, Arc<[usize]>)>>,
}

impl Tables {
    pub(super) fn new(selection: &IndexSelection) -> Self {
        let mut indices: BTreeMap<FlatInRel, Vec<(FlatInRel, Arc<[usize]>)>> = BTreeMap::new();
        for (rel, index) in selection.current_indices() {
            let entry = indices.entry(source_relation(rel)).or_default();
            let key = (rel.clone(), index.order.clone());
            if !entry.contains(&key) {
                entry.push(key);
            }
        }
        Tables { indices }
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
                format!("(&[{columns}], &[{equal}])")
            })
            .join(", ");
        let arity = source.arity(ctx.signature()).len();
        format!("eqlog_runtime::IndexedTable::<{arity}>::new(&[{specs}])")
    }
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

/// An expression for a view of all rows through the index serving `query`.
fn query_view(
    rel: FlatRel,
    query: QuerySpec,
    selection: &IndexSelection,
    tables: &Tables,
    ctx: &RustGenCtx<'_>,
) -> (String, Arc<[usize]>) {
    let flat = FlatInRel::Rel(rel);
    let index = selection.current_query(&flat, query);
    let field = table_field(&flat, ctx);
    let position = tables.position(&flat, &index.order);
    (
        format!("self.{field}.view({position}, 0, u32::MAX)"),
        index.order.clone(),
    )
}

/// The tables and rule inputs read by one stratum.
struct StratumInputs {
    sources: Vec<FlatInRel>,
    // Rule input and its source position in `sources`.
    reads: Vec<((FlatInRel, IndexSpec), usize)>,
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
        let element_index_fields = iter_flat_rels(ctx.signature())
            .flat_map(|rel| {
                let arity = rel.arity(ctx.signature());
                let arity_len = arity.len();
                arity
                    .into_iter()
                    .collect::<BTreeSet<TypeId>>()
                    .into_iter()
                    .map(move |typ| {
                        let field = display_element_index_field_name(rel, typ, ctx);
                        format!("{field}: BTreeMap<u32, Vec<[u32; {arity_len}]>>,")
                    })
            })
            .join("\n");
        let type_fields = ctx
            .signature()
            .iter_types()
            .map(|typ| display_type_fields(typ, ctx))
            .format("\n");
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
        writedoc! {f, "
            /// A model of the `{name}` theory.
            pub struct {name} {{
                {table_fields}
                {element_index_fields}
                {type_fields}
                __allocated: bool,
                __closed: bool,
                __pending_delta: ModelDelta,
                __stratum_initialized: [bool; {count}],
                {since_fields}
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
        let element_indices = iter_flat_rels(ctx.signature())
            .flat_map(|rel| {
                rel.arity(ctx.signature())
                    .into_iter()
                    .collect::<BTreeSet<TypeId>>()
                    .into_iter()
                    .map(move |typ| {
                        let field = display_element_index_field_name(rel, typ, ctx);
                        format!("{field}: BTreeMap::new(),")
                    })
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
                    __stratum_initialized: [false; {count}],
                    {since}
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
            "}?;
            for (k, ((rel, index), source)) in inputs.reads.iter().enumerate() {
                match index.age {
                    IndexAge::New => {}
                    IndexAge::Old | IndexAge::All => continue,
                }
                let field = table_field(&inputs.sources[*source], ctx);
                let position = tables.position(rel, &index.order);
                let width = index.order.len();
                writedoc! {f, "
                    let delta_{k}: Vec<[u32; {width}]> = if since[{source}] < now[{source}] {{
                        self.{field}.delta::<{width}>({position}, since[{source}])
                    }} else {{
                        Vec::new()
                    }};
                "}?;
            }
            writeln!(f, "{{")?;
            for &m in &stratum.groups {
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
                            "{env_field}: self.{field}.view({position}, 0, since[{source}]),"
                        )?,
                        IndexAge::All => writeln!(
                            f,
                            "{env_field}: self.{field}.view({position}, 0, u32::MAX),"
                        )?,
                        IndexAge::New => {
                            writeln!(f, "{env_field}: eqlog_runtime::RowsView::new(&delta_{k}),")?
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
                        let converted = args.iter().map(|arg| format!("{arg}.into()")).join(", ");
                        let args = args.join(", ");
                        writedoc! {f, "
                            delta.{field}.sort_unstable();
                            delta.{field}.dedup();
                            for [{args}] in delta.{field}.drain(..) {{ self.{insert}({converted}); }}
                        "}?;
                    }
                    FlatOutRel::Equality(_) | FlatOutRel::FuncDomain(_) => {}
                }
            }
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

pub(super) fn display_close<'a>(program: &'a RamProgram) -> impl Display + 'a {
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
        emit_schedule(f, &program.schedule.body, None, 0)?;
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

fn row_args(len: usize) -> Vec<ElVar> {
    (0..len).map(ElVar::from).collect()
}

/// Rows of the relation, unpacked into `el{i}` variables, that contain an
/// uprooted element are removed and inserted again with representatives.
fn display_canonicalize_rel_block<'a>(rel: FlatRel, ctx: &'a RustGenCtx<'a>) -> impl Display + 'a {
    FmtFn(move |f| {
        let supported_insert = ctx.supported_insert_name(rel);
        let arity = rel.arity(ctx.signature());
        let arity_len = arity.len();
        let args = row_args(arity_len);
        let field = table_field(&FlatInRel::Rel(rel), ctx);
        let collect = arity
            .iter()
            .copied()
            .collect::<BTreeSet<_>>()
            .into_iter()
            .map(|typ| {
                let type_snake = display_type(typ, ctx).to_string().to_case(Case::Snake);
                let element_index = display_element_index_field_name(rel, typ, ctx);
                format!(
                    "for el in self.{type_snake}_uprooted.iter().copied() {{ if let Some(rows) = self.{element_index}.remove(&el.0) {{ non_canonical_rows.push(rows); }} }}"
                )
            })
            .join("\n");
        let reduce_weights = arity
            .iter()
            .enumerate()
            .map(|(i, &typ)| {
                let type_snake = display_type(typ, ctx).to_string().to_case(Case::Snake);
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
            #[allow(unused_mut)]
            let mut non_canonical_rows: Vec<Vec<[u32; {arity_len}]>> = Vec::new();
            {collect}
            for [{args}] in non_canonical_rows.into_iter().flatten() {{
                if !self.{field}.remove([{args}]) {{
                    continue;
                }}
                {reduce_weights}
                self.{supported_insert}(true, {insert_args});
            }}
        "}
    })
}

pub(super) fn display_canonicalize_fn<'a>(ctx: &'a RustGenCtx<'a>) -> impl Display + 'a {
    FmtFn(move |f| {
        let rels: Vec<FlatRel> = iter_flat_rels(ctx.signature())
            .filter(|rel| rel.is_model_membership_relation())
            .chain(
                iter_flat_rels(ctx.signature()).filter(|rel| !rel.is_model_membership_relation()),
            )
            .collect();
        let calls = rels
            .iter()
            .map(|&rel| {
                let name = display_rel(rel, ctx).to_case(Case::Snake);
                format!("self.__canonicalize_rows_{name}();")
            })
            .join("\n");
        let clear_uprooted = ctx
            .signature()
            .iter_types()
            .map(|typ| {
                let type_snake = display_type(typ, ctx).to_string().to_case(Case::Snake);
                format!("self.{type_snake}_uprooted.clear();")
            })
            .join("\n");
        writedoc! {f, "
            /// Rewrites facts using the current equality representatives without running rules.
            /// Consumer checkpoints retain pending matches after equality replacement.
            /// Element handles remain valid, and repeated calls preserve pending work.
            #[allow(dead_code)]
            pub fn canonicalize(&mut self) {{
                self.__canonicalize_relations();
            }}

            fn __canonicalize_relations(&mut self) {{
                {calls}
                {clear_uprooted}
            }}
        "}?;
        for rel in rels {
            let name = display_rel(rel, ctx).to_case(Case::Snake);
            let block = display_canonicalize_rel_block(rel, ctx);
            writedoc! {f, "
                #[inline(never)]
                fn __canonicalize_rows_{name}(&mut self) {{
                    {block}
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
        let args = args.iter().join(", ");
        writedoc! {f, "
            if !self.{field}.insert([{args}]) {{
                return;
            }}
        "}
    })
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
    rel: FlatRel,
    query: QuerySpec,
    selection: &IndexSelection,
    tables: &Tables,
    ctx: &RustGenCtx<'_>,
) -> String {
    let (view, order) = query_view(rel, query, selection, tables, ctx);
    let gets = order[..order.len() - 1]
        .iter()
        .map(|i| format!("let set = set.get(arg{i}.0)?;"))
        .join("\n");
    format!("let set = {view};\n{gets}\nlet (result, _) = set.iter_restrictions().next()?;")
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

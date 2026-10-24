//! Each stratum needs its own insertion-log cursor so consumers cannot
//! consume each other's pending matches.

use convert_case::{Case, Casing};
use indoc::{formatdoc, writedoc};
use itertools::Itertools;
use std::fmt::Display;

use super::{
    display_index_field_name, display_module_env_struct_name, display_out_rows_field_name,
    display_out_set_field_name, display_out_set_type, display_rel, display_type,
    display_type_fields, display_weight_static_name, ElVar, RustGenCtx,
};
use crate::algebra::signature::{FuncId, TypeId};
use crate::flat_eqlog::{
    iter_flat_rels, FlatInRel, FlatOutRel, FlatRel, IndexAge, IndexSelection, QuerySpec,
};
use crate::fmt_util::FmtFn;
use crate::ram::{
    IndexedCondition, IndexedLifecycle, IndexedOperation, IndexedPlan, IndexedStmt, RamProgram,
};

pub(super) struct Tables<'a> {
    plan: Option<&'a IndexedPlan>,
}

impl<'a> Tables<'a> {
    pub(super) fn new(program: &'a RamProgram) -> Self {
        Self {
            plan: program.indexed.as_ref(),
        }
    }

    fn plan(&self) -> &IndexedPlan {
        self.plan.expect("indexed storage has a RAM plan")
    }

    fn sources(&self) -> impl Iterator<Item = &FlatInRel> {
        self.plan().tables.keys()
    }

    fn init(&self, source: &FlatInRel, _ctx: &RustGenCtx<'_>) -> String {
        let table = &self.plan().tables[source];
        let specs = table
            .indices
            .iter()
            .map(|index| {
                let columns = index.columns.iter().join(", ");
                let equal = index
                    .equalities
                    .iter()
                    .map(|(i, j)| format!("({i}, {j})"))
                    .join(", ");
                let viewed = index.viewed;
                format!("(&[{columns}], &[{equal}], {viewed})")
            })
            .join(", ");
        let arity = table.arity;
        let constructor = if table.functional { "function" } else { "new" };
        format!("eqlog_runtime::IndexedTable::<{arity}>::{constructor}(&[{specs}])")
    }
}

fn type_snake(typ: TypeId, ctx: &RustGenCtx<'_>) -> String {
    display_type(typ, ctx).to_string().to_case(Case::Snake)
}

pub(super) fn table_field(source: &FlatInRel, ctx: &RustGenCtx<'_>) -> String {
    match source {
        FlatInRel::Rel(rel) => {
            let rel_snake = display_rel(*rel, ctx).to_case(Case::Snake);
            format!("{rel_snake}_table")
        }
        FlatInRel::TypeSet(typ) => {
            let type_snake = display_type(*typ, ctx).to_string().to_case(Case::Snake);
            format!("{type_snake}_order_0")
        }
        FlatInRel::RelWithDiagonals { .. } | FlatInRel::Equality(_) => {
            unreachable!("only relations and types have tables")
        }
    }
}

pub(super) fn display_struct<'a>(
    name: &'a str,
    ctx: &'a RustGenCtx<'a>,
    tables: &'a Tables,
    _program: &'a RamProgram,
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
        let functional_fields = ctx
            .indexed()
            .function_codomains
            .iter()
            .copied()
            .map(|typ| {
                let name = type_snake(typ, ctx);
                format!("__functional_{name}: Vec<[u32; 2]>,")
            })
            .join("\n");
        let strata = &ctx.indexed().strata;
        let count = strata.len();
        let since_fields = strata
            .iter()
            .enumerate()
            .map(|(s, stratum)| {
                let len = stratum.sources.len();
                format!("__since_{s}: [u32; {len}],")
            })
            .join("\n");
        let output_fields = strata
            .iter()
            .enumerate()
            .flat_map(|(s, stratum)| {
                stratum.buffers.iter().copied().map(move |(i, rel)| {
                    let field = display_out_set_field_name(&rel, ctx);
                    let typ = display_out_set_type(&rel, ctx);
                    format!("__out_{s}_{i}_{field}: {typ},")
                })
            })
            .join("\n");
        writedoc! {f, "
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
    _program: &'a RamProgram,
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
                formatdoc! {"
                    {type_snake}_equalities: Unification::new(),
                    {type_snake}_weights: Vec::new(),
                    {type_snake}_uprooted: Vec::new(),
                "}
            })
            .join("\n");
        let functional = ctx
            .indexed()
            .function_codomains
            .iter()
            .copied()
            .map(|typ| {
                let name = type_snake(typ, ctx);
                format!("__functional_{name}: Vec::new(),")
            })
            .join("\n");
        let strata = &ctx.indexed().strata;
        let count = strata.len();
        let since = strata
            .iter()
            .enumerate()
            .map(|(s, stratum)| {
                let len = stratum.sources.len();
                format!("__since_{s}: [0; {len}],")
            })
            .join("\n");
        let outputs = strata
            .iter()
            .enumerate()
            .flat_map(|(s, stratum)| {
                stratum.buffers.iter().copied().map(move |(i, rel)| {
                    let field = display_out_set_field_name(&rel, ctx);
                    format!("__out_{s}_{i}_{field}: Vec::new(),")
                })
            })
            .join("\n");
        writedoc! {f, "
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

            #[allow(unused_variables)]
            fn __set_tables_deferred(&mut self, deferred: bool) {{
                self.__sync_tables();
                {set_deferred}
            }}
        "}?;
        for (s, stratum) in ctx.indexed().strata.iter().enumerate() {
            writedoc! {f, "
                #[allow(unused_variables)]
                #[inline(never)]
                fn __run_stratum_{s}(&mut self, delta: &mut ModelDelta) -> bool {{
            "}?;
            emit_operations(f, &stratum.body, s, program, ctx)?;
            writeln!(f, "}}")?;
        }
        Ok(())
    })
}

fn emit_operations(
    f: &mut std::fmt::Formatter<'_>,
    body: &[IndexedOperation],
    s: usize,
    program: &RamProgram,
    ctx: &RustGenCtx<'_>,
) -> std::fmt::Result {
    let stratum = &ctx.indexed().strata[s];
    for operation in body {
        match operation {
            IndexedOperation::SnapshotCursors => {
                let now = stratum.sources.iter().map(|source| { let field=table_field(source,ctx); format!("self.{field}.log_len()") }).join(", ");
                let len=stratum.sources.len();
                writeln!(f,"let since = self.__since_{s}; let now: [u32; {len}] = [{now}];")?;
            }
            IndexedOperation::ReturnUnlessChanged => {
                let changed=stratum.sources.iter().enumerate().map(|(i,source)| {let field=table_field(source,ctx); format!("|| (since[{i}] < now[{i}] && self.{field}.changed_since(since[{i}]))")}).join(" ");
                writeln!(f,"if !(!self.__stratum_initialized[{s}] {changed}) {{ return false; }}")?;
            }
            IndexedOperation::SaveCursors => writeln!(f,"self.__stratum_initialized[{s}] = true; self.__since_{s} = now;")?,
            IndexedOperation::SyncTables => writeln!(f,"self.__sync_tables();")?,
            IndexedOperation::ComputeWork => writeln!(f,"let work: usize = now.iter().zip(&since).map(|(now, since)| (now - since) as usize).sum();")?,
            IndexedOperation::AllocateDelta(id) => { let width=stratum.reads[*id].index.order.len(); writeln!(f,"let mut delta_{id}: Vec<[u32; {width}]> = Vec::new();")?; }
            IndexedOperation::Block(body) => { writeln!(f,"{{")?; emit_operations(f,body,s,program,ctx)?; writeln!(f,"}}")?; }
            IndexedOperation::InitializeTasks { capacity } => {
                let value=capacity.map_or_else(|| "new()".to_owned(),|capacity| format!("with_capacity({capacity})"));
                writeln!(f,"let mut tasks: Vec<eqlog_runtime::Task<'_>> = Vec::{value};")?;
            }
            IndexedOperation::WhenAdvanced { source,body } => {
                writeln!(f,"if since[{source}] < now[{source}] {{")?;
                emit_operations(f,body,s,program,ctx)?;
                writeln!(f,"}}")?;
            }
            IndexedOperation::QueueDelta(id) => {
                let read=&stratum.reads[*id];
                let source=read.source; let position=read.position; let width=read.index.order.len(); let field=table_field(&stratum.sources[source],ctx);
                writedoc! {f, "
                    let (table, delta, since) = (&self.{field}, &mut delta_{id}, since[{source}]);
                    tasks.push(Box::new(move || *delta = table.delta::<{width}>({position}, since)));
                "}?;
            }
            IndexedOperation::RunTasks => writeln!(f,"eqlog_runtime::run_tasks(work, tasks);")?,
            IndexedOperation::TakeOutput { producer,rel } => {
                let field=display_out_set_field_name(rel,ctx);
                writeln!(f,"let mut __out_{producer}_{field} = std::mem::take(&mut self.__out_{s}_{producer}_{field});")?;
            }
            IndexedOperation::QueueCall(call) => {
                let module=&program.functions[call.function];
                let env=display_module_env_struct_name(module); let name=&module.name; let i=call.producer;
                writeln!(f,"let env = {env} {{ phantom: std::marker::PhantomData,")?;
                for &id in &call.inputs {
                    let read=&stratum.reads[id];
                    let env_field=display_index_field_name(&read.rel,&read.index,ctx);
                    let source=read.source; let position=read.position; let field=table_field(&stratum.sources[source],ctx);
                    match read.index.age {
                        IndexAge::Old => writeln!(f,"{env_field}: self.{field}.view_before({position}, since[{source}]),")?,
                        IndexAge::All => writeln!(f,"{env_field}: self.{field}.view({position}),")?,
                        IndexAge::New => writeln!(f,"{env_field}: eqlog_runtime::RowsView::new(&delta_{id}),")?,
                    }
                }
                for rel in &call.outputs {
                    let field=display_out_set_field_name(rel,ctx);
                    writeln!(f,"{field}: &mut __out_{i}_{field},")?;
                    match rel {
                        FlatOutRel::Rel(rel) => { let rows=display_out_rows_field_name(*rel,ctx); let table=table_field(&FlatInRel::Rel(*rel),ctx); writeln!(f,"{rows}: &self.{table},")?; }
                        FlatOutRel::Equality(_) | FlatOutRel::FuncDomain(_) => {}
                    }
                }
                writeln!(f,"}}; tasks.push(Box::new(move || {name}(env)));")?;
            }
            IndexedOperation::ApplyEquality { producer,typ } => {
                let name=type_snake(*typ,ctx); let rel=FlatOutRel::Equality(*typ); let field=display_out_set_field_name(&rel,ctx);
                writedoc! {f, "
                    for [lhs, rhs] in __out_{producer}_{field}.drain(..) {{
                        self.__equate_{name}(lhs.into(), rhs.into());
                    }}
                "}?;
            }
            IndexedOperation::CanonicalizeEqualities(types) => {
                let changed=types.iter().map(|&typ| { let name=type_snake(typ,ctx); format!("!self.{name}_uprooted.is_empty()") }).join(" || ");
                writeln!(f,"if {changed} {{ self.__canonicalize_relations(); }}")?;
            }
            IndexedOperation::Insert { producer,rel,arity } => {
                let output=FlatOutRel::Rel(*rel); let field=display_out_set_field_name(&output,ctx); let insert=ctx.internal_insert_name(*rel); let table=table_field(&FlatInRel::Rel(*rel),ctx);
                let args=(0..*arity).map(|i|format!("arg{i}")).collect::<Vec<_>>(); let converted=args.iter().map(|arg|format!("{arg}.into()")).join(", "); let args=args.join(", ");
                writedoc! {f, "
                    for [{args}] in __out_{producer}_{field}.drain(..) {{
                        if !self.{table}.contains([{args}]) {{ self.{insert}({converted}); }}
                    }}
                "}?;
            }
            IndexedOperation::AppendPending { producer,rel } => { let field=display_out_set_field_name(rel,ctx); writeln!(f,"delta.{field}.append(&mut __out_{producer}_{field});")?; }
            IndexedOperation::RestoreOutput { producer,rel } => { let field=display_out_set_field_name(rel,ctx); writeln!(f,"self.__out_{s}_{producer}_{field} = __out_{producer}_{field};")?; }
            IndexedOperation::NormalizeFunctions => writeln!(f,"self.__normalize_functions();")?,
            IndexedOperation::ReturnChanged => writeln!(f,"true")?,
        }
    }
    Ok(())
}

fn emit_schedule(
    f: &mut std::fmt::Formatter<'_>,
    body: &[IndexedStmt],
    ctx: &RustGenCtx<'_>,
) -> std::fmt::Result {
    for stmt in body {
        match stmt {
            IndexedStmt::When { condition, body } => {
                let condition = match condition {
                    IndexedCondition::Closed => "self.__closed".to_owned(),
                    IndexedCondition::NoAllocationOrNormalization => {
                        "!self.__allocated && !normalized".to_owned()
                    }
                    IndexedCondition::NoPendingEqualities => "!pending".to_owned(),
                    IndexedCondition::AnyUprooted(types) => {
                        let checks = types
                            .iter()
                            .map(|&typ| {
                                let name = type_snake(typ, ctx);
                                format!("|| !self.{name}_uprooted.is_empty()")
                            })
                            .join(" ");
                        format!("false {checks}")
                    }
                };
                writeln!(f, "if {condition} {{")?;
                emit_schedule(f, body, ctx)?;
                writeln!(f, "}}")?;
            }
            IndexedStmt::ApplyFunctionalEqualities(typ) => {
                let name = type_snake(*typ, ctx);
                writeln!(f,"for [lhs, rhs] in std::mem::take(&mut self.__functional_{name}) {{ pending = true; self.__equate_{name}(lhs.into(), rhs.into()); }}")?;
            }
            IndexedStmt::Lifecycle(operation) => {
                let value=match operation {
                    IndexedLifecycle::SetDeferred(value) => format!("self.__set_tables_deferred({value});"),
                    IndexedLifecycle::CallDeferredClose => "let result = self.__close_until_deferred(condition);".to_owned(),
                    IndexedLifecycle::ReturnResult => "result".to_owned(),
                    IndexedLifecycle::CanonicalizeRelations => "self.__canonicalize_relations();".to_owned(),
                    IndexedLifecycle::NormalizeFunctions => "self.__normalize_functions();".to_owned(),
                    IndexedLifecycle::CheckConditionBeforeDelta => "if self.__check_condition(condition) { return true; }".to_owned(),
                    IndexedLifecycle::TakeDelta => "let mut delta = std::mem::replace(&mut self.__pending_delta, ModelDelta::new());".to_owned(),
                    IndexedLifecycle::ClearAllocated => "self.__allocated = false;".to_owned(),
                    IndexedLifecycle::ApplyDeferredFunctions => "delta.apply_func_defs(self);".to_owned(),
                    IndexedLifecycle::RecordNormalized => "let normalized = self.__normalize_functions();".to_owned(),
                    IndexedLifecycle::SaveDelta => "std::mem::swap(&mut self.__pending_delta, &mut delta);".to_owned(),
                    IndexedLifecycle::Canonicalize => "self.canonicalize();".to_owned(),
                    IndexedLifecycle::MarkClosed => "self.__closed = true;".to_owned(),
                    IndexedLifecycle::ReturnFalse => "return false;".to_owned(),
                    IndexedLifecycle::ReturnCondition => "return condition.is_some_and(|condition| condition(self));".to_owned(),
                    IndexedLifecycle::InitializeNormalization => "let mut changed = false;".to_owned(),
                    IndexedLifecycle::InitializePending => "let mut pending = false;".to_owned(),
                    IndexedLifecycle::MarkNormalizationChanged => "changed = true;".to_owned(),
                    IndexedLifecycle::ReturnNormalizationChanged => "return changed;".to_owned(),
                };
                writeln!(f, "{value}")?;
            }

            IndexedStmt::Loop(body) => {
                writeln!(f, "loop {{")?;
                emit_schedule(f, body, ctx)?;
                writeln!(f, "}}")?;
            }
            IndexedStmt::WhenChanged { stratum, body } => {
                writeln!(f, "if self.__run_stratum_{stratum}(&mut delta) {{")?;
                emit_schedule(f, body, ctx)?;
                writeln!(f, "}}")?;
            }
            IndexedStmt::InitializeChanges(id) => writeln!(f, "let mut active_{id} = false;")?,
            IndexedStmt::MarkChanged(id) => writeln!(f, "active_{id} = true;")?,
            IndexedStmt::BreakUnlessChanged(id) => writeln!(f, "if !active_{id} {{ break; }}")?,
            IndexedStmt::CheckCondition => writedoc! {f, "
                if self.__check_condition(condition) {{
                    std::mem::swap(&mut self.__pending_delta, &mut delta);
                    return true;
                }}
            "}?,
        }
    }
    Ok(())
}

pub(super) fn display_close<'a>(
    _program: &'a RamProgram,
    ctx: &'a RustGenCtx<'a>,
) -> impl Display + 'a {
    FmtFn(move |f| {
        writedoc! {f, "
            #[allow(unused_mut)]
            fn __normalize_functions(&mut self) -> bool {{
        "}?;
        emit_schedule(f, &ctx.indexed().normalize, ctx)?;
        writeln!(f, "}}")?;
        writedoc! {f, "
            /// Closes the model until the condition holds or all rules are satisfied.
            /// Depending on the axioms, this may run indefinitely.
            #[allow(dead_code)]
            pub fn close_until(&mut self, condition: impl Fn(&Self) -> bool) -> bool {{
                self.__close_until(Some(&condition))
            }}

            fn __close_until(&mut self, condition: Option<&dyn Fn(&Self) -> bool>) -> bool {{
        "}?;
        emit_schedule(f, &ctx.indexed().wrapper, ctx)?;
        writedoc! {f, "
            }}
            fn __close_until_deferred(&mut self, condition: Option<&dyn Fn(&Self) -> bool>) -> bool {{
        "}?;
        emit_schedule(f, &ctx.indexed().body, ctx)?;
        writeln!(f, "}}")
    })
}

fn relation_tag(rel: FlatRel, ctx: &RustGenCtx<'_>) -> usize {
    iter_flat_rels(ctx.signature())
        .position(|other| other == rel)
        .expect("relations are flat relations of the signature")
}

pub(super) fn occurrences_field(typ: TypeId, ctx: &RustGenCtx<'_>) -> String {
    let name = type_snake(typ, ctx);
    format!("__occurrences_{name}")
}

pub(super) fn display_occurrence(rel: FlatRel, ctx: &RustGenCtx<'_>) -> String {
    let field = table_field(&FlatInRel::Rel(rel), ctx);
    let tag = relation_tag(rel, ctx);
    format!("let occurrence = u64::from(self.{field}.log_len() - 1) | ({tag} << 32);")
}

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
                    formatdoc! {"
                        let weight{i}: &mut usize = &mut self.{type_snake}_weights[el{i} as usize];
                        *weight{i} = weight{i}.saturating_sub({weight});
                    "}
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

pub(super) fn display_eval_body(
    func: FuncId,
    selection: &IndexSelection,
    ctx: &RustGenCtx<'_>,
) -> String {
    let rel = FlatInRel::Rel(FlatRel::Func(func));
    let index = selection.current_query(&rel, QuerySpec::eval_func(func, ctx.signature()));
    let field = table_field(&rel, ctx);
    let position = ctx.indexed().position(&rel, &index.order);
    let gets = index.order[..index.order.len() - 1]
        .iter()
        .map(|i| format!("let set = set.get(arg{i}.0)?;"))
        .join("\n");
    formatdoc! {"
        let set = self.{field}.view({position});
        {gets}
        let (result, _) = set.iter_restrictions().next()?;
    "}
}

pub(super) fn display_iter_expr(rel: FlatRel, ctx: &RustGenCtx<'_>) -> String {
    let field = table_field(&FlatInRel::Rel(rel), ctx);
    format!("self.{field}")
}

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

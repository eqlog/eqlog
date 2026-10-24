use crate::algebra::signature::{Signature, TypeId};
use crate::flat_eqlog::*;
use crate::fmt_util::*;
use crate::options::ModelMode;
use crate::rust_gen::flat_eqlog::display_flat_rule;
use crate::rust_gen::*;
use convert_case::{Case, Casing};
use indoc::writedoc;
use itertools::Itertools;
use std::fmt::{Display, Formatter, Result};

use Case::{Snake, UpperCamel};

fn display_imports<'a>() -> impl 'a + Display {
    FmtFn(move |f: &mut Formatter| -> Result {
        writedoc! {f, "
            #[allow(unused)]
            use eqlog_runtime::*;
            #[allow(unused)]
            use std::cell::LazyCell;
        "}
    })
}

pub fn display_module_env_struct_name<'a>(ram_module: &'a RamModule) -> impl 'a + Display {
    FmtFn(move |f| {
        // Keep internal environments distinct from user rules after case conversion.
        if ram_module.name.starts_with("__") {
            write!(f, "__")?;
        }
        let name_camel = &ram_module.name.to_case(UpperCamel);
        write!(f, "{name_camel}Env")
    })
}

pub fn module_env_in_rels(ram_module: &RamModule) -> BTreeSet<(FlatInRel, IndexSpec)> {
    ram_module.input_indices()
}

fn iteration_type(stmt: &IterStmt, signature: &Signature) -> TypeId {
    let set = &stmt.sets[0];
    let column = set.name.index.order[set.name.restricted];
    set.name.rel.arity(signature)[column]
}

pub fn module_env_iter_types(ram_module: &RamModule, signature: &Signature) -> BTreeSet<TypeId> {
    ram_module
        .routines
        .iter()
        .flat_map(|routine| &routine.stmts)
        .filter_map(|stmt| match stmt {
            RamStmt::Iter(stmt) => stmt
                .canonical_filter
                .then(|| iteration_type(stmt, signature)),
            RamStmt::DefineSet(_)
            | RamStmt::Insert(_)
            | RamStmt::GuardInhabited(_)
            | RamStmt::GuardPlan(_) => None,
        })
        .collect()
}

pub fn module_env_out_rels(ram_module: &RamModule) -> BTreeSet<FlatOutRel> {
    ram_module
        .routines
        .iter()
        .flat_map(|routine| {
            routine
                .stmts
                .iter()
                .filter_map(|stmt| -> Option<FlatOutRel> {
                    let InsertStmt { rel, args: _ } = match stmt {
                        RamStmt::DefineSet(_)
                        | RamStmt::Iter(_)
                        | RamStmt::GuardInhabited(_)
                        | RamStmt::GuardPlan(_) => {
                            return None;
                        }
                        RamStmt::Insert(insert_stmt) => insert_stmt,
                    };

                    Some(rel.clone())
                })
        })
        .collect()
}

pub fn display_out_rows_field_name<'a>(rel: FlatRel, ctx: &'a RustGenCtx<'a>) -> impl 'a + Display {
    FmtFn(move |f| {
        let rel_snake = display_rel(rel, ctx).to_string().to_case(Snake);
        write!(f, "{rel_snake}_rows")
    })
}

pub fn display_module_env_struct<'a>(
    ram_module: &'a RamModule,
    ctx: &'a RustGenCtx<'a>,
) -> impl 'a + Display {
    FmtFn(move |f: &mut Formatter| -> Result {
        let in_rels = module_env_in_rels(ram_module)
            .into_iter()
            .map(|(rel, index_spec)| {
                FmtFn(move |f| {
                    let name = display_index_field_name(&rel, &index_spec, ctx);
                    match ctx.model_mode() {
                        ModelMode::Native => {
                            let typ = display_index_type(&rel, ctx);
                            write!(f, "{name}: &'a {typ},")
                        }
                        ModelMode::Desugared => match index_spec.age {
                            IndexAge::New => {
                                let width = index_spec.order.len();
                                write!(f, "{name}: eqlog_runtime::RowsView<'a, {width}>,")
                            }
                            IndexAge::Old => {
                                write!(f, "{name}: eqlog_runtime::TrieView<'a, true>,")
                            }
                            IndexAge::All => {
                                write!(f, "{name}: eqlog_runtime::TrieView<'a, false>,")
                            }
                        },
                    }
                })
            })
            .format("\n");

        let out_rels = module_env_out_rels(ram_module)
            .into_iter()
            .map(|rel| {
                FmtFn(move |f| {
                    let name = display_out_set_field_name(&rel, ctx);
                    let typ = display_out_set_type(&rel, ctx);
                    write!(f, "{name}: &'a mut {typ},")?;
                    match ctx.model_mode() {
                        ModelMode::Native => Ok(()),
                        ModelMode::Desugared => match &rel {
                            FlatOutRel::Rel(out_rel) => {
                                let rows = display_out_rows_field_name(*out_rel, ctx);
                                let arity = out_rel.arity(ctx.signature()).len();
                                write!(f, "\n{rows}: &'a eqlog_runtime::IndexedTable<{arity}>,")
                            }
                            FlatOutRel::Equality(_) | FlatOutRel::FuncDomain(_) => Ok(()),
                        },
                    }
                })
            })
            .format("\n");

        let name = display_module_env_struct_name(ram_module);
        let canonical_types = match ctx.model_mode() {
            ModelMode::Native => module_env_iter_types(ram_module, ctx.signature()),
            ModelMode::Desugared => BTreeSet::new(),
        };
        let canonical = canonical_types
            .iter()
            .map(|&typ| {
                let name = display_type(typ, ctx).to_string().to_case(Snake);
                if ctx.supports_compact_members(typ) {
                    format!("__canonical_{name}: eqlog_runtime::__private::CanonicalMask<'a>,")
                } else {
                    format!("__canonical_{name}: &'a [bool],")
                }
            })
            .join("\n");
        let proofs = match ctx.model_mode() {
            ModelMode::Native if ram_module.owner_count() > 0 => {
                "__proofs: &'a [Vec<eqlog_runtime::__private::Table>],"
            }
            ModelMode::Native | ModelMode::Desugared => "",
        };
        let owners = if ram_module.owner_count() > 0 {
            let count = ram_module.owner_count();
            format!("__owners: [u32; {count}],")
        } else {
            String::new()
        };

        writedoc! {f, "
            #[allow(unused)]
            pub struct {name}<'a> {{
            phantom: std::marker::PhantomData<&'a ()>,
            {proofs}
            {owners}
            {canonical}

            {in_rels}

            {out_rels}
            }}
        "}
    })
}

fn display_set_var<'a>(set_var: &'a SetVar, ctx: &'a RustGenCtx<'a>) -> impl 'a + Display {
    FmtFn(move |f| {
        let SetVarName {
            stmt_index,
            rel,
            index,
            restricted,
        } = set_var.name.clone();
        let field_name = display_index_field_name(&rel, &index, ctx);
        write!(f, "set{stmt_index}_{field_name}_r{restricted}")
    })
}

fn display_in_set_expr<'a>(expr: &'a InSetExpr, ctx: &'a RustGenCtx<'a>) -> impl 'a + Display {
    FmtFn(move |f| match expr {
        InSetExpr::GetIndex(GetIndexExpr { rel, index_spec }) => {
            let index_field = display_index_field_name(rel, index_spec, ctx);
            write!(f, "env.{index_field}")
        }
        InSetExpr::Restrict(RestrictExpr {
            set,
            first_column_var,
        }) => {
            let result_arity = set.arity - 1;
            let set = display_set_var(set, ctx);
            match ctx.model_mode() {
                ModelMode::Native => write!(
                    f,
                    "{set}.get({first_column_var}).unwrap_or_else(|| PrefixTree{result_arity}::empty())"
                ),
                ModelMode::Desugared => {
                    write!(f, "{set}.get({first_column_var}).unwrap_or_default()")
                }
            }
        }
    })
}

fn display_key_count<'a>(sets: &'a [SetVar], ctx: &'a RustGenCtx<'a>) -> impl 'a + Display {
    FmtFn(move |f| {
        write!(f, "0usize")?;
        for set in sets {
            let name = display_set_var(set, ctx);
            let count = match ctx.model_mode() {
                ModelMode::Native if set.arity == 1 => "set.len()",
                ModelMode::Native => "map.len_upper_bound()",
                ModelMode::Desugared => "len_upper_bound()",
            };
            write!(f, ".saturating_add({name}.{count})")?;
        }
        Ok(())
    })
}

fn display_iter_sources<'a>(
    sets: &'a [SetVar],
    ctx: &'a RustGenCtx<'a>,
    unique: bool,
) -> impl 'a + Display {
    FmtFn(move |f| {
        for (i, set) in sets.iter().enumerate() {
            if i > 0 {
                write!(f, ".chain(")?;
            }
            let name = display_set_var(set, ctx);
            write!(f, "{name}.iter_restrictions()")?;
            if unique && i > 0 {
                write!(f, ".filter(|(key, _)| true")?;
                for earlier in &sets[..i] {
                    let earlier = display_set_var(earlier, ctx);
                    write!(f, " && {earlier}.get(*key).is_none()")?;
                }
                write!(f, ")")?;
            }
            if i > 0 {
                write!(f, ")")?;
            }
        }
        Ok(())
    })
}

fn display_iter_expr<'a>(stmt: &'a IterStmt, ctx: &'a RustGenCtx<'a>) -> impl 'a + Display {
    FmtFn(move |f| {
        let direct = display_iter_sources(&stmt.sets, ctx, false);
        if stmt.lookup_drivers.is_empty() {
            return write!(f, "{direct}");
        }
        let loop_set = display_set_var(&stmt.loop_var_set, ctx);
        match ctx.model_mode() {
            ModelMode::Native => {}
            ModelMode::Desugared => {
                let [set] = stmt.sets.as_slice() else {
                    panic!("desugared premises read one set")
                };
                let set = display_set_var(set, ctx);
                let inverse = display_iter_sources(&stmt.lookup_drivers, ctx, true);
                return write!(
                    f,
                    "if {loop_set}_use_lookup {{ eqlog_runtime::Either::Right({inverse}.filter_map(|(key, _)| {set}.get(key).map(|suffix| (key, suffix)))) }} else {{ eqlog_runtime::Either::Left({direct}) }}"
                );
            }
        }
        let inverse = display_iter_sources(&stmt.lookup_drivers, ctx, true);
        write!(
            f,
            "(!{loop_set}_use_lookup).then(|| {direct}).into_iter().flatten()"
        )?;
        write!(
            f,
            ".chain({loop_set}_use_lookup.then(|| {inverse}.flat_map(|(key, _)| {{"
        )?;
        for (i, set) in stmt.sets.iter().enumerate() {
            let name = display_set_var(set, ctx);
            if i > 0 {
                write!(f, ".chain(")?;
            }
            write!(f, "{name}.get(key).into_iter()")?;
            if i > 0 {
                write!(f, ")")?;
            }
        }
        let copy = if stmt.sets[0].arity == 1 {
            ".cloned()"
        } else {
            ""
        };
        write!(
            f,
            "{copy}.map(move |suffix| (key, suffix)) }})).into_iter().flatten())"
        )
    })
}

fn display_stmt_pre<'a>(
    ram_stmt: &'a RamStmt,
    ctx: &'a RustGenCtx<'a>,
    proof_variable: Option<usize>,
) -> impl 'a + Display {
    FmtFn(move |f| match ram_stmt {
        RamStmt::DefineSet(DefineSetStmt { defined_var, expr }) => {
            let expr = display_in_set_expr(expr, ctx);
            let strictness = match ctx.model_mode() {
                ModelMode::Native => defined_var.strictness,
                ModelMode::Desugared => Strictness::Strict,
            };
            let defined_var = display_set_var(defined_var, ctx);
            match strictness {
                Strictness::Lazy => {
                    writedoc! {f, "
                            let {defined_var} =
                            LazyCell::new(|| {{
                            {expr}
                            }});
                        "}
                }
                Strictness::Strict => {
                    writedoc! {f, "
                            let {defined_var} =
                            {expr}
                            ;
                        "}
                }
            }
        }
        RamStmt::Iter(
            iter @ IterStmt {
                sets,
                lookup_drivers,
                loop_var_el,
                loop_var_set,
                first_only,
                canonical_filter,
            },
        ) => {
            let canonical_filter = match ctx.model_mode() {
                ModelMode::Native => *canonical_filter,
                ModelMode::Desugared => false,
            };
            let filter = if canonical_filter {
                let typ = iteration_type(iter, ctx.signature());
                let name = display_type(typ, ctx).to_string().to_case(Snake);
                if ctx.supports_compact_members(typ) {
                    format!(".filter(|(key, _)| env.__canonical_{name}.contains(*key))")
                } else {
                    format!(".filter(|(key, _)| env.__canonical_{name}[*key as usize])")
                }
            } else {
                String::new()
            };
            let SetVar {
                name: _,
                arity: _,
                strictness,
            } = loop_var_set;
            match strictness {
                Strictness::Lazy => {
                    panic!("Loop set variables for iter statements must be strict")
                }
                Strictness::Strict => {}
            }
            assert!(sets.len() >= 1, "Expected at least one set in IterStmt");
            let iterator = display_iter_expr(iter, ctx);
            let iterator = if let Some(variable) = proof_variable {
                writedoc! {f, "
                    let __proof_keys = __match_proofs.as_ref()
                        .and_then(|proofs| proofs.uncovered_keys({variable}));
                "}?;
                let copy = if sets[0].arity == 1 { ".cloned()" } else { "" };
                let lookups = sets
                    .iter()
                    .map(|set| {
                        let name = display_set_var(set, ctx);
                        format!(
                            "{name}.get(key).into_iter(){copy}.map(move |suffix| (key, suffix))"
                        )
                    })
                    .reduce(|left, right| format!("{left}.chain({right})"))
                    .unwrap();
                format!(
                    "__proof_keys.as_ref().into_iter().flat_map(|keys| keys.iter_restrictions().flat_map(|(key, _)| {{ {lookups} }})).chain(__proof_keys.is_none().then(|| {iterator}).into_iter().flatten())"
                )
            } else {
                iterator.to_string()
            };
            if !lookup_drivers.is_empty() {
                let direct_count = display_key_count(sets, ctx);
                let inverse_count = display_key_count(lookup_drivers, ctx);
                let loop_set = display_set_var(loop_var_set, ctx);
                let lookup_cost = sets.len() + 1;
                writedoc! {f, "
                    let {loop_set}_key_count = {direct_count};
                    let {loop_set}_use_lookup = {loop_set}_key_count > 1
                        && ({inverse_count}).saturating_mul({lookup_cost}) < {loop_set}_key_count;
                "}?;
            }
            let loop_var_set = display_set_var(loop_var_set, ctx);
            let limit = if *first_only { ".take(1)" } else { "" };
            // Old rows come first in trie views of age all only until a
            // removal reorders their entries.
            let iterator = match ctx.model_mode() {
                ModelMode::Desugared if *first_only => {
                    let [set] = sets.as_slice() else {
                        panic!("desugared anchors read one set")
                    };
                    let set = display_set_var(set, ctx);
                    format!("{set}.oldest_restriction().into_iter()")
                }
                ModelMode::Native | ModelMode::Desugared => iterator.to_string(),
            };
            writedoc! {f, "
                    #[allow(unused_variables)]
                    for
                    ({loop_var_el}, {loop_var_set})
                    in
                    {iterator}
                    {filter}
                    {limit}
                    {{
                "}
        }
        RamStmt::Insert(InsertStmt { rel, args }) => {
            let rel_field = display_out_set_field_name(rel, ctx);
            match rel {
                FlatOutRel::Equality(_) => {
                    let [lhs, rhs] = args.as_slice() else {
                        unreachable!("equality output has two operands")
                    };
                    if lhs == rhs {
                        return Ok(());
                    }
                    writedoc! {f, "
                            if {lhs} != {rhs} {{
                                env.{rel_field}.push([{lhs}, {rhs}]);
                            }}
                        "}
                }
                FlatOutRel::Rel(out_rel) => {
                    let args = args.iter().join(", ");
                    match ctx.model_mode() {
                        ModelMode::Native => writedoc! {f, "
                            env.{rel_field}.push([{args}]);
                        "},
                        ModelMode::Desugared => {
                            let rows = display_out_rows_field_name(*out_rel, ctx);
                            writedoc! {f, "
                                if !env.{rows}.contains([{args}]) {{
                                    env.{rel_field}.push([{args}]);
                                }}
                            "}
                        }
                    }
                }
                FlatOutRel::FuncDomain(_) => {
                    let args = args.iter().format(", ");
                    writedoc! {f, "
                            env.{rel_field}.push([{args}]);
                        "}
                }
            }
        }
        RamStmt::GuardPlan(plan) => {
            let original = display_key_count(&plan.original, ctx);
            let alternative = display_key_count(&plan.alternative, ctx);
            let selected = plan.select_alternative;
            if !plan.probe_rows {
                return writedoc! {f, "
                    if (({alternative}).saturating_mul(2) < {original}) == {selected} {{
                "};
            }
            let (first, rest) = plan.alternative.split_first().expect("a plan has a driver");
            let first = display_set_var(first, ctx);
            let rest = rest
                .iter()
                .map(|set| {
                    let name = display_set_var(set, ctx);
                    format!(".chain({name}.iter())")
                })
                .join("");
            writedoc! {f, "
                let __plan_size = {original};
                let __plan_lookup_cost = (__plan_size.max(1).ilog2() as usize + 1).saturating_mul(2);
                let __plan_budget = __plan_size / __plan_lookup_cost;
                let __plan_alternative = __plan_size > 1
                    && ({alternative}) <= __plan_budget
                    && {first}.iter(){rest}.take(__plan_budget.saturating_add(1)).count() <= __plan_budget;
                if __plan_alternative == {selected} {{
            "}
        }
        RamStmt::GuardInhabited(GuardInhabitedStmt { sets }) => {
            let checks = sets
                .iter()
                .map(|set| {
                    FmtFn(move |f| {
                        let set = display_set_var(set, ctx);
                        write!(f, "|| !{set}.is_empty()")
                    })
                })
                .format("");
            writedoc! {f, "
                    if false {checks} {{
                "}
        }
    })
}

fn display_stmt_post<'a>(ram_stmt: &'a RamStmt) -> impl 'a + Display {
    FmtFn(move |f| match ram_stmt {
        RamStmt::DefineSet(_) | RamStmt::Insert(_) => Ok(()),
        RamStmt::Iter(_) | RamStmt::GuardInhabited(_) | RamStmt::GuardPlan(_) => {
            writedoc! {f, "
                    }}
                "}
        }
    })
}

fn shared_routine_groups(ram_module: &RamModule) -> Vec<Vec<&RamRoutine>> {
    let mut groups: BTreeMap<(&[FlatVar], &[RamStmt]), Vec<&RamRoutine>> = BTreeMap::new();
    let mut independent = Vec::new();
    for routine in &ram_module.routines {
        let first_loop = routine.stmts.iter().position(|stmt| match stmt {
            RamStmt::Iter(_) => true,
            RamStmt::DefineSet(_)
            | RamStmt::Insert(_)
            | RamStmt::GuardInhabited(_)
            | RamStmt::GuardPlan(_) => false,
        });
        if let Some(first_loop) = first_loop {
            groups
                .entry((
                    routine.flat_rule.scope.owners(),
                    &routine.stmts[..=first_loop],
                ))
                .or_default()
                .push(routine);
        } else {
            independent.push(vec![routine]);
        }
    }
    independent.extend(groups.into_values());
    independent
}

fn display_shared_stmts<'a>(
    routines: &'a [&'a [RamStmt]],
    ctx: &'a RustGenCtx<'a>,
) -> impl 'a + Display {
    FmtFn(move |f| {
        let first = routines[0];
        if routines.len() == 1 {
            for stmt in first {
                write!(f, "{}", display_stmt_pre(stmt, ctx, None))?;
            }
            for stmt in first.iter().rev() {
                write!(f, "{}", display_stmt_post(stmt))?;
            }
            return Ok(());
        }
        let shared = first
            .iter()
            .enumerate()
            .take_while(|(i, stmt)| match stmt {
                RamStmt::Insert(_) => false,
                RamStmt::DefineSet(_)
                | RamStmt::Iter(_)
                | RamStmt::GuardInhabited(_)
                | RamStmt::GuardPlan(_) => {
                    routines.iter().all(|routine| routine.get(*i) == Some(stmt))
                }
            })
            .count();
        for stmt in &first[..shared] {
            write!(f, "{}", display_stmt_pre(stmt, ctx, None))?;
        }

        let mut branches: BTreeMap<&RamStmt, Vec<&[RamStmt]>> = BTreeMap::new();
        for routine in routines {
            if let Some(stmt) = routine.get(shared) {
                branches.entry(stmt).or_default().push(&routine[shared..]);
            }
        }
        for (stmt, branch) in branches {
            writeln!(f, "{{")?;
            match stmt {
                RamStmt::Insert(_) => {
                    for suffix in branch {
                        writeln!(f, "{{ {} }}", display_shared_stmts(&[suffix], ctx))?;
                    }
                }
                RamStmt::DefineSet(_)
                | RamStmt::Iter(_)
                | RamStmt::GuardInhabited(_)
                | RamStmt::GuardPlan(_) => {
                    write!(f, "{}", display_shared_stmts(&branch, ctx))?;
                }
            }
            writeln!(f, "}}")?;
        }

        for stmt in first[..shared].iter().rev() {
            write!(f, "{}", display_stmt_post(stmt))?;
        }
        Ok(())
    })
}

pub(super) fn proof_owner_prefix(module: &RamModule) -> bool {
    if module.owner_count() != 1 {
        return false;
    }
    module.routines.iter().all(|routine| {
        let owner = &routine.flat_rule.scope.owners()[0];
        !routine.flat_rule.premise.is_empty()
            && routine
                .flat_rule
                .premise
                .iter()
                .all(|stmt| stmt.args.first() == Some(owner))
            && routine.stmts.iter().all(|stmt| match stmt {
                RamStmt::DefineSet(stmt) => match &stmt.expr {
                    InSetExpr::GetIndex(index) => index.index_spec.order.first() == Some(&0),
                    InSetExpr::Restrict(_) => true,
                },
                RamStmt::Iter(_)
                | RamStmt::Insert(_)
                | RamStmt::GuardInhabited(_)
                | RamStmt::GuardPlan(_) => true,
            })
    })
}

struct ProofAtom {
    inputs: Vec<usize>,
    columns: Vec<usize>,
}

struct ProofPlan {
    atoms: Vec<ProofAtom>,
    variables: BTreeMap<String, usize>,
    relevant: BTreeSet<usize>,
    owner_prefix: bool,
}

fn proof_plan(routine: &RamRoutine, module: &RamModule) -> Option<ProofPlan> {
    let inputs: Vec<_> = module_env_in_rels(module).into_iter().collect();
    let mut variables = BTreeMap::new();
    for var in routine.flat_rule.premise.iter().flat_map(|stmt| &stmt.args) {
        let next = variables.len();
        variables.entry(var.name.to_string()).or_insert(next);
    }
    let owner_prefix = proof_owner_prefix(module);
    let mut atoms = Vec::new();
    for (position, premise) in routine.flat_rule.premise.iter().enumerate() {
        let mut reads = Vec::new();
        for stmt in &routine.stmts {
            match stmt {
                RamStmt::DefineSet(stmt) => match &stmt.expr {
                    InSetExpr::GetIndex(index) => {
                        if stmt.defined_var.name.stmt_index == position {
                            reads.push(index);
                        }
                    }
                    InSetExpr::Restrict(_) => {}
                },
                RamStmt::Iter(_)
                | RamStmt::Insert(_)
                | RamStmt::GuardInhabited(_)
                | RamStmt::GuardPlan(_) => {}
            }
        }
        let first = reads.first()?;
        if reads
            .iter()
            .any(|read| read.rel != premise.rel || read.index_spec.order != first.index_spec.order)
        {
            return None;
        }
        atoms.push(ProofAtom {
            inputs: reads
                .iter()
                .map(|read| {
                    inputs
                        .binary_search(&(read.rel.clone(), read.index_spec.clone()))
                        .unwrap()
                })
                .collect(),
            columns: first
                .index_spec
                .order
                .iter()
                .skip(usize::from(owner_prefix))
                .map(|&column| variables[premise.args[column].name.as_ref()])
                .collect(),
        });
    }
    let mut relevant = BTreeSet::new();
    for owner in routine.flat_rule.scope.owners() {
        if let Some(&variable) = variables.get(owner.name.as_ref()) {
            relevant.insert(variable);
        }
    }
    for stmt in &routine.stmts {
        match stmt {
            RamStmt::Iter(iter) => {
                relevant.insert(variables[iter.loop_var_el.name.as_ref()]);
            }
            RamStmt::DefineSet(_)
            | RamStmt::Insert(_)
            | RamStmt::GuardInhabited(_)
            | RamStmt::GuardPlan(_) => {}
        }
    }
    (!atoms.is_empty()).then_some(ProofPlan {
        atoms,
        variables,
        relevant,
        owner_prefix,
    })
}

fn display_proved_routine<'a>(
    routine: &'a RamRoutine,
    module: &'a RamModule,
    plan: &'a ProofPlan,
    ctx: &'a RustGenCtx<'a>,
) -> impl 'a + Display {
    FmtFn(move |f| {
        let inputs: Vec<_> = module_env_in_rels(module).into_iter().collect();
        let current = plan
            .atoms
            .iter()
            .map(|atom| {
                let rows = atom.inputs
                    .iter()
                    .map(|&input| {
                        let (rel, index) = &inputs[input];
                        let name = display_index_field_name(rel, index, ctx);
                        format!("eqlog_runtime::__private::Table::from((*env.{name}).clone())")
                    })
                    .reduce(|left, right| format!("{left}.union(&{right})"))
                    .unwrap();
                if plan.owner_prefix {
                    let owner = &routine.flat_rule.scope.owners()[0].name;
                    let arity = atom.columns.len();
                    format!("({rows}).first_column({owner}).unwrap_or_else(|| eqlog_runtime::__private::Table::new({arity}))")
                } else {
                    rows
                }
            })
            .join(", ");
        let proofs = plan
            .atoms
            .iter()
            .map(|atom| {
                let input = atom.inputs[0];
                format!("proof[{input}].clone()")
            })
            .join(", ");
        let columns = plan
            .atoms
            .iter()
            .map(|atom| {
                let columns = atom.columns.iter().join(", ");
                format!("vec![{columns}]")
            })
            .join(", ");
        let relevant = plan.relevant.iter().join(", ");
        writedoc! {f, "
            let __match_proofs = eqlog_runtime::__private::MatchProofState::new(
                vec![{current}],
                env.__proofs.iter().map(|proof| vec![{proofs}]).collect(),
                vec![{columns}],
            ).map(|proofs| proofs.with_relevant_variables(&[{relevant}]));
        "}?;
        for owner in routine
            .flat_rule
            .scope
            .owners()
            .iter()
            .filter(|_| !plan.owner_prefix)
        {
            if let Some(variable) = plan.variables.get(owner.name.as_ref()) {
                let owner = &owner.name;
                writedoc! {f, "
                    let __match_proofs = __match_proofs
                        .and_then(|proofs| proofs.restrict({variable}, {owner}));
                "}?;
            }
        }
        writeln!(
            f,
            "if !__match_proofs.as_ref().is_some_and(|proofs| proofs.is_covered()) {{"
        )?;
        for stmt in &routine.stmts {
            match stmt {
                RamStmt::Iter(iter) => {
                    let variable = plan.variables[iter.loop_var_el.name.as_ref()];
                    write!(f, "{}", display_stmt_pre(stmt, ctx, Some(variable)))?;
                    let value = &iter.loop_var_el;
                    writedoc! {f, "
                        let __match_proofs = __match_proofs.as_ref()
                            .and_then(|proofs| proofs.restrict({variable}, {value}));
                        if !__match_proofs.as_ref().is_some_and(|proofs| proofs.is_covered()) {{
                    "}?;
                }
                RamStmt::Insert(_) => {
                    // Unbound private suffixes only witness existence. A source
                    // containing all those witnesses has already proved this head.
                    writeln!(
                        f,
                        "if !__match_proofs.as_ref().is_some_and(|proofs| proofs.is_covered()) {{"
                    )?;
                    write!(f, "{}", display_stmt_pre(stmt, ctx, None))?;
                    writeln!(f, "}}")?;
                }
                RamStmt::DefineSet(_) | RamStmt::GuardInhabited(_) | RamStmt::GuardPlan(_) => {
                    write!(f, "{}", display_stmt_pre(stmt, ctx, None))?;
                }
            }
        }
        for stmt in routine.stmts.iter().rev() {
            match stmt {
                RamStmt::Iter(_) => writeln!(f, "}}")?,
                RamStmt::DefineSet(_)
                | RamStmt::Insert(_)
                | RamStmt::GuardInhabited(_)
                | RamStmt::GuardPlan(_) => {}
            }
            write!(f, "{}", display_stmt_post(stmt))?;
        }
        writeln!(f, "}}")
    })
}

fn display_routine_group<'a>(
    routines: &'a [&'a RamRoutine],
    ram_module: &'a RamModule,
    ctx: &'a RustGenCtx<'a>,
) -> impl 'a + Display {
    FmtFn(move |f| {
        let name = &routines[0].name;
        let env_type = display_module_env_struct_name(ram_module);
        let owners = routines[0]
            .flat_rule
            .scope
            .owners()
            .iter()
            .enumerate()
            .map(|(i, owner)| {
                let name = &owner.name;
                format!("let {name} = env.__owners[{i}];")
            })
            .join("\n");

        let stmts: Vec<_> = routines
            .iter()
            .map(|routine| routine.stmts.as_slice())
            .collect();
        let body = display_shared_stmts(&stmts, ctx);

        let flat_rules = routines
            .iter()
            .map(|routine| display_flat_rule(&routine.flat_rule, ctx))
            .format("\n")
            .to_string();
        let flat_rule_comment = flat_rules
            .lines()
            .map(|line| FmtFn(move |f| write!(f, "// {line}")))
            .format("\n");

        writedoc! {f, "
            {flat_rule_comment}
            fn {name}(env: &mut {env_type}) {{
            {owners}
        "}?;
        let plans: Option<Vec<_>> = match ctx.model_mode() {
            ModelMode::Native if ram_module.owner_count() > 0 => routines
                .iter()
                .map(|routine| proof_plan(routine, ram_module))
                .collect(),
            ModelMode::Native | ModelMode::Desugared => None,
        };
        if let Some(plans) = plans {
            writeln!(f, "if env.__proofs.is_empty() {{ {body} }} else {{")?;
            for (routine, plan) in routines.iter().zip(&plans) {
                writeln!(
                    f,
                    "{{ {} }}",
                    display_proved_routine(routine, ram_module, plan, ctx)
                )?;
            }
            writeln!(f, "}}")?;
        } else {
            write!(f, "{body}")?;
        }
        writeln!(f, "}}")
    })
}

pub fn display_module_main_fn_name<'a>(ram_module: &'a RamModule) -> impl 'a + Display {
    ram_module.name.to_case(Snake)
}

pub fn display_module_main_fn_decl<'a>(
    ram_module: &'a RamModule,
    symbol_prefix: &'a str,
) -> impl 'a + Display {
    FmtFn(move |f| {
        let fn_name = display_module_main_fn_name(ram_module);
        let env_name = display_module_env_struct_name(ram_module);
        writedoc! {f, r#"
            #[link_name = "{symbol_prefix}_{fn_name}"]
            safe fn {fn_name}(env: {env_name});
        "#}
    })
}

fn display_module_main_fn<'a>(
    ram_module: &'a RamModule,
    routine_groups: &'a [Vec<&'a RamRoutine>],
    symbol_prefix: &'a str,
) -> impl 'a + Display {
    FmtFn(move |f| {
        let fn_name = display_module_main_fn_name(ram_module);
        let env_name = display_module_env_struct_name(ram_module);
        let calls = routine_groups
            .iter()
            .map(|routines| {
                FmtFn(move |f| {
                    let name = &routines[0].name;
                    write!(f, "{name}(&mut env);")
                })
            })
            .format("\n");
        writedoc! {f, r#"
            #[allow(non_snake_case)]
            #[unsafe(no_mangle)]
            pub fn {symbol_prefix}_{fn_name}(mut env: {env_name}) {{
            {calls}
            }}
        "#}
    })
}

pub fn display_ram_module<'a>(
    ram_module: &'a RamModule,
    ctx: &'a RustGenCtx<'a>,
    symbol_prefix: &'a str,
) -> impl 'a + Display {
    FmtFn(move |f: &mut Formatter| -> Result {
        let imports = display_imports();
        let env_struct = display_module_env_struct(ram_module, ctx);
        let groups = shared_routine_groups(ram_module);
        let main_fn = display_module_main_fn(ram_module, &groups, symbol_prefix);
        let routines = groups
            .iter()
            .map(|routines| display_routine_group(routines, ram_module, ctx))
            .format("\n");

        writedoc! {f, r#"
            {imports}
            {env_struct}
            {routines}
            {main_fn}
        "#}
    })
}

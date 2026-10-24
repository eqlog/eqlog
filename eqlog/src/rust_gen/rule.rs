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

pub fn display_function_env_name<'a>(ram_function: &'a RamFunction) -> impl 'a + Display {
    FmtFn(move |f| {
        // Keep internal environments distinct from user rules after case conversion.
        if ram_function.name.starts_with("__") {
            write!(f, "__")?;
        }
        let name_camel = &ram_function.name.to_case(UpperCamel);
        write!(f, "{name_camel}Env")
    })
}

pub fn display_out_rows_field_name<'a>(rel: FlatRel, ctx: &'a RustGenCtx<'a>) -> impl 'a + Display {
    FmtFn(move |f| {
        let rel_snake = display_rel(rel, ctx).to_string().to_case(Snake);
        write!(f, "{rel_snake}_rows")
    })
}

pub fn display_function_env<'a>(
    ram_function: &'a RamFunction,
    ctx: &'a RustGenCtx<'a>,
) -> impl 'a + Display {
    FmtFn(move |f: &mut Formatter| -> Result {
        let in_rels = ram_function
            .interface
            .inputs
            .iter()
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

        let out_rels = ram_function
            .interface
            .outputs
            .iter()
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

        let name = display_function_env_name(ram_function);
        let canonical_types = &ram_function.interface.canonical_types;
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
        let proofs = if ram_function.interface.matching_proofs {
            "__proofs: &'a [Vec<eqlog_runtime::__private::Table>],"
        } else {
            ""
        };
        let owners = if ram_function.owner_count() > 0 {
            let count = ram_function.owner_count();
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

fn display_scalar_var<'a>(
    variable: &'a RamScalarVar,
    ctx: &'a RustGenCtx<'a>,
) -> impl 'a + Display {
    FmtFn(move |f| match variable {
        RamScalarVar::LoopSize(set) => {
            let set = display_set_var(set, ctx);
            write!(f, "{set}_key_count")
        }
        RamScalarVar::LookupSelected(set) => {
            let set = display_set_var(set, ctx);
            write!(f, "{set}_use_lookup")
        }
        RamScalarVar::PlanSize => write!(f, "__plan_size"),
        RamScalarVar::PlanLookupCost => write!(f, "__plan_lookup_cost"),
        RamScalarVar::PlanBudget => write!(f, "__plan_budget"),
        RamScalarVar::PlanAlternative => write!(f, "__plan_alternative"),
    })
}

fn scalar_precedence(expr: &RamScalarExpr) -> usize {
    match expr {
        RamScalarExpr::Binary { op, .. } => match op {
            RamScalarOp::And => 1,
            RamScalarOp::GreaterThan
            | RamScalarOp::LessThan
            | RamScalarOp::LessEqual
            | RamScalarOp::Equal => 2,
            RamScalarOp::Add => 3,
            RamScalarOp::Divide => 4,
            RamScalarOp::SaturatingAdd | RamScalarOp::SaturatingMul | RamScalarOp::Max => 6,
        },
        RamScalarExpr::Log2(_) => 5,
        RamScalarExpr::Integer(_)
        | RamScalarExpr::Boolean(_)
        | RamScalarExpr::Variable(_)
        | RamScalarExpr::KeyCount(_)
        | RamScalarExpr::RowCount { .. } => 6,
    }
}

fn display_scalar_expr<'a>(expr: &'a RamScalarExpr, ctx: &'a RustGenCtx<'a>) -> impl 'a + Display {
    display_scalar_operand(expr, 0, ctx)
}

fn display_scalar_operand<'a>(
    expr: &'a RamScalarExpr,
    precedence: usize,
    ctx: &'a RustGenCtx<'a>,
) -> impl 'a + Display {
    FmtFn(move |f| {
        let own_precedence = scalar_precedence(expr);
        let parentheses = own_precedence < precedence;
        if parentheses {
            write!(f, "(")?;
        }
        match expr {
            RamScalarExpr::Integer(value) => write!(f, "{value}usize")?,
            RamScalarExpr::Boolean(value) => write!(f, "{value}")?,
            RamScalarExpr::Variable(variable) => {
                write!(f, "{}", display_scalar_var(variable, ctx))?
            }
            RamScalarExpr::KeyCount(sets) => write!(f, "{}", display_key_count(sets, ctx))?,
            RamScalarExpr::RowCount { sets, limit } => {
                let (first, rest) = sets.split_first().expect("a row count has a source");
                let first = display_set_var(first, ctx);
                write!(f, "{first}.iter()")?;
                for set in rest {
                    let set = display_set_var(set, ctx);
                    write!(f, ".chain({set}.iter())")?;
                }
                let limit = display_scalar_expr(limit, ctx);
                write!(f, ".take({limit}).count()")?;
            }
            RamScalarExpr::Log2(expr) => {
                let expr = display_scalar_operand(expr, 6, ctx);
                write!(f, "{expr}.ilog2() as usize")?;
            }
            RamScalarExpr::Binary { op, left, right } => match op {
                RamScalarOp::SaturatingAdd | RamScalarOp::SaturatingMul | RamScalarOp::Max => {
                    let left = display_scalar_operand(left, 6, ctx);
                    let right = display_scalar_expr(right, ctx);
                    let method = match op {
                        RamScalarOp::SaturatingAdd => "saturating_add",
                        RamScalarOp::SaturatingMul => "saturating_mul",
                        RamScalarOp::Max => "max",
                        RamScalarOp::Add
                        | RamScalarOp::Divide
                        | RamScalarOp::GreaterThan
                        | RamScalarOp::LessThan
                        | RamScalarOp::LessEqual
                        | RamScalarOp::Equal
                        | RamScalarOp::And => unreachable!("scalar method has a method operator"),
                    };
                    write!(f, "{left}.{method}({right})")?;
                }
                RamScalarOp::Add
                | RamScalarOp::Divide
                | RamScalarOp::GreaterThan
                | RamScalarOp::LessThan
                | RamScalarOp::LessEqual
                | RamScalarOp::Equal
                | RamScalarOp::And => {
                    let left = display_scalar_operand(left, own_precedence + 1, ctx);
                    let right = display_scalar_operand(right, own_precedence + 1, ctx);
                    let operator = match op {
                        RamScalarOp::Add => "+",
                        RamScalarOp::Divide => "/",
                        RamScalarOp::GreaterThan => ">",
                        RamScalarOp::LessThan => "<",
                        RamScalarOp::LessEqual => "<=",
                        RamScalarOp::Equal => "==",
                        RamScalarOp::And => "&&",
                        RamScalarOp::SaturatingAdd
                        | RamScalarOp::SaturatingMul
                        | RamScalarOp::Max => {
                            unreachable!("scalar binary expression has an infix operator")
                        }
                    };
                    write!(f, "{left} {operator} {right}")?;
                }
            },
        }
        if parentheses {
            write!(f, ")")?;
        }
        Ok(())
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

fn display_iter_expr<'a>(stmt: &'a RamIteration, ctx: &'a RustGenCtx<'a>) -> impl 'a + Display {
    FmtFn(move |f| {
        let direct = display_iter_sources(&stmt.sets, ctx, false);
        let selected = match &stmt.strategy {
            IterationStrategy::Direct => return write!(f, "{direct}"),
            IterationStrategy::Oldest => {
                let [set] = stmt.sets.as_slice() else {
                    panic!("desugared anchors read one set")
                };
                let set = display_set_var(set, ctx);
                return write!(f, "{set}.oldest_restriction().into_iter()");
            }
            IterationStrategy::AdaptiveLookup(selected) => display_scalar_var(selected, ctx),
        };
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
                    "if {selected} {{ eqlog_runtime::Either::Right({inverse}.filter_map(|(key, _)| {set}.get(key).map(|suffix| (key, suffix)))) }} else {{ eqlog_runtime::Either::Left({direct}) }}"
                );
            }
        }
        let inverse = display_iter_sources(&stmt.lookup_drivers, ctx, true);
        write!(f, "(!{selected}).then(|| {direct}).into_iter().flatten()")?;
        write!(
            f,
            ".chain({selected}.then(|| {inverse}.flat_map(|(key, _)| {{"
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

fn display_instruction<'a>(
    instruction: &'a RamInstruction,
    module: &'a RamFunction,
    ctx: &'a RustGenCtx<'a>,
) -> impl 'a + Display {
    FmtFn(move |f| match instruction {
        RamInstruction::DefineSet(DefineSetStmt { defined_var, expr }) => {
            let expr = display_in_set_expr(expr, ctx);
            let strictness = defined_var.strictness;
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
        RamInstruction::DefineScalar { variable, value } => {
            let variable = display_scalar_var(variable, ctx);
            let value = display_scalar_expr(value, ctx);
            writeln!(f, "let {variable} = {value};")
        }
        RamInstruction::ForEach {
            iteration:
                iter @ RamIteration {
                    sets,
                    lookup_drivers: _,
                    loop_var_el,
                    loop_var_set,
                    strategy: _,
                    canonical_type,
                    limit,
                },
            proof_variable,
            body,
        } => {
            let filter = if let Some(typ) = canonical_type {
                let name = display_type(*typ, ctx).to_string().to_case(Snake);
                if ctx.supports_compact_members(*typ) {
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
            let iterator = if proof_variable.is_some() {
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
            let loop_var_set = display_set_var(loop_var_set, ctx);
            let limit = limit.map_or_else(String::new, |limit| format!(".take({limit})"));
            writedoc! {f, "
                    #[allow(unused_variables)]
                    for
                    ({loop_var_el}, {loop_var_set})
                    in
                    {iterator}
                    {filter}
                    {limit}
                    {{
                "}?;
            write!(f, "{}", display_block(body, module, ctx))?;
            writeln!(f, "}}")
        }
        RamInstruction::Insert(InsertStmt { rel, args }) => {
            let rel_field = display_out_set_field_name(rel, ctx);
            let args = args.iter().join(", ");
            writeln!(f, "env.{rel_field}.push([{args}]);")
        }
        RamInstruction::If {
            condition,
            then_body,
            else_body,
        } => {
            write!(f, "{}", display_condition_open(condition, ctx))?;
            write!(f, "{}", display_block(then_body, module, ctx))?;
            if !else_body.is_empty() {
                writeln!(f, "}} else {{")?;
                write!(f, "{}", display_block(else_body, module, ctx))?;
            }
            writeln!(f, "}}")
        }
        RamInstruction::Scope(body) => {
            writeln!(f, "{{")?;
            write!(f, "{}", display_block(body, module, ctx))?;
            writeln!(f, "}}")
        }
        RamInstruction::Call(procedure) => {
            let name = &module.procedures[*procedure].name;
            writeln!(f, "{name}(&mut env);")
        }
        RamInstruction::BeginProof(plan) => write!(f, "{}", display_begin_proof(module, plan, ctx)),
        RamInstruction::PrepareProofKeys(variable) => writedoc! {f, "
            let __proof_keys = __match_proofs.as_ref()
                .and_then(|proofs| proofs.uncovered_keys({variable}));
        "},
        RamInstruction::RestrictProof {
            variable,
            value,
            access,
        } => {
            let access = match access {
                ProofAccess::Consume => "",
                ProofAccess::Borrow => ".as_ref()",
            };
            writedoc! {f, "
                let __match_proofs = __match_proofs{access}
                    .and_then(|proofs| proofs.restrict({variable}, {value}));
            "}
        }
    })
}

fn display_condition_open<'a>(
    condition: &'a RamCondition,
    ctx: &'a RustGenCtx<'a>,
) -> impl 'a + Display {
    FmtFn(move |f| match condition {
        RamCondition::Scalar(condition) => {
            let condition = display_scalar_expr(condition, ctx);
            writeln!(f, "if {condition} {{")
        }
        RamCondition::Distinct(left, right) => writeln!(f, "if {left} != {right} {{"),
        RamCondition::Absent { rel, args } => {
            let rows = display_out_rows_field_name(*rel, ctx);
            let args = args.iter().join(", ");
            writeln!(f, "if !env.{rows}.contains([{args}]) {{")
        }
        RamCondition::Inhabited(GuardInhabitedStmt { sets }) => {
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
        RamCondition::Uncovered => writeln!(
            f,
            "if !__match_proofs.as_ref().is_some_and(|proofs| proofs.is_covered()) {{"
        ),
        RamCondition::NoProofs => writeln!(f, "if env.__proofs.is_empty() {{"),
    })
}

fn display_block<'a>(
    body: &'a [RamInstruction],
    module: &'a RamFunction,
    ctx: &'a RustGenCtx<'a>,
) -> impl 'a + Display {
    FmtFn(move |f| {
        for instruction in body {
            write!(f, "{}", display_instruction(instruction, module, ctx))?;
        }
        Ok(())
    })
}

fn display_begin_proof<'a>(
    module: &'a RamFunction,
    plan: &'a ProofPlan,
    ctx: &'a RustGenCtx<'a>,
) -> impl 'a + Display {
    FmtFn(move |f| {
        let inputs: Vec<_> = module.interface.inputs.iter().collect();
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
                if let Some(owner) = &plan.owner_prefix {
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
        "}
    })
}

fn display_procedure<'a>(
    procedure: &'a RamProcedure,
    module: &'a RamFunction,
    ctx: &'a RustGenCtx<'a>,
) -> impl 'a + Display {
    FmtFn(move |f| {
        let name = &procedure.name;
        let env_type = display_function_env_name(module);
        let owners = procedure
            .owners
            .iter()
            .enumerate()
            .map(|(i, owner)| format!("let {owner} = env.__owners[{i}];"))
            .join("\n");
        let flat_rules = procedure
            .rules
            .iter()
            .map(|rule| display_flat_rule(rule, ctx))
            .format("\n")
            .to_string();
        let comment = flat_rules
            .lines()
            .map(|line| format!("// {line}"))
            .join("\n");
        let body = display_block(&procedure.body, module, ctx);
        writedoc! {f, "
            {comment}
            fn {name}(env: &mut {env_type}) {{
                {owners}
                {body}
            }}
        "}
    })
}

pub fn display_function_name<'a>(ram_function: &'a RamFunction) -> impl 'a + Display {
    ram_function.name.to_case(Snake)
}

pub fn display_function_declaration<'a>(
    ram_function: &'a RamFunction,
    symbol_prefix: &'a str,
) -> impl 'a + Display {
    FmtFn(move |f| {
        let fn_name = display_function_name(ram_function);
        let env_name = display_function_env_name(ram_function);
        writedoc! {f, r#"
            #[link_name = "{symbol_prefix}_{fn_name}"]
            safe fn {fn_name}(env: {env_name});
        "#}
    })
}

fn display_function_entry<'a>(
    ram_function: &'a RamFunction,
    ctx: &'a RustGenCtx<'a>,
    symbol_prefix: &'a str,
) -> impl 'a + Display {
    FmtFn(move |f| {
        let fn_name = display_function_name(ram_function);
        let env_name = display_function_env_name(ram_function);
        let calls = display_block(&ram_function.body, ram_function, ctx);
        writedoc! {f, r#"
            #[allow(non_snake_case)]
            #[unsafe(no_mangle)]
            pub fn {symbol_prefix}_{fn_name}(mut env: {env_name}) {{
            {calls}
            }}
        "#}
    })
}

pub fn display_ram_function<'a>(
    ram_function: &'a RamFunction,
    ctx: &'a RustGenCtx<'a>,
    symbol_prefix: &'a str,
) -> impl 'a + Display {
    FmtFn(move |f: &mut Formatter| -> Result {
        let imports = display_imports();
        let env_struct = display_function_env(ram_function, ctx);
        let main_fn = display_function_entry(ram_function, ctx, symbol_prefix);
        let routines = ram_function
            .procedures
            .iter()
            .map(|procedure| display_procedure(procedure, ram_function, ctx))
            .format("\n");

        writedoc! {f, r#"
            {imports}
            {env_struct}
            {routines}
            {main_fn}
        "#}
    })
}

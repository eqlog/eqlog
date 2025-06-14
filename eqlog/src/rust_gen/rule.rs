use crate::eqlog_util::*;
use crate::flat_eqlog::*;
use crate::fmt_util::*;
use crate::rust_gen::*;
use convert_case::{Case, Casing};
use eqlog_eqlog::*;
use indoc::writedoc;
use itertools::Itertools;
use std::collections::BTreeMap;
use std::fmt::{Display, Formatter, Result};

use Case::{Snake, UpperCamel};

fn display_imports<'a>() -> impl 'a + Display {
    FmtFn(move |f: &mut Formatter| -> Result {
        writedoc! {f, "
            #[allow(unused)]
            use eqlog_runtime::collections::BTreeSet;
            use eqlog_runtime::collections::btree_set;
        "}
    })
}

pub fn display_rule_env_struct<'a>(
    analysis: &'a FlatRuleAnalysis<'a>,
    eqlog: &'a Eqlog,
    identifiers: &'a BTreeMap<Ident, String>,
) -> impl 'a + Display {
    FmtFn(move |f: &mut Formatter| -> Result {
        let rule_name_camel = analysis.rule_name.to_case(UpperCamel);

        let table_fields = analysis
            .used_rels
            .iter()
            .map(|rel| {
                FmtFn(move |f: &mut Formatter| {
                    let rel_snake = display_rel(*rel, eqlog, identifiers)
                        .to_string()
                        .to_case(Snake);
                    let rel_camel = rel_snake.to_case(UpperCamel);
                    write!(f, "{rel_snake}_table: &'a {rel_camel}Table,")
                })
            })
            .format("\n");

        let type_set_fields = analysis
            .used_types
            .iter()
            .map(|typ| {
                FmtFn(move |f: &mut Formatter| {
                    let type_snake = display_type(*typ, eqlog, identifiers)
                        .to_string()
                        .to_case(Snake);
                    writedoc! {f, "
                    {type_snake}_new: &'a BTreeSet<u32>,
                    {type_snake}_old: &'a BTreeSet<u32>,
                "}
                })
            })
            .format("\n");

        let new_rel_fields = analysis
            .used_rels
            .iter()
            .map(|rel| {
                FmtFn(move |f: &mut Formatter| {
                    let rel_snake = display_rel(*rel, eqlog, identifiers)
                        .to_string()
                        .to_case(Snake);
                    let row_type = display_rel_row_type(*rel, eqlog);
                    writedoc! {f, "
                        new_{rel_snake}: &'a mut Vec<{row_type}>,
                    "}?;
                    if let RelCase::FuncRel(func) = eqlog.rel_case(*rel) {
                        if eqlog.function_can_be_made_defined(func) {
                            let args_type = display_func_args_type(func, eqlog);
                            writedoc! {f, "
                                new_{rel_snake}_def: &'a mut Vec<{args_type}>,
                            "}?;
                        }
                    }
                    Ok(())
                })
            })
            .format("\n");

        let new_type_equalities_fields = analysis
            .used_types
            .iter()
            .map(|typ| {
                FmtFn(move |f: &mut Formatter| {
                    let type_snake = display_type(*typ, eqlog, identifiers)
                        .to_string()
                        .to_case(Snake);
                    writedoc! {f, "
                        new_{type_snake}_equalities: &'a mut Vec<(u32, u32)>,
                    "}
                })
            })
            .format("\n");

        writedoc! {f, "
            #[allow(unused)]
            pub struct {rule_name_camel}Env<'a> {{
                {table_fields}
                {type_set_fields}
                {new_rel_fields}
                {new_type_equalities_fields}
            }}
        "}
    })
}

fn display_rule_iter_types<'a>(
    analysis: &'a FlatRuleAnalysis<'a>,
    index_selection: &'a IndexSelection,
    eqlog: &'a Eqlog,
    identifiers: &'a BTreeMap<Ident, String>,
) -> impl 'a + Display {
    analysis
        .used_rels
        .iter()
        .copied()
        .map(|rel| {
            let rel_name = display_rel(rel, eqlog, identifiers).to_string();
            let query_indices = index_selection.get(&rel_name).unwrap();
            display_iter_ty_structs(rel, query_indices, eqlog, identifiers)
        })
        .format("\n")
}

fn display_rule_iter_fns<'a>(
    analysis: &'a FlatRuleAnalysis<'a>,
    index_selection: &'a IndexSelection,
    eqlog: &'a Eqlog,
    identifiers: &'a BTreeMap<Ident, String>,
    symbol_prefix: &'a str,
) -> impl 'a + Display {
    FmtFn(move |f: &mut Formatter| -> Result {
        // Unique indices:
        let indices: BTreeSet<(Rel, &IndexSpec)> = analysis
            .used_queries
            .iter()
            .flat_map(|(rel, query_spec)| {
                let rel_name = display_rel(*rel, eqlog, identifiers).to_string();
                let index_specs = index_selection
                    .get(rel_name.as_str())
                    .unwrap()
                    .get(query_spec)
                    .unwrap();
                index_specs.iter().map(move |index| (*rel, index))
            })
            .collect();

        let index_getter_fn_decls = indices
            .iter()
            .map(|(rel, index)| {
                display_index_getter_decl(index, *rel, eqlog, identifiers, symbol_prefix)
            })
            .format("\n");

        let iter_fns = analysis
            .used_queries
            .iter()
            .map(move |(rel, query_spec)| {
                let rel_name = display_rel(*rel, eqlog, identifiers).to_string();
                let query_indices = index_selection.get(&rel_name).unwrap();
                let indices = query_indices.get(query_spec).unwrap();

                FmtFn(move |f: &mut Formatter| -> Result {
                    let iter_fn_decl = display_iter_fn_decl(
                        query_spec,
                        indices,
                        *rel,
                        eqlog,
                        identifiers,
                        symbol_prefix,
                    );
                    let iter_next_fn_decl = display_iter_next_fn_decl(
                        query_spec,
                        indices,
                        *rel,
                        eqlog,
                        identifiers,
                        symbol_prefix,
                    );

                    writedoc! {f, "
                    {iter_fn_decl}
                    {iter_next_fn_decl}
                "}
                })
            })
            .format("\n");
        writedoc! {f, "
            {index_getter_fn_decls}
            {iter_fns}
        "}
    })
}

fn display_rule_contains_fns<'a>(
    analysis: &'a FlatRuleAnalysis<'a>,
    eqlog: &'a Eqlog,
    identifiers: &'a BTreeMap<Ident, String>,
    symbol_prefix: &'a str,
) -> impl 'a + Display {
    analysis
        .used_rels
        .iter()
        .copied()
        .map(|rel| display_contains_fn_decl(rel, eqlog, identifiers, symbol_prefix))
        .format("\n")
}

fn display_if_stmt_header<'a>(
    stmt: &'a FlatIfStmt,
    analysis: &'a FlatRuleAnalysis<'a>,
    eqlog: &'a Eqlog,
    identifiers: &'a BTreeMap<Ident, String>,
    index_selection: &'a IndexSelection,
) -> impl 'a + Display {
    FmtFn(move |f: &mut Formatter| -> Result {
        match stmt {
            FlatIfStmt::Equal(eq_stmt) => {
                let FlatStmtEqual { lhs, rhs } = eq_stmt;

                let lhs = display_var(*lhs);
                let rhs = display_var(*rhs);

                // Beware: This works only if variables are always necessary canonical. That's true
                // at the moment, but if it changes, then things will break.
                writedoc! {f, "
                    if {lhs} == {rhs} {{
                "}?;
            }
            FlatIfStmt::Relation(rel_stmt) => {
                let FlatIfStmtRelation { rel, args: _, age } = rel_stmt;
                let RelationInfo {
                    diagonals,
                    in_projections,
                    out_projections,
                    rel: _,
                    age: _,
                } = analysis
                    .if_stmt_rel_infos
                    .get(&ByAddress(rel_stmt))
                    .unwrap();
                let query_spec = QuerySpec {
                    diagonals: diagonals.clone(),
                    projections: in_projections.keys().copied().collect(),
                    age: *age,
                };
                let indices = index_selection
                    .get(&display_rel(*rel, eqlog, identifiers).to_string())
                    .unwrap()
                    .get(&query_spec)
                    .unwrap();
                let relation = format!("{}", display_rel(*rel, eqlog, identifiers));
                let relation_snake = relation.to_case(Snake);
                let relation_snake = &relation_snake;
                let row_type = display_rel_row_type(*rel, eqlog);
                let row_type = &row_type;
                let arity_len = type_list_vec(eqlog.flat_arity(*rel).unwrap(), eqlog).len();
                let fixed_arg_len = query_spec.projections.len();
                let open_arg_len = arity_len - fixed_arg_len;

                let range_defs = indices
                    .iter()
                    .enumerate()
                    .map(|(i, index)| {
                        let fixed_args = index.order[..fixed_arg_len]
                            .iter()
                            .map(|i| {
                                FmtFn(move |f| {
                                    let var = *in_projections.get(i).unwrap();
                                    let var = display_var(var);
                                    write!(f, "{var}, ")
                                })
                            })
                            .format("")
                            .to_string();

                        let open_args_min = (0..open_arg_len).map(|_| "u32::MIN, ").format("");
                        let open_args_max = (0..open_arg_len).map(|_| "u32::MAX, ").format("");
                        let getter_fn =
                            display_index_getter_fn_name(index, *rel, eqlog, identifiers);

                        let row_args = (0..arity_len)
                            .map(|i| FmtFn(move |f| write!(f, "r{i}, ")))
                            .format("");
                        let out_proj_args = (0..arity_len)
                            .filter(|i| out_projections.contains_key(&i))
                            .map(|i| {
                                let j = index.order.iter().position(|&x| x == i).unwrap();
                                FmtFn(move |f| write!(f, "*r{j}"))
                            })
                            .format(", ");
                        let out_proj_arg_num = out_projections.len();

                        FmtFn(move |f| {
                            writedoc! {f, "
                                    let lower: {row_type} = [{fixed_args}{open_args_min}];
                                    let upper: {row_type} = [{fixed_args}{open_args_max}];
                                    let range{i} =
                                    {getter_fn}(&env.{relation_snake}_table).range(lower..=upper)
                                    .map(|[{row_args}]| -> [u32; {out_proj_arg_num}] {{
                                        [{out_proj_args}]
                                    }});
                                "}
                        })
                    })
                    .format("\n");

                let range_chains = (0..indices.len())
                    .map(|i| FmtFn(move |f| write!(f, ".chain(range{i})")))
                    .format("");

                writedoc! {f, "
                        {range_defs}
                        let mut it = [].into_iter(){range_chains};
                    "}?;
                write!(f, "#[allow(unused_variables)]\n")?;
                write!(f, "while let Some([")?;
                for i in 0..arity_len {
                    if let Some(var) = out_projections.get(&i) {
                        write!(f, "tm{}", var.0)?;
                        write!(f, ", ")?;
                    }
                }
                write!(f, "]) = it.next() {{")?;
            }
            FlatIfStmt::Range(_) => todo!(),
            FlatIfStmt::Type(type_stmt) => {
                let FlatIfStmtType { var, age } = type_stmt;
                let typ = format!(
                    "{}",
                    display_type(*analysis.var_types.get(var).unwrap(), eqlog, identifiers)
                );
                let typ_snake = typ.to_case(Snake);
                let var = display_var(*var);
                match age {
                    QueryAge::New => {
                        writedoc! {f, "
                            #[allow(unused_variables)]
                            for {var} in env.{typ_snake}_new.iter().copied() {{
                        "}?;
                    }
                    QueryAge::Old => {
                        writedoc! {f, "
                            #[allow(unused_variables)]
                            for {var} in env.{typ_snake}_old.iter().copied() {{
                        "}?;
                    }
                    QueryAge::All => {
                        writedoc! {f, "
                            #[allow(unused_variables)]
                            for {var} in env.{typ_snake}_old.iter().chain(env.{typ_snake}_new.iter()).copied() {{
                        "}?;
                    }
                }
            }
        };

        Ok(())
    })
}

fn display_surj_then<'a>(
    stmt: &'a FlatSurjThenStmt,
    analysis: &'a FlatRuleAnalysis<'a>,
    eqlog: &'a Eqlog,
    identifiers: &'a BTreeMap<Ident, String>,
) -> impl 'a + Display {
    FmtFn(move |f: &mut Formatter| -> Result {
        match stmt {
            FlatSurjThenStmt::Equal(eq_stmt) => {
                let FlatStmtEqual { lhs, rhs } = eq_stmt;

                let typ = *analysis.var_types.get(lhs).unwrap();
                let typ_snake = format!("{}", display_type(typ, eqlog, identifiers)).to_case(Snake);

                let lhs = display_var(*lhs);
                let rhs = display_var(*rhs);

                writedoc! {f, "
                    env.new_{typ_snake}_equalities.push(({lhs}, {rhs}));
                "}?;
            }
            FlatSurjThenStmt::Relation(rel_stmt) => {
                let FlatSurjThenStmtRelation { rel, args } = rel_stmt;
                let relation_snake = display_rel(*rel, eqlog, identifiers)
                    .to_string()
                    .to_case(Snake);
                let args = args
                    .iter()
                    .copied()
                    .map(|arg| {
                        FmtFn(move |f| {
                            let arg = display_var(arg);
                            write!(f, "{arg}, ")
                        })
                    })
                    .format("")
                    .to_string();
                let contains_fn_name = display_contains_fn_name(*rel, eqlog, identifiers);
                writedoc! {f, "
                    if !{contains_fn_name}(env.{relation_snake}_table, [{args}]) {{
                    env.new_{relation_snake}.push([{args}]);
                    }}
                "}?;
            }
        };

        Ok(())
    })
}

fn display_non_surj_then<'a>(
    stmt: &'a FlatNonSurjThenStmt,
    eqlog: &'a Eqlog,
    identifiers: &'a BTreeMap<Ident, String>,
) -> impl 'a + Display {
    FmtFn(move |f: &mut Formatter| -> Result {
        let FlatNonSurjThenStmt {
            func,
            func_args,
            result,
        } = stmt;
        let rel = eqlog.func_rel(*func).unwrap();
        let relation_snake = format!("{}", display_rel(rel, eqlog, identifiers)).to_case(Snake);

        let eval_func_spec = QuerySpec::eval_func(*func, eqlog);
        let iter_fn_name = display_iter_fn_name(rel, &eval_func_spec, eqlog, identifiers);
        let iter_next_fn_name = display_iter_next_fn_name(&eval_func_spec, rel, eqlog, identifiers);

        let in_args = func_args
            .iter()
            .copied()
            .map(display_var)
            .format(", ")
            .to_string();

        let out_arg_wildcards = repeat("_, ").take(func_args.len()).format("");
        let result = display_var(*result);

        writedoc! {f, "
            let mut it = {iter_fn_name}(env.{relation_snake}_table, {in_args});
            let {result} = match {iter_next_fn_name}(&mut it) {{
                Some([{out_arg_wildcards} res]) => res,
                None => {{
                    env.new_{relation_snake}_def.push([{in_args}]);
                    break;
                }},
            }};
        "}?;
        Ok(())
    })
}

fn display_stmts<'a>(
    stmts: &'a [FlatStmt],
    analysis: &'a FlatRuleAnalysis<'a>,
    eqlog: &'a Eqlog,
    identifiers: &'a BTreeMap<Ident, String>,
    index_selection: &'a IndexSelection,
) -> impl 'a + Display {
    FmtFn(move |f: &mut Formatter| -> Result {
        let (head, tail) = match stmts {
            [] => {
                return Ok(());
            }
            [head, tail @ ..] => (head, tail),
        };

        match head {
            FlatStmt::If(if_stmt) => {
                let if_header =
                    display_if_stmt_header(if_stmt, analysis, eqlog, identifiers, index_selection);
                let if_footer = "}";
                let tail = display_stmts(tail, analysis, eqlog, identifiers, index_selection);
                writedoc! {f, "
                    {if_header}
                    {tail}
                    {if_footer}
                "}?;
            }
            FlatStmt::DefineRange(_) => todo!(),
            FlatStmt::SurjThen(surj_then) => {
                let tail = display_stmts(tail, analysis, eqlog, identifiers, index_selection);
                let surj_then = display_surj_then(surj_then, analysis, eqlog, identifiers);
                writedoc! {f, "
                    {surj_then}
                    {tail}
                "}?;
            }
            FlatStmt::NonSurjThen(non_surj_then) => {
                let tail = display_stmts(tail, analysis, eqlog, identifiers, index_selection);
                let non_surj_then = display_non_surj_then(non_surj_then, eqlog, identifiers);
                writedoc! {f, "
                    {non_surj_then}
                    {tail}
                "}?;
            }
            FlatStmt::Call { func_name, args } => {
                let rule_name = analysis.rule_name;
                let i = func_name.0;
                let args = args.iter().copied().map(display_var).format(", ");
                let tail = display_stmts(tail, analysis, eqlog, identifiers, index_selection);
                writedoc! {f, "
                    {rule_name}_{i}(env, {args});
                    {tail}
                "}?;
            }
        };
        Ok(())
    })
}

fn display_rule_func<'a>(
    rule_name: &'a str,
    flat_func: &'a FlatFunc,
    analysis: &'a FlatRuleAnalysis<'a>,
    eqlog: &'a Eqlog,
    identifiers: &'a BTreeMap<Ident, String>,
    index_selection: &'a IndexSelection,
) -> impl 'a + Display {
    FmtFn(move |f: &mut Formatter| -> Result {
        let func_name = flat_func.name.0;
        let rule_camel = rule_name.to_case(UpperCamel);

        let var_args = flat_func
            .args
            .iter()
            .copied()
            .map(|var| {
                let var_name = display_var(var);
                FmtFn(move |f: &mut Formatter| -> Result { write!(f, "{var_name}: u32") })
            })
            .format(", ");

        let stmts = display_stmts(
            flat_func.body.as_slice(),
            analysis,
            eqlog,
            identifiers,
            index_selection,
        );

        writedoc! {f, "
            #[allow(unused_variables)]
            fn {rule_name}_{func_name}(env: &mut {rule_camel}Env, {var_args}) {{
            for _ in [()] {{
            {stmts}
            }}
            }}
        "}
    })
}
pub fn display_rule_fn_name<'a>(rule_name: &'a str) -> impl 'a + Display {
    FmtFn(move |f| {
        let rule_snake = rule_name.to_case(Snake);
        write!(f, "evaluate_{rule_snake}")
    })
}

fn display_rule_fn_signature<'a>(rule_name: &'a str) -> impl 'a + Display {
    FmtFn(move |f| {
        let fn_name = display_rule_fn_name(rule_name);
        let rule_camel = rule_name.to_case(UpperCamel);
        write!(f, "fn {fn_name}(env: &mut {rule_camel}Env)")
    })
}

pub fn display_rule_fn_decl<'a>(rule_name: &'a str, symbol_prefix: &'a str) -> impl 'a + Display {
    FmtFn(move |f| {
        let fn_name = display_rule_fn_name(rule_name);
        let signature = display_rule_fn_signature(rule_name);
        writedoc! {f, r#"
            #[link_name = "{symbol_prefix}_{fn_name}"]
            safe {signature};
        "#}
    })
}

fn display_rule_fn<'a>(rule_name: &'a str, symbol_prefix: &'a str) -> impl 'a + Display {
    FmtFn(move |f| {
        let fn_name = display_rule_fn_name(rule_name);
        let signature = display_rule_fn_signature(rule_name);

        writedoc! {f, r#"
            #[unsafe(export_name = "{symbol_prefix}_{fn_name}")]
            pub extern "Rust" {signature} {{
                {rule_name}_0(env);
            }}
        "#}
    })
}

pub fn display_rule_lib<'a>(
    rule: &'a FlatRule,
    analysis: &'a FlatRuleAnalysis<'a>,
    index_selection: &'a IndexSelection,
    eqlog: &'a Eqlog,
    identifiers: &'a BTreeMap<Ident, String>,
    symbol_prefix: &'a str,
) -> impl 'a + Display {
    FmtFn(move |f: &mut Formatter| -> Result {
        let imports = display_imports();
        let env_struct = display_rule_env_struct(analysis, eqlog, identifiers);
        let table_struct_decls = analysis
            .used_rels
            .iter()
            .copied()
            .map(|rel| display_table_struct_decl(rel, eqlog, identifiers))
            .format("\n");

        let iter_types = display_rule_iter_types(analysis, index_selection, eqlog, identifiers);
        let iter_fns =
            display_rule_iter_fns(analysis, index_selection, eqlog, identifiers, symbol_prefix);
        let contains_fns = display_rule_contains_fns(analysis, eqlog, identifiers, symbol_prefix);

        let internal_funcs = rule
            .funcs
            .iter()
            .map(|func| {
                display_rule_func(
                    rule.name.as_str(),
                    func,
                    analysis,
                    eqlog,
                    identifiers,
                    index_selection,
                )
            })
            .format("\n");

        let exported_rule_func = display_rule_fn(rule.name.as_str(), symbol_prefix);

        writedoc! {f, r#"
            {imports}
            {table_struct_decls}
            {iter_types}
            #[allow(unused, clashing_extern_declarations)]
            unsafe extern "Rust" {{
            {iter_fns}
            {contains_fns}
            }}
            {env_struct}
            {internal_funcs}
            {exported_rule_func}
        "#}
    })
}

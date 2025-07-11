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
            use eqlog_runtime::{{*, collections::*}};
        "}
    })
}

pub fn display_module_env_struct_name<'a>(ram_module: &'a RamModule) -> impl 'a + Display {
    FmtFn(move |f| {
        let name_camel = &ram_module.name.to_case(UpperCamel);
        write!(f, "{name_camel}Env")
    })
}

pub fn module_env_in_rels(ram_module: &RamModule) -> BTreeSet<(FlatInRel, IndexSpec)> {
    ram_module
        .routines
        .iter()
        .flat_map(|routine| {
            routine
                .stmts
                .iter()
                .filter_map(|stmt| -> Option<(FlatInRel, IndexSpec)> {
                    let define_set_stmt = match stmt {
                        RamStmt::DefineSet(define_set_stmt) => define_set_stmt,
                        RamStmt::Iter(_) | RamStmt::Insert(_) => {
                            return None;
                        }
                    };

                    let GetIndexExpr { rel, index_spec } = match &define_set_stmt.expr {
                        InSetExpr::GetIndex(get_index_expr) => get_index_expr,
                        InSetExpr::Restrict(_) => {
                            return None;
                        }
                    };

                    Some((rel.clone(), index_spec.clone()))
                })
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
                        RamStmt::DefineSet(_) | RamStmt::Iter(_) => {
                            return None;
                        }
                        RamStmt::Insert(insert_stmt) => insert_stmt,
                    };

                    Some(rel.clone())
                })
        })
        .collect()
}

pub fn display_module_env_struct<'a>(
    ram_module: &'a RamModule,
    eqlog: &'a Eqlog,
    identifiers: &'a BTreeMap<Ident, String>,
) -> impl 'a + Display {
    FmtFn(move |f: &mut Formatter| -> Result {
        let in_rels = module_env_in_rels(ram_module)
            .into_iter()
            .map(|(rel, index_spec)| {
                FmtFn(move |f| {
                    let name = display_index_field_name(&rel, &index_spec, eqlog, identifiers);
                    let typ = display_index_type(&rel, eqlog);

                    write!(f, "{name}: &'a {typ},")
                })
            })
            .format("\n");

        let out_rels = module_env_out_rels(ram_module)
            .into_iter()
            .map(|rel| {
                FmtFn(move |f| {
                    let name = display_out_set_field_name(&rel, eqlog, identifiers);
                    let typ = display_out_set_type(&rel, eqlog);

                    write!(f, "{name}: &'a mut {typ},")
                })
            })
            .format("\n");

        let name = display_module_env_struct_name(ram_module);

        writedoc! {f, "
            #[allow(unused)]
            pub struct {name}<'a> {{
            phantom: std::marker::PhantomData<&'a ()>,

            {in_rels}

            {out_rels}
            }}
        "}
    })
}

/*
fn display_table_fn_decls<'a>(
    analysis: &'a FlatRuleAnalysis<'a>,
    eqlog: &'a Eqlog,
    identifiers: &'a BTreeMap<Ident, String>,
    index_selection: &'a IndexSelection,
    symbol_prefix: &'a str,
) -> impl 'a + Display {
    let rels = analysis
        .used_rels
        .iter()
        .copied()
        .map(move |rel| {
            FmtFn(move |f| {
                let contains_fn = display_contains_fn_decl(rel, eqlog, identifiers, symbol_prefix);

                let eval_fn = FmtFn(move |f| match eqlog.rel_case(rel) {
                    RelCase::FuncRel(func) => {
                        let func_name =
                            display_eval_fn_decl(func, eqlog, identifiers, symbol_prefix);
                        write!(f, "{func_name}")
                    }
                    RelCase::PredRel(_) => Ok(()),
                });

                let rel_string = display_rel(rel, eqlog, identifiers).to_string();

                let indices: BTreeSet<&IndexSpec> = analysis
                    .used_queries
                    .iter()
                    .filter_map(|(r, query)| {
                        if *r == rel {
                            Some(
                                index_selection
                                    .get(&rel_string)
                                    .unwrap()
                                    .get(query)
                                    .unwrap(),
                            )
                        } else {
                            None
                        }
                    })
                    .collect();
                let index_getters = indices
                    .into_iter()
                    .map(|index| {
                        display_index_getter_decl(index, rel, eqlog, identifiers, symbol_prefix)
                    })
                    .format("\n");
                writedoc! {f, "
                {contains_fn}
                {eval_fn}
                {index_getters}
            "}
            })
        })
        .format("\n");

    FmtFn(move |f| {
        writedoc! {f, r#"
            #[allow(unused, clashing_extern_declarations)]
            unsafe extern "Rust" {{
            {rels}
            }}
        "#}
    })
}

fn display_if_stmt_header<'a>(
    stmt: &'a FlatIfStmt,
    analysis: &'a FlatRuleAnalysis<'a>,
    eqlog: &'a Eqlog,
    identifiers: &'a BTreeMap<Ident, String>,
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
            FlatIfStmt::Relation(_) => {
                panic!("Should have been resolved into range statements")
            }
            FlatIfStmt::Range(range_stmt) => {
                let FlatIfStmtRange { range_var, args } = range_stmt;

                let range_var = display_range_var(*range_var);
                let args = args
                    .iter()
                    .map(|var| {
                        FmtFn(move |f| match *var {
                            None => {
                                write!(f, "_")
                            }
                            Some(var) => {
                                let var = display_var(var);
                                write!(f, "{var}")
                            }
                        })
                    })
                    .format(", ");

                writedoc! {f, r#"
                    #[allow(unused_variables)]
                    for [{args}] in {range_var}.iter() {{
                "#}?;
            }
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
                    QueryAge::All => panic!("Should have been desugared into Old/New earlier"),
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

        let eval_fn = display_eval_fn_name(*func, eqlog, identifiers);

        let func_args = func_args
            .iter()
            .copied()
            .map(display_var)
            .format(", ")
            .to_string();

        let result = display_var(*result);

        writedoc! {f, "
            let {result} = match {eval_fn}(env.{relation_snake}_table, {func_args}) {{
                Some(res) => res,
                None => {{
                    env.new_{relation_snake}_def.push([{func_args}]);
                    break;
                }},
            }};
        "}?;
        Ok(())
    })
}

fn display_range_expr<'a>(
    expr: &'a FlatRangeExpr,
    eqlog: &'a Eqlog,
    identifiers: &'a BTreeMap<Ident, String>,
) -> impl 'a + Display {
    FmtFn(move |f: &mut Formatter| -> Result {
        match expr {
            FlatRangeExpr::Index(index_expr) => {
                let FlatIndexRangeExpr { rel, index } = index_expr;
                let getter_fn = display_index_getter_fn_name(index, *rel, eqlog, identifiers);
                let rel_snake = display_rel(*rel, eqlog, identifiers)
                    .to_string()
                    .to_case(Snake);
                write!(f, "Some({getter_fn}(&env.{rel_snake}_table))")
            }
            FlatRangeExpr::Restriction(restriction_expr) => {
                let FlatRangeRestrictionExpr {
                    range_var,
                    first_projection,
                } = restriction_expr;

                let range_var = display_range_var(*range_var);
                let first_projection = display_var(*first_projection);

                write!(f, "{range_var}.get({first_projection})")
            }
        }
    })
}

fn display_stmts<'a>(
    stmts: &'a [FlatStmt],
    analysis: &'a FlatRuleAnalysis<'a>,
    eqlog: &'a Eqlog,
    identifiers: &'a BTreeMap<Ident, String>,
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
                let if_header = display_if_stmt_header(if_stmt, analysis, eqlog, identifiers);
                let if_footer = "}";
                let tail = display_stmts(tail, analysis, eqlog, identifiers);
                writedoc! {f, "
                    {if_header}
                    {tail}
                    {if_footer}
                "}?;
            }
            FlatStmt::DefineRange(FlatDefineRangeStmt {
                defined_var,
                expression,
            }) => {
                let tail = display_stmts(tail, analysis, eqlog, identifiers);
                let expression = display_range_expr(expression, eqlog, identifiers);
                let defined_var = display_range_var(*defined_var);

                writedoc! {f, "
                    if let Some({defined_var}) = {expression} {{
                    {tail}
                    }}
                "}?;
            }
            FlatStmt::SurjThen(surj_then) => {
                let tail = display_stmts(tail, analysis, eqlog, identifiers);
                let surj_then = display_surj_then(surj_then, analysis, eqlog, identifiers);
                writedoc! {f, "
                    {surj_then}
                    {tail}
                "}?;
            }
            FlatStmt::NonSurjThen(non_surj_then) => {
                let tail = display_stmts(tail, analysis, eqlog, identifiers);
                let non_surj_then = display_non_surj_then(non_surj_then, eqlog, identifiers);
                writedoc! {f, "
                    {non_surj_then}
                    {tail}
                "}?;
            }
            FlatStmt::Call {
                func_name,
                args,
                range_args,
            } => {
                let rule_name = analysis.rule_name;
                let i = func_name.0;
                let args = args
                    .iter()
                    .copied()
                    .map(|var| FmtFn(move |f| write!(f, "{}, ", display_var(var))))
                    .format("");
                let range_args = range_args
                    .iter()
                    .copied()
                    .map(|var| FmtFn(move |f| write!(f, "{}, ", display_range_var(var))))
                    .format("");
                let tail = display_stmts(tail, analysis, eqlog, identifiers);
                writedoc! {f, "
                    {rule_name}_{i}(env, {args} {range_args});
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
    range_var_types: &'a BTreeMap<FlatRangeVar, FlatRangeType>,
    eqlog: &'a Eqlog,
    identifiers: &'a BTreeMap<Ident, String>,
) -> impl 'a + Display {
    FmtFn(move |f: &mut Formatter| -> Result {
        let func_name = flat_func.name.0;
        let rule_camel = rule_name.to_case(UpperCamel);

        let var_args = flat_func
            .args
            .iter()
            .copied()
            .map(|var| {
                FmtFn(move |f| {
                    let var_name = display_var(var);
                    write!(f, "{var_name}: u32, ")
                })
            })
            .format("");

        let range_args = flat_func
            .range_args
            .iter()
            .copied()
            .map(|var| {
                FmtFn(move |f| {
                    let var_name = display_range_var(var);
                    let range_type = *range_var_types.get(&var).unwrap();
                    let range_type = display_range_type(range_type);
                    write!(f, "{var_name}: {range_type}, ")
                })
            })
            .format("");

        let stmts = display_stmts(flat_func.body.as_slice(), analysis, eqlog, identifiers);

        writedoc! {f, "
            #[allow(unused_variables)]
            fn {rule_name}_{func_name}(env: &mut {rule_camel}Env, {var_args} {range_args}) {{
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
*/

pub fn display_module_main_fn_name<'a>(ram_module: &'a RamModule) -> impl 'a + Display {
    ram_module.name.to_case(Snake)
}

fn display_module_main_fn_signature<'a>(ram_module: &'a RamModule) -> impl 'a + Display {
    FmtFn(move |f| {
        let fn_name = display_module_main_fn_name(ram_module);
        let env_name = display_module_env_struct_name(ram_module);

        write!(f, "fn {fn_name}(env: {env_name})")
    })
}

pub fn display_module_main_fn_decl<'a>(
    ram_module: &'a RamModule,
    symbol_prefix: &'a str,
) -> impl 'a + Display {
    FmtFn(move |f| {
        let fn_name = display_module_main_fn_name(ram_module);
        let signature = display_module_main_fn_signature(ram_module);
        writedoc! {f, r#"
            #[link_name = "{symbol_prefix}_{fn_name}"]
            safe {signature};
        "#}
    })
}

fn display_module_main_fn<'a>(
    ram_module: &'a RamModule,
    symbol_prefix: &'a str,
) -> impl 'a + Display {
    FmtFn(move |f| {
        let fn_name = display_module_main_fn_name(ram_module);
        let signature = display_module_main_fn_signature(ram_module);
        writedoc! {f, r#"
            #[link_name = "{symbol_prefix}_{fn_name}"]
            pub {signature} {{
            todo!()
            }}
        "#}
    })
}

pub fn display_ram_module<'a>(
    ram_module: &'a RamModule,
    _index_selection: &'a IndexSelection,
    eqlog: &'a Eqlog,
    identifiers: &'a BTreeMap<Ident, String>,
    symbol_prefix: &'a str,
) -> impl 'a + Display {
    FmtFn(move |f: &mut Formatter| -> Result {
        let imports = display_imports();
        let env_struct = display_module_env_struct(ram_module, eqlog, identifiers);
        let main_fn = display_module_main_fn(ram_module, symbol_prefix);

        writedoc! {f, r#"
            {imports}
            {env_struct}
            {main_fn}
        "#}
    })
}

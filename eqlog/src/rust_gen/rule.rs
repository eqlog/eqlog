use crate::flat_eqlog::*;
use crate::fmt_util::*;
use crate::rust_gen::flat_eqlog::display_flat_rule;
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
                        RamStmt::Iter(_) | RamStmt::Insert(_) | RamStmt::GuardInhabited(_) => {
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
                        RamStmt::DefineSet(_) | RamStmt::Iter(_) | RamStmt::GuardInhabited(_) => {
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

impl Display for SetVar {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        self.name.fmt(f)
    }
}

fn display_in_set_expr<'a>(
    expr: &'a InSetExpr,
    eqlog: &'a Eqlog,
    identifiers: &'a BTreeMap<Ident, String>,
) -> impl 'a + Display {
    FmtFn(move |f| match expr {
        InSetExpr::GetIndex(GetIndexExpr { rel, index_spec }) => {
            let index_field = display_index_field_name(rel, index_spec, eqlog, identifiers);
            write!(f, "env.{index_field}")
        }
        InSetExpr::Restrict(RestrictExpr {
            set,
            first_column_var,
        }) => {
            let result_arity = set.arity - 1;
            write!(f, "{set}.get({first_column_var}).unwrap_or_else(|| PrefixTree{result_arity}::empty())")
        }
    })
}

fn display_stmt_pre<'a>(
    ram_stmt: &'a RamStmt,
    eqlog: &'a Eqlog,
    identifiers: &'a BTreeMap<Ident, String>,
) -> impl 'a + Display {
    FmtFn(move |f| {
        match ram_stmt {
            RamStmt::DefineSet(DefineSetStmt { defined_var, expr }) => {
                let expr = display_in_set_expr(expr, eqlog, identifiers);
                match defined_var.strictness {
                    Strictness::Lazy => {
                        writedoc! {f, "
                            let {defined_var} =
                            LazyCell::new(|| {{
                            {expr}
                            }});
                            ;
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
            RamStmt::Iter(IterStmt {
                sets,
                loop_var_el,
                loop_var_set,
            }) => {
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
                let set_head = sets[0].clone();
                let set_tail_chain_iters = sets[1..]
                    .iter()
                    .map(|set| FmtFn(move |f| write!(f, ".chain({set}.iter_restrictions())")))
                    .format("\n");
                writedoc! {f, "
                    #[allow(unused_variables)]
                    for
                    ({loop_var_el}, {loop_var_set})
                    in
                    {set_head}.iter_restrictions()
                    {set_tail_chain_iters}
                    {{
                "}
            }
            RamStmt::Insert(InsertStmt { rel, args }) => {
                let rel_field = display_out_set_field_name(rel, eqlog, identifiers);
                let args = args.iter().format(", ");
                // TODO: Check that this row doesn't exist already in indices.
                writedoc! {f, "
                    env.{rel_field}.push([{args}]);
                "}
            }
            RamStmt::GuardInhabited(GuardInhabitedStmt { sets }) => {
                let checks = sets
                    .iter()
                    .map(|set| {
                        FmtFn(move |f| {
                            let set_name = &set.name;
                            write!(f, "|| !{set_name}.is_empty()")
                        })
                    })
                    .format("");
                writedoc! {f, "
                    if false {checks} {{
                "}
            }
        }
    })
}

fn display_stmt_post<'a>(ram_stmt: &'a RamStmt) -> impl 'a + Display {
    FmtFn(move |f| match ram_stmt {
        RamStmt::DefineSet(_) | RamStmt::Insert(_) => Ok(()),
        RamStmt::Iter(_) | RamStmt::GuardInhabited(_) => {
            writedoc! {f, "
                    }}
                "}
        }
    })
}

fn display_routine<'a>(
    RamRoutine {
        name,
        flat_rule,
        stmts,
    }: &'a RamRoutine,
    ram_module: &'a RamModule,
    eqlog: &'a Eqlog,
    identifiers: &'a BTreeMap<Ident, String>,
) -> impl 'a + Display {
    FmtFn(move |f| {
        let name = name;
        let env_type = display_module_env_struct_name(ram_module);

        let stmts_pre = stmts
            .iter()
            .map(|stmt| display_stmt_pre(stmt, eqlog, identifiers))
            .format("\n");
        let stmts_post = stmts
            .iter()
            .rev()
            .map(|stmt| display_stmt_post(stmt))
            .format("\n");

        let flat_rule = display_flat_rule(flat_rule, eqlog, identifiers).to_string();
        let flat_rule_comment = flat_rule
            .lines()
            .map(|line| FmtFn(move |f| write!(f, "// {line}")))
            .format("\n");

        writedoc! {f, "
            {flat_rule_comment}
            fn {name}(env: &mut {env_type}) {{
            {stmts_pre}
            {stmts_post}
            }}
        "}
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
    symbol_prefix: &'a str,
) -> impl 'a + Display {
    FmtFn(move |f| {
        let fn_name = display_module_main_fn_name(ram_module);
        let env_name = display_module_env_struct_name(ram_module);
        let calls = ram_module
            .routines
            .iter()
            .map(|routine| {
                FmtFn(move |f| {
                    let name = &routine.name;
                    write!(f, "{name}(&mut env);")
                })
            })
            .format("\n");
        writedoc! {f, r#"
            #[unsafe(no_mangle)]
            pub fn {symbol_prefix}_{fn_name}(mut env: {env_name}) {{
            {calls}
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
        let routines = ram_module
            .routines
            .iter()
            .map(|routine| display_routine(routine, ram_module, eqlog, identifiers))
            .format("\n");

        writedoc! {f, r#"
            {imports}
            {env_struct}
            {routines}
            {main_fn}
        "#}
    })
}

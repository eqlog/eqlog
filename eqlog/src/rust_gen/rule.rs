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
            use std::collections::BTreeSet;
            use std::collections::btree_set;
        "}
    })
}

fn display_rule_env_struct<'a>(
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

        let delta_new_rel_fields = analysis
            .used_rels
            .iter()
            .map(|rel| {
                FmtFn(move |f: &mut Formatter| {
                    let rel_snake = display_rel(*rel, eqlog, identifiers)
                        .to_string()
                        .to_case(Snake);
                    let row_type = display_rel_row_type(*rel, eqlog);
                    writedoc! {f, "
                    delta_new_{rel_snake}: &'a mut Vec<{row_type}>,
                "}?;
                    if let RelCase::FuncRel(func) = eqlog.rel_case(*rel) {
                        let args_type = display_func_args_type(func, eqlog);
                        writedoc! {f, "
                        delta_new_{rel_snake}_def: &'a mut Vec<{args_type}>,
                    "}?;
                    }
                    Ok(())
                })
            })
            .format("\n");

        let delta_new_type_equalities_fields = analysis
            .used_types
            .iter()
            .map(|typ| {
                FmtFn(move |f: &mut Formatter| {
                    let type_snake = display_type(*typ, eqlog, identifiers)
                        .to_string()
                        .to_case(Snake);
                    writedoc! {f, "
                        delta_new_{type_snake}_equalities: &'a mut Vec<(u32, u32)>,
                    "}
                })
            })
            .format("\n");

        writedoc! {f, "
            #[allow(unused)]
            struct {rule_name_camel}Env<'a> {{
                {table_fields}
                {type_set_fields}
                {delta_new_rel_fields}
                {delta_new_type_equalities_fields}
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
) -> impl 'a + Display {
    FmtFn(move |f: &mut Formatter| -> Result {
        let used_queries = &analysis.used_queries;

        let iter_fns = used_queries
            .iter()
            .map(|(rel, query_spec)| {
                let rel_name = display_rel(*rel, eqlog, identifiers).to_string();
                let query_indices = index_selection.get(&rel_name).unwrap();
                let indices = query_indices.get(query_spec).unwrap();

                FmtFn(move |f: &mut Formatter| -> Result {
                    let iter_fn_decl =
                        display_iter_fn_decl(query_spec, indices, *rel, eqlog, identifiers, "");
                    let iter_next_fn_decl = display_iter_next_fn_decl(
                        query_spec,
                        indices,
                        *rel,
                        eqlog,
                        identifiers,
                        "",
                    );

                    writedoc! {f, "
                        {iter_fn_decl}
                        {iter_next_fn_decl}
                    "}
                })
            })
            .format("\n");

        writedoc! {f, r#"
            unsafe extern "Rust" {{
            {iter_fns}
            }}
        "#}
    })
}

pub fn display_rule_lib<'a>(
    _rule: &'a FlatRule,
    analysis: &'a FlatRuleAnalysis<'a>,
    index_selection: &'a IndexSelection,
    eqlog: &'a Eqlog,
    identifiers: &'a BTreeMap<Ident, String>,
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
        let iter_fns = display_rule_iter_fns(analysis, index_selection, eqlog, identifiers);

        writedoc! {f, "
            {imports}
            {table_struct_decls}
            {iter_types}
            {iter_fns}
            {env_struct}
        "}
    })
}

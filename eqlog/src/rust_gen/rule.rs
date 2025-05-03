use crate::eqlog_util::*;
use crate::flat_eqlog::*;
use crate::fmt_util::*;
use crate::rust_gen::*;
use convert_case::{Case, Casing};
use eqlog_eqlog::*;
use indoc::writedoc;
use std::collections::BTreeMap;
use std::fmt::{Display, Formatter, Result};

use Case::{Snake, UpperCamel};

fn display_imports<'a>() -> impl 'a + Display {
    FmtFn(move |f: &mut Formatter| -> Result {
        writedoc! {f, "
            use std::collections::BTreeSet;
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

pub fn display_rule_lib<'a>(
    _rule: &'a FlatRule,
    analysis: &'a FlatRuleAnalysis<'a>,
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

        writedoc! {f, "
            {imports}
            {table_struct_decls}
            {env_struct}
        "}
    })
}

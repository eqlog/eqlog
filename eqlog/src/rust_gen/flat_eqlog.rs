use std::{collections::BTreeMap, fmt::Display};

use eqlog_eqlog::Ident;
use indoc::writedoc;
use itertools::Itertools;

use crate::{
    flat_eqlog::{FlatIfStmt, FlatOutRel, FlatRule, FlatThenStmt, QueryAge},
    fmt_util::FmtFn,
    rust_gen::display_type,
    rust_gen::EqlogIds,
};

fn display_flat_if_stmt<'a>(
    stmt: &'a FlatIfStmt,
    eqlog_ids: &'a EqlogIds<'a>,
    identifiers: &'a BTreeMap<Ident, String>,
) -> impl 'a + Display {
    FmtFn(move |f| {
        let eqlog = eqlog_ids.eqlog();
        let rel_name = match &stmt.rel {
            crate::flat_eqlog::FlatInRel::Rel(rel) => {
                crate::rust_gen::display_rel(eqlog_ids.flat_rel(*rel), eqlog, identifiers)
                    .to_string()
            }
            crate::flat_eqlog::FlatInRel::RelWithDiagonals { rel, equalities } => {
                format!(
                    "{}[diag={}]",
                    crate::rust_gen::display_rel(eqlog_ids.flat_rel(*rel), eqlog, identifiers),
                    equalities.iter().format(",")
                )
            }
            crate::flat_eqlog::FlatInRel::Equality(typ) => {
                format!(
                    "{}=={}",
                    display_type(eqlog_ids.typ(*typ), eqlog, identifiers),
                    display_type(eqlog_ids.typ(*typ), eqlog, identifiers)
                )
            }
            crate::flat_eqlog::FlatInRel::TypeSet(typ) => {
                format!(
                    "{}Set",
                    display_type(eqlog_ids.typ(*typ), eqlog, identifiers)
                )
            }
        };

        let age_str = match stmt.age {
            QueryAge::New => "new",
            QueryAge::Old => "old",
            QueryAge::All => "all",
        };

        let args = stmt.args.iter().map(|var| var.name.as_ref()).format(", ");
        write!(f, "- {rel_name}({args}) [{age_str}]")
    })
}

fn display_flat_then_stmt<'a>(
    stmt: &'a FlatThenStmt,
    eqlog_ids: &'a EqlogIds<'a>,
    identifiers: &'a BTreeMap<Ident, String>,
) -> impl 'a + Display {
    FmtFn(move |f| {
        let eqlog = eqlog_ids.eqlog();
        let rel_name = match stmt.rel {
            FlatOutRel::Rel(rel) => {
                crate::rust_gen::display_rel(eqlog_ids.flat_rel(rel), eqlog, identifiers)
                    .to_string()
            }
            FlatOutRel::Equality(typ) => {
                format!(
                    "{}=={}",
                    display_type(eqlog_ids.typ(typ), eqlog, identifiers),
                    display_type(eqlog_ids.typ(typ), eqlog, identifiers)
                )
            }
            FlatOutRel::FuncDomain(func) => {
                let rel = eqlog_ids.func_rel(func);
                format!(
                    "{}Def",
                    crate::rust_gen::display_rel(rel, eqlog, identifiers)
                )
            }
        };

        let args = stmt.args.iter().map(|var| var.name.as_ref()).format(", ");
        write!(f, "- {rel_name}({args})")
    })
}

pub fn display_flat_rule<'a>(
    FlatRule {
        name,
        premise,
        conclusion,
    }: &'a FlatRule,
    eqlog_ids: &'a EqlogIds<'a>,
    identifiers: &'a BTreeMap<Ident, String>,
) -> impl 'a + Display {
    FmtFn(move |f| {
        let premise = premise
            .iter()
            .map(move |stmt| display_flat_if_stmt(stmt, eqlog_ids, identifiers))
            .format("\n");

        let conclusion = conclusion
            .iter()
            .map(move |stmt| display_flat_then_stmt(stmt, eqlog_ids, identifiers))
            .format("\n");

        writedoc! {f, "
            rule {name}:
            if:
            {premise}
            then:
            {conclusion}
        "}
    })
}

use std::{collections::BTreeMap, fmt::Display};

use eqlog_eqlog::{Eqlog, Ident};
use indoc::writedoc;
use itertools::Itertools;

use crate::{
    flat_eqlog::{FlatIfStmt, FlatOutRel, FlatRule, FlatThenStmt, QueryAge},
    fmt_util::FmtFn,
    rust_gen::display_type,
};

fn display_flat_if_stmt<'a>(
    stmt: &'a FlatIfStmt,
    eqlog: &'a Eqlog,
    identifiers: &'a BTreeMap<Ident, String>,
) -> impl 'a + Display {
    FmtFn(move |f| {
        let rel_name = match &stmt.rel {
            crate::flat_eqlog::FlatInRel::EqlogRel(rel) => {
                crate::rust_gen::display_rel(*rel, eqlog, identifiers).to_string()
            }
            crate::flat_eqlog::FlatInRel::EqlogRelWithDiagonals { rel, equalities } => {
                format!(
                    "{}[diag={}]",
                    crate::rust_gen::display_rel(*rel, eqlog, identifiers),
                    equalities.iter().format(",")
                )
            }
            crate::flat_eqlog::FlatInRel::Equality(typ) => {
                format!(
                    "{}=={}",
                    display_type(*typ, eqlog, identifiers),
                    display_type(*typ, eqlog, identifiers)
                )
            }
            crate::flat_eqlog::FlatInRel::TypeSet(typ) => {
                format!("{}Set", display_type(*typ, eqlog, identifiers))
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
    eqlog: &'a Eqlog,
    identifiers: &'a BTreeMap<Ident, String>,
) -> impl 'a + Display {
    FmtFn(move |f| {
        let rel_name = match stmt.rel {
            FlatOutRel::EqlogRel(rel) => {
                crate::rust_gen::display_rel(rel, eqlog, identifiers).to_string()
            }
            FlatOutRel::Equality(typ) => {
                format!(
                    "{}=={}",
                    display_type(typ, eqlog, identifiers),
                    display_type(typ, eqlog, identifiers)
                )
            }
            FlatOutRel::FuncDomain(func) => {
                let rel = eqlog.func_rel(func).unwrap();
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
    eqlog: &'a Eqlog,
    identifiers: &'a BTreeMap<Ident, String>,
) -> impl 'a + Display {
    FmtFn(move |f| {
        let premise = premise
            .iter()
            .map(move |stmt| display_flat_if_stmt(stmt, eqlog, identifiers))
            .format("\n");

        let conclusion = conclusion
            .iter()
            .map(move |stmt| display_flat_then_stmt(stmt, eqlog, identifiers))
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

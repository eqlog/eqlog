use std::fmt::Display;

use indoc::writedoc;
use itertools::Itertools;

use crate::{
    flat_eqlog::{FlatIfStmt, FlatOutRel, FlatRule, FlatThenStmt, QueryAge},
    fmt_util::FmtFn,
    rust_gen::{display_rel, display_type, RustGenCtx},
};

fn display_flat_if_stmt<'a>(stmt: &'a FlatIfStmt, ctx: &'a RustGenCtx<'a>) -> impl 'a + Display {
    FmtFn(move |f| {
        let rel_name = match &stmt.rel {
            crate::flat_eqlog::FlatInRel::Rel(rel) => display_rel(*rel, ctx).to_string(),
            crate::flat_eqlog::FlatInRel::RelWithDiagonals { rel, equalities } => {
                format!(
                    "{}[diag={}]",
                    display_rel(*rel, ctx),
                    equalities.iter().format(",")
                )
            }
            crate::flat_eqlog::FlatInRel::Equality(typ) => {
                format!("{}=={}", display_type(*typ, ctx), display_type(*typ, ctx))
            }
            crate::flat_eqlog::FlatInRel::TypeSet(typ) => {
                format!("{}Set", display_type(*typ, ctx))
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
    ctx: &'a RustGenCtx<'a>,
) -> impl 'a + Display {
    FmtFn(move |f| {
        let rel_name = match stmt.rel {
            FlatOutRel::Rel(rel) => display_rel(rel, ctx).to_string(),
            FlatOutRel::Equality(typ) => {
                format!("{}=={}", display_type(typ, ctx), display_type(typ, ctx))
            }
            FlatOutRel::FuncDomain(func) => {
                format!(
                    "{}Def",
                    display_rel(crate::flat_eqlog::FlatRel::Func(func), ctx)
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
    ctx: &'a RustGenCtx<'a>,
) -> impl 'a + Display {
    FmtFn(move |f| {
        let premise = premise
            .iter()
            .map(move |stmt| display_flat_if_stmt(stmt, ctx))
            .format("\n");

        let conclusion = conclusion
            .iter()
            .map(move |stmt| display_flat_then_stmt(stmt, ctx))
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

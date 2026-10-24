use std::collections::BTreeMap;
use std::fmt::Display;

use convert_case::{Case, Casing};
use indoc::writedoc;
use itertools::Itertools;

use super::{display_element_index_field_name, display_weight_static_name, indexed, RustGenCtx};
use crate::algebra::signature::TypeId;
use crate::flat_eqlog::FlatRel;
use crate::fmt_util::FmtFn;
use crate::options::ModelMode;

pub(super) fn weights<'a>(
    rel: FlatRel,
    args: &'a [String],
    ctx: &'a RustGenCtx<'a>,
) -> impl Display + 'a {
    FmtFn(move |f| {
        let weight = display_weight_static_name(rel, ctx);
        for (i, (arg, typ)) in args.iter().zip(rel.arity(ctx.signature())).enumerate() {
            let name = ctx.type_name(typ).to_case(Case::Snake);
            writedoc! {f, "
                let weight{i} = &mut self.{name}_weights[usize::try_from({arg}).unwrap()];
                *weight{i} = weight{i}.saturating_add({weight});
            "}?;
        }
        Ok(())
    })
}

fn record(rel: FlatRel, typ: TypeId, element: &str, row: &str, ctx: &RustGenCtx<'_>) -> String {
    match ctx.model_mode() {
        ModelMode::Native => {
            let field = display_element_index_field_name(rel, typ, ctx);
            format!("self.{field}.entry({element}).or_default().push({row});")
        }
        ModelMode::Desugared => {
            let field = indexed::occurrences_field(typ, ctx);
            format!("self.{field}.push({element}, occurrence);")
        }
    }
}

pub(super) fn occurrences<'a>(
    rel: FlatRel,
    args: &'a [String],
    row: &'a str,
    imported: bool,
    ctx: &'a RustGenCtx<'a>,
) -> impl Display + 'a {
    FmtFn(move |f| {
        let mut positions: BTreeMap<TypeId, Vec<usize>> = BTreeMap::new();
        for (i, typ) in rel.arity(ctx.signature()).into_iter().enumerate() {
            positions.entry(typ).or_default().push(i);
        }
        for (typ, columns) in positions {
            for (i, &column) in columns.iter().enumerate() {
                let element = &args[column];
                let checks = columns[..i]
                    .iter()
                    .map(|&previous| {
                        let previous = &args[previous];
                        format!(" && {element} != {previous}")
                    })
                    .join("");
                let insert = record(rel, typ, element, row, ctx);
                writeln!(f, "if true{checks} {{ {insert}")?;
                let is_member = match rel {
                    FlatRel::ModelMember(member) => member == typ,
                    FlatRel::Pred(_) | FlatRel::Func(_) => false,
                };
                if imported && is_member {
                    // Imported membership may only be recorded under an alias.
                    let name = ctx.type_name(typ).to_case(Case::Snake);
                    let camel = ctx.type_name(typ).to_case(Case::UpperCamel);
                    let insert = record(rel, typ, "root", row, ctx);
                    writedoc! {f, "
                        let root = self.root_{name}({camel}({element})).0;
                        if root != {element} {{ {insert} }}
                    "}?;
                }
                writeln!(f, "}}")?;
            }
        }
        Ok(())
    })
}

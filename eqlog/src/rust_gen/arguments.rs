use convert_case::{Case, Casing};
use itertools::Itertools;

use super::RustGenCtx;
use crate::algebra::signature::TypeId;
use crate::ram::ElVar;

pub(super) fn declarations(args: &[ElVar], types: &[TypeId], ctx: &RustGenCtx<'_>) -> String {
    args.iter()
        .zip(types)
        .map(|(arg, &typ)| {
            let name = ctx.type_name(typ).to_case(Case::UpperCamel);
            format!("{arg}: {name}")
        })
        .join(", ")
}

pub(super) fn canonicalize(args: &[ElVar], types: &[TypeId], ctx: &RustGenCtx<'_>) -> String {
    args.iter()
        .zip(types)
        .map(|(arg, &typ)| {
            let name = ctx.type_name(typ).to_case(Case::Snake);
            format!("let {arg} = self.root_{name}({arg});")
        })
        .join("\n")
}

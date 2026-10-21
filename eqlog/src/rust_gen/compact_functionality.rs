use std::fmt::Display;

use convert_case::{Case, Casing};
use indoc::writedoc;

use super::{compact_indices, RustGenCtx};
use crate::algebra::signature::{FuncId, TypeId};
use crate::flat_eqlog::{functionality_anchor, FlatInRel, FlatRel, Stratum};
use crate::fmt_util::FmtFn;
use crate::ram::RamModule;

fn owner(func: FuncId, ctx: &RustGenCtx<'_>) -> Option<TypeId> {
    let rel = FlatRel::Func(func);
    let owner = compact_indices::owner(&FlatInRel::Rel(rel), ctx)?;
    let arity = rel.arity(ctx.signature());
    let (&result, arguments) = arity.split_last()?;
    // A quotient of outputs preserves functionality; a quotient of inputs may not.
    if !ctx.supports_compact_members(result)
        || !rel.column_maps_under(ctx.signature(), arguments.len(), owner)
        || (1..arguments.len()).any(|column| rel.column_maps_under(ctx.signature(), column, owner))
    {
        return None;
    }
    Some(owner)
}

pub(super) fn stratum_function(
    stratum: &Stratum,
    modules: &[RamModule],
    ctx: &RustGenCtx<'_>,
) -> Option<FuncId> {
    let [module] = stratum.groups.as_slice() else {
        return None;
    };
    let [routine] = modules[*module].routines.as_slice() else {
        return None;
    };
    functionality_anchor(&routine.flat_rule)?;
    let func = match routine.flat_rule.premise[0].rel {
        FlatInRel::Rel(FlatRel::Func(func)) => func,
        FlatInRel::Rel(FlatRel::Pred(_) | FlatRel::ModelMember(_))
        | FlatInRel::RelWithDiagonals { .. }
        | FlatInRel::TypeSet(_)
        | FlatInRel::Equality(_) => return None,
    };
    (Some(owner(func, ctx)?) == stratum.model).then_some(func)
}

fn functions<'a>(ctx: &'a RustGenCtx<'a>) -> impl Iterator<Item = FuncId> + 'a {
    ctx.signature()
        .iter_funcs()
        .filter(|&func| owner(func, ctx).is_some())
}

pub(super) fn fields<'a>(ctx: &'a RustGenCtx<'a>, initialize: bool) -> impl Display + 'a {
    FmtFn(move |f| {
        for func in functions(ctx) {
            let name = ctx.func_name(func).to_case(Case::Snake);
            if initialize {
                writeln!(f, "__compact_checked_{name}: BTreeMap::new(),")?;
            } else {
                writeln!(
                    f,
                    "__compact_checked_{name}: BTreeMap<u32, eqlog_runtime::__private::Table>,"
                )?;
            }
        }
        Ok(())
    })
}

pub(super) fn preserve<'a>(
    model: TypeId,
    ctx: &'a RustGenCtx<'a>,
    before: bool,
) -> impl Display + 'a {
    FmtFn(move |f| {
        for func in functions(ctx).filter(|&func| owner(func, ctx) == Some(model)) {
            let name = ctx.func_name(func).to_case(Case::Snake);
            if before {
                writeln!(
                    f,
                    "let checked_{name} = self.__compact_is_checked_{name}(owner);"
                )?;
            } else {
                writeln!(
                    f,
                    "if checked_{name} {{ self.__compact_certify_{name}(owner); }}"
                )?;
            }
        }
        Ok(())
    })
}

pub(super) fn methods<'a>(ctx: &'a RustGenCtx<'a>) -> impl Display + 'a {
    FmtFn(move |f| {
        for func in functions(ctx) {
            let model = owner(func, ctx).unwrap();
            let model_name = ctx.type_name(model).to_case(Case::Snake);
            let name = ctx.func_name(func).to_case(Case::Snake);
            let result = ctx.signature().func(func).codomain;
            let result_name = ctx.type_name(result).to_case(Case::Snake);
            let arity = FlatRel::Func(func).arity(ctx.signature()).len() - 1;
            let arguments = arity - 1;
            let key = if arguments == 0 { "_key" } else { "key" };
            writedoc! {f, "
                fn __compact_is_checked_{name}(&self, owner: u32) -> bool {{
                    self.__compact_primary_{name}(owner).is_some_and(|current|
                        self.__compact_checked_{name}.get(&owner)
                            .is_some_and(|checked| current.shares_storage_with(checked)))
                }}

                fn __compact_certify_{name}(&mut self, owner: u32) {{
                    if let Some(current) = self.__compact_primary_{name}(owner) {{
                        self.__compact_checked_{name}.insert(owner, current.clone());
                    }}
                }}

                fn __compact_normalize_{name}(&mut self, owner: u32) -> Option<bool> {{
                    let indices = self.__compact_indices_{model_name}.as_ref()?;
                    if !indices.has_owner(owner) {{ return Some(false); }}
                    if self.__compact_is_checked_{name}(owner) {{ return Some(false); }}
                    let current = self.__compact_primary_{name}(owner).unwrap();
                    if current.is_empty() {{
                        self.__compact_certify_{name}(owner);
                        return Some(false);
                    }}
                    let source = indices.source(owner)?;
                    if !self.__compact_is_checked_{name}(source) {{ return None; }}
                    let inherited = self.__compact_inherited_{name}(owner)?;
                    let checked = self.__compact_checked_{name}.get(&source)?;
                    if !inherited.shares_storage_with(checked) {{ return None; }}
                    let current: &PrefixTree{arity} = current.try_into().unwrap();
                    let keys: BTreeSet<[u32; {arguments}]> = self.__compact_local_{name}(owner).unwrap()
                        .iter().map(|row| row[..{arguments}].try_into().unwrap()).collect();
                    let mut equalities = Vec::new();
                    for {key} in keys {{
                        let values = current;
            "}?;
            for argument in 0..arguments {
                let remaining = arity - argument - 1;
                writeln!(f, "let values = values.get(key[{argument}]).unwrap_or_else(|| PrefixTree{remaining}::empty());")?;
            }
            writedoc! {f, "
                        let mut values = values.iter();
                        if let Some([first]) = values.next() {{
                            equalities.extend(values.map(|[other]| [first, other]));
                        }}
                    }}
                    let equalities: Vec<_> = equalities.into_iter().map(|[left, right]|
                        [self.__compact_{result_name}_uid(owner, left), self.__compact_{result_name}_uid(owner, right)]).collect();
                    for [left, right] in equalities {{ self.__equate_{result_name}(left, right); }}
                    self.__compact_certify_{name}(owner);
                    Some(true)
                }}
            "}?;
        }
        Ok(())
    })
}

use std::fmt::Display;

use convert_case::{Case, Casing};
use indoc::{formatdoc, writedoc};
use itertools::Itertools;

use super::{compact_indices, display_rel, RustGenCtx};
use crate::algebra::signature::TypeId;
use crate::flat_eqlog::{iter_flat_rels, FlatInRel, FlatRel};
use crate::fmt_util::FmtFn;

#[derive(Clone, Copy)]
enum View {
    Owned(TypeId),
    Membership(TypeId),
    Morphism { model: TypeId, member: TypeId },
}

fn view(rel: FlatRel, ctx: &RustGenCtx<'_>) -> Option<View> {
    match rel {
        FlatRel::ModelMember(member) => ctx
            .supports_compact_members(member)
            .then_some(View::Membership(member)),
        FlatRel::Func(func) => {
            if let Some(types) = ctx.signature().types_for_mor_app_func(func) {
                let model = types.model_type(ctx.signature());
                return (ctx.supports_compact_members(types.member_type)
                    && compact_indices::supports_model(model, ctx))
                .then_some(View::Morphism {
                    model,
                    member: types.member_type,
                });
            }
            compact_indices::owner(&FlatInRel::Rel(rel), ctx).map(View::Owned)
        }
        FlatRel::Pred(_) => compact_indices::owner(&FlatInRel::Rel(rel), ctx).map(View::Owned),
    }
}

pub(super) fn supports(rel: FlatRel, ctx: &RustGenCtx<'_>) -> bool {
    view(rel, ctx).is_some()
}

fn snake(typ: TypeId, ctx: &RustGenCtx<'_>) -> String {
    ctx.type_name(typ).to_case(Case::Snake)
}

fn camel(typ: TypeId, ctx: &RustGenCtx<'_>) -> String {
    ctx.type_name(typ).to_case(Case::UpperCamel)
}

fn uid_value(rel: FlatRel, model: TypeId, column: usize, ctx: &RustGenCtx<'_>) -> String {
    let typ = rel.arity(ctx.signature())[column];
    let name = snake(typ, ctx);
    if ctx.supports_compact_members(typ) && rel.column_maps_under(ctx.signature(), column, model) {
        format!("self.__compact_{name}_uid(owner, row[{}]).0", column - 1)
    } else {
        format!("row[{}]", column - 1)
    }
}

pub(super) fn methods<'a>(ctx: &'a RustGenCtx<'a>) -> impl Display + 'a {
    FmtFn(move |f| {
        for rel in iter_flat_rels(ctx.signature()) {
            let Some(view) = view(rel, ctx) else {
                continue;
            };
            let name = display_rel(rel, ctx).to_case(Case::Snake);
            let arity = rel.arity(ctx.signature()).len();
            let rows = match view {
                View::Owned(model) => {
                    let owner_name = snake(model, ctx);
                    let values = (1..arity)
                        .map(|column| uid_value(rel, model, column, ctx))
                        .join(", ");
                    let suffix_arity = arity - 1;
                    formatdoc! {"
                        self.__compact_indices_{owner_name}.as_ref().map(move |indices| {{
                            indices.owners().flat_map(move |owner| {{
                                let table = self.__compact_primary_{name}(owner)
                                    .expect(\"compact owners have every relation index\");
                                let tree: &PrefixTree{suffix_arity} = table.try_into().unwrap();
                                tree.iter().map(move |row| [owner, {values}])
                            }})
                        }})
                    "}
                }
                View::Membership(member) => {
                    let member_name = snake(member, ctx);
                    formatdoc! {"
                        self.__compact_members_{member_name}.as_ref().map(move |spaces| {{
                            spaces.owners().flat_map(move |owner| {{
                                spaces.iter(owner).map(move |member| [owner, member])
                            }})
                        }})
                    "}
                }
                View::Morphism { model, member } => {
                    let owner_name = snake(model, ctx);
                    let mor_camel = format!("{}Mor", camel(model, ctx));
                    let member_name = snake(member, ctx);
                    // Export keeps source aliases until their distinct target images
                    // have been equated by transport.
                    writedoc! {f, "
                        fn __compact_all_{name}(&self, canonical: bool)
                            -> Option<impl '_ + Iterator<Item = [u32; {arity}]>>
                        {{
                            let spaces = self.__compact_members_{member_name}.as_ref()?;
                            Some(self.__compact_adopted_{owner_name}.iter().flat_map(move |&morphism| {{
                                let source = self.{owner_name}_mor_dom({mor_camel}(morphism))
                                    .expect(\"total morphisms have a source\").0;
                                let target = self.{owner_name}_mor_cod({mor_camel}(morphism))
                                    .expect(\"total morphisms have a target\").0;
                                spaces.get_snapshot(source).into_iter().flat_map(move |snapshot| {{
                                    snapshot.domain().iter().filter_map(move |origin| {{
                                        if canonical && snapshot.root_origin(origin) != Some(origin) {{
                                            return None;
                                        }}
                                        let source = snapshot.handle(origin)?;
                                        let target = spaces.image(source, target)?;
                                        Some([morphism, source, target])
                                    }})
                                }})
                            }}))
                        }}
                    "}?;
                    format!("self.__compact_all_{name}(true)")
                }
            };
            let export_rows = match view {
                View::Owned(_) | View::Membership(_) => format!("self.__compact_rows_{name}()?"),
                View::Morphism { .. } => format!("self.__compact_all_{name}(false)?"),
            };
            let explicit_rows = match view {
                View::Owned(_) | View::Membership(_) => String::new(),
                View::Morphism { .. } => formatdoc! {"
                    for (morphism, source, target) in self.iter_{name}() {{
                        table.insert(&[morphism.0, source.0, target.0]);
                    }}
                "},
            };
            writedoc! {f, "
                fn __compact_rows_{name}(&self)
                    -> Option<impl '_ + Iterator<Item = [u32; {arity}]>>
                {{
                    {rows}
                }}

                fn __compact_export_{name}(&self) -> Option<eqlog_runtime::__private::Table> {{
                    let rows = {export_rows};
                    let mut table = eqlog_runtime::__private::Table::new({arity});
                    for row in rows {{ table.insert(&row); }}
                    {explicit_rows}
                    Some(table)
                }}
            "}?;
        }
        Ok(())
    })
}

pub(super) fn lookup<'a>(
    rel: FlatRel,
    function: bool,
    ctx: &'a RustGenCtx<'a>,
) -> impl Display + 'a {
    FmtFn(move |f| {
        let Some(view) = view(rel, ctx) else {
            return Ok(());
        };
        match view {
            View::Membership(member) => {
                let member_name = snake(member, ctx);
                let model = ctx.signature().type_(member).parents[0];
                let owner_name = snake(model, ctx);
                writedoc! {f, "
                    if let Some(spaces) = &self.__compact_members_{member_name} {{
                        return spaces.contains(self.root_{owner_name}(arg0).0, arg1.0);
                    }}
                "}
            }
            View::Morphism { model, member } => {
                let owner_name = snake(model, ctx);
                let member_name = snake(member, ctx);
                let member_camel = camel(member, ctx);
                writedoc! {f, "
                    if let Some(spaces) = &self.__compact_members_{member_name} {{
                        let morphism = self.root_{owner_name}_mor(arg0);
                        if self.__compact_adopted_{owner_name}.contains(&morphism.0) {{
                            let source = self.{owner_name}_mor_dom(morphism)?;
                            if spaces.owner(arg1.0) != Some(source.0) {{ return None; }}
                            let target = self.{owner_name}_mor_cod(morphism)?;
                            return spaces.image(spaces.root(arg1.0)?, target.0).map({member_camel});
                        }}
                    }}
                "}
            }
            View::Owned(model) => {
                let name = display_rel(rel, ctx).to_case(Case::Snake);
                let owner_name = snake(model, ctx);
                let arity = rel.arity(ctx.signature());
                let suffix_arity = arity.len() - 1;
                let input_len = arity.len() - usize::from(function);
                let missing = if function { "None" } else { "false" };
                writedoc! {f, "
                    if self.__compact_indices_{owner_name}.is_some() {{
                        let owner = self.root_{owner_name}(arg0).0;
                        let Some(table) = self.__compact_primary_{name}(owner) else {{ return {missing}; }};
                "}?;
                for (column, &typ) in arity.iter().enumerate().take(input_len).skip(1) {
                    let type_name = snake(typ, ctx);
                    if ctx.supports_compact_members(typ)
                        && rel.column_maps_under(ctx.signature(), column, model)
                    {
                        writedoc! {f, "
                            let Some(snapshot) = self.__compact_{type_name}_snapshot(owner) else {{ return {missing}; }};
                            let Some(value) = snapshot.root(arg{column}.0)
                                .and_then(|root| snapshot.origin(root)) else {{ return {missing}; }};
                            let value{column} = value;
                        "}?;
                    } else {
                        writeln!(
                            f,
                            "let value{column} = self.root_{type_name}(arg{column}).0;"
                        )?;
                    }
                }
                if function {
                    writeln!(
                        f,
                        "let set: &PrefixTree{suffix_arity} = table.try_into().unwrap();"
                    )?;
                    for column in 1..input_len {
                        writeln!(f, "let set = set.get(value{column})?;")?;
                    }
                    writeln!(f, "let [result] = set.iter().next()?;")?;
                    let output = arity.len() - 1;
                    let typ = arity[output];
                    let output_name = snake(typ, ctx);
                    let output_camel = camel(typ, ctx);
                    if ctx.supports_compact_members(typ)
                        && rel.column_maps_under(ctx.signature(), output, model)
                    {
                        writeln!(
                            f,
                            "return Some(self.__compact_{output_name}_uid(owner, result));"
                        )?;
                    } else {
                        writeln!(f, "return Some({output_camel}(result));")?;
                    }
                } else {
                    let values = (1..arity.len())
                        .map(|column| format!("value{column}"))
                        .join(", ");
                    writeln!(f, "return table.contains(&[{values}]);")?;
                }
                writeln!(f, "}}")
            }
        }
    })
}

pub(super) fn iter_expr(rel: FlatRel, legacy: String, row: &str, ctx: &RustGenCtx<'_>) -> String {
    let Some(view) = view(rel, ctx) else {
        return legacy;
    };
    let name = display_rel(rel, ctx).to_case(Case::Snake);
    let unpack = (0..rel.arity(ctx.signature()).len())
        .map(|column| format!("arg{column}"))
        .join(", ");
    let legacy = match view {
        View::Owned(_) | View::Membership(_) => {
            format!("(!compact_active).then(|| {legacy}).into_iter().flatten()")
        }
        View::Morphism { model, .. } => {
            let owner_name = snake(model, ctx);
            format!("{legacy}.filter(move |row| !compact_active || !self.__total_members_{owner_name}.contains(&row.0.0))")
        }
    };
    formatdoc! {"
        let compact = self.__compact_rows_{name}();
        let compact_active = compact.is_some();
        compact.into_iter().flatten().map(|[{unpack}]| {row})
            .chain({legacy})
    "}
}

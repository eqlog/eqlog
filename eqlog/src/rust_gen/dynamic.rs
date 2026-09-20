use std::collections::BTreeMap;
use std::fmt::Display;

use convert_case::{Case, Casing};
use indoc::writedoc;
use itertools::Itertools;

use crate::algebra::signature::{FuncId, TypeId, TypeKind};
use crate::flat_eqlog::{iter_flat_rels, FlatRel};
use crate::fmt_util::FmtFn;

use super::{display_element_index_field_name, RustGenCtx};

struct DynamicContext<'a> {
    ctx: &'a RustGenCtx<'a>,
    sorts: BTreeMap<TypeId, usize>,
}

impl DynamicContext<'_> {
    fn sort(&self, typ: TypeId) -> String {
        let id = self.sorts[&typ];
        format!("eqlog_runtime::dynamic::SortId({id})")
    }

    fn element(&self, typ: TypeId, index: &str) -> String {
        let sort = self.sort(typ);
        format!("eqlog_runtime::dynamic::Element {{ sort: {sort}, index: {index} }}")
    }

    fn qualified(&self, parents: &[TypeId], name: &str) -> String {
        parents
            .iter()
            .map(|&parent| self.ctx.type_name(parent))
            .chain(std::iter::once(name.to_owned()))
            .join("::")
    }

    fn function_kind(&self, func: FuncId) -> String {
        let signature = self.ctx.signature();
        let kind = if signature.iter_ctor_decls().any(|(_, ctor)| ctor == func) {
            "Constructor".to_owned()
        } else if let Some(types) = signature.types_for_mor_app_func(func) {
            let morphism = self.sort(types.morphism_type);
            let member = self.sort(types.member_type);
            format!("MorphismApplication {{ morphism: {morphism}, member: {member} }}")
        } else if let Some((_, ids)) = signature
            .iter_model_decls()
            .find(|(_, ids)| ids.dom == func || ids.cod == func)
        {
            let model = self.sort(ids.type_);
            if ids.dom == func {
                format!("MorphismDomain({model})")
            } else {
                format!("MorphismCodomain({model})")
            }
        } else {
            "Ordinary".to_owned()
        };
        format!("eqlog_runtime::dynamic::FunctionKind::{kind}")
    }

    fn signature(&self) -> impl Display + '_ {
        FmtFn(move |f| {
            writedoc! {f, "
                fn dynamic_signature() -> std::sync::Arc<eqlog_runtime::dynamic::Signature> {{
                    static SIGNATURE: std::sync::OnceLock<std::sync::Arc<eqlog_runtime::dynamic::Signature>> = std::sync::OnceLock::new();
                    SIGNATURE.get_or_init(|| std::sync::Arc::new(
                        eqlog_runtime::dynamic::Signature::new(vec![
            "}?;
            for typ in self.ctx.signature().iter_types() {
                let descriptor = self.ctx.signature().type_(typ);
                let name = self.qualified(&descriptor.parents, &self.ctx.type_name(typ));
                let parents = descriptor
                    .parents
                    .iter()
                    .map(|&parent| self.sort(parent))
                    .join(", ");
                let kind = match descriptor.kind {
                    TypeKind::Plain => "Plain".to_owned(),
                    TypeKind::Model => "Model".to_owned(),
                    TypeKind::Enum => "Enum".to_owned(),
                    TypeKind::Mor(model) => format!("Morphism({})", self.sort(model)),
                };
                writedoc! {f, "
                    eqlog_runtime::dynamic::Sort {{
                        name: {name:?}.into(),
                        kind: eqlog_runtime::dynamic::SortKind::{kind},
                        parents: vec![{parents}],
                    }},
                "}?;
            }
            writeln!(f, "], vec![")?;
            for rel in iter_flat_rels(self.ctx.signature()) {
                let (parents, kind) = match rel {
                    FlatRel::Pred(pred) => (
                        &self.ctx.signature().pred(pred).parents,
                        "Predicate".to_owned(),
                    ),
                    FlatRel::Func(func) => (
                        &self.ctx.signature().func(func).parents,
                        format!("Function({})", self.function_kind(func)),
                    ),
                    FlatRel::ModelMember(typ) => (
                        &self.ctx.signature().type_(typ).parents,
                        format!("Membership({})", self.sort(typ)),
                    ),
                };
                let name = self.qualified(parents, &self.ctx.rel_name(rel));
                let parents = parents.iter().map(|&parent| self.sort(parent)).join(", ");
                let arity = rel
                    .arity(self.ctx.signature())
                    .iter()
                    .map(|&typ| self.sort(typ))
                    .join(", ");
                writedoc! {f, "
                    eqlog_runtime::dynamic::Relation {{
                        name: {name:?}.into(),
                        kind: eqlog_runtime::dynamic::RelationKind::{kind},
                        parents: vec![{parents}],
                        arity: vec![{arity}],
                    }},
                "}?;
            }
            writedoc! {f, "
                        ]).expect(\"compiler generated a valid dynamic signature\")
                    )).clone()
                }}
            "}
        })
    }

    fn export(&self) -> impl Display + '_ {
        FmtFn(move |f| {
            writedoc! {f, "
                fn to_dynamic(&self) -> (eqlog_runtime::dynamic::DynamicModel, eqlog_runtime::dynamic::ElementMap) {{
                    let mut model = eqlog_runtime::dynamic::DynamicModel::new(
                        <Self as eqlog_runtime::dynamic::CompiledModel>::dynamic_signature()
                    );
                    let mut elements = eqlog_runtime::dynamic::ElementMap::new();
            "}?;
            // Owners must exist before their members, independently of signature ID order.
            let types = self
                .ctx
                .signature()
                .iter_types()
                .sorted_by_key(|&typ| self.ctx.signature().type_(typ).parents.len());
            for typ in types {
                let name = self.ctx.type_name(typ);
                let snake = name.to_case(Case::Snake);
                let camel = name.to_case(Case::UpperCamel);
                let sort = self.sort(typ);
                let source = self.element(typ, "el.0");
                let alias = self.element(typ, "index");
                let root = self.element(typ, &format!("self.root_{snake}({camel}(index)).0"));
                let parent_sorts = &self.ctx.signature().type_(typ).parents;
                let parent_binding = FmtFn(|f| {
                    if parent_sorts.is_empty() {
                        return Ok(());
                    }
                    let index =
                        display_element_index_field_name(FlatRel::ModelMember(typ), typ, self.ctx);
                    writedoc! {f, "
                        let parents = self.{index}.get(&el.0)
                            .and_then(|rows| rows.first())
                            .expect(\"a member representative has a membership row\");
                    "}
                });
                let parents = parent_sorts
                    .iter()
                    .enumerate()
                    .map(|(i, &parent)| {
                        let element = self.element(parent, &format!("parents[{i}]"));
                        format!("elements[&{element}]")
                    })
                    .join(", ");
                writedoc! {f, "
                    for el in self.iter_{snake}() {{
                        {parent_binding}
                        let target = model.new_element({sort}, &[{parents}])
                            .expect(\"compiled elements have valid parent chains\");
                        elements.insert({source}, target);
                    }}
                    for index in 0..u32::try_from(self.{snake}_equalities.len()).unwrap() {{
                        let target = elements[&{root}];
                        elements.insert({alias}, target);
                    }}
                "}?;
            }
            for (i, rel) in iter_flat_rels(self.ctx.signature()).enumerate() {
                let snake = self.ctx.rel_name(rel).to_case(Case::Snake);
                let arity = rel.arity(self.ctx.signature());
                if arity.is_empty() {
                    writedoc! {f, "
                        if self.{snake}() {{
                            model.insert(eqlog_runtime::dynamic::RelationId({i}), &[])
                                .expect(\"compiled nullary relation has valid arity\");
                        }}
                    "}?;
                    continue;
                }
                let args = (0..arity.len()).map(|i| format!("arg{i}")).join(", ");
                let pattern = if arity.len() == 1 {
                    args
                } else {
                    format!("({args})")
                };
                let tuple = arity
                    .iter()
                    .enumerate()
                    .map(|(i, &typ)| {
                        let element = self.element(typ, &format!("arg{i}.0"));
                        format!("elements[&{element}]")
                    })
                    .join(", ");
                writedoc! {f, "
                    for {pattern} in self.iter_{snake}() {{
                        model.insert(eqlog_runtime::dynamic::RelationId({i}), &[{tuple}])
                            .expect(\"compiled relation has valid carrier sorts and membership\");
                    }}
                "}?;
            }
            writedoc! {f, "
                    (model, elements)
                }}
            "}
        })
    }

    fn import(&self) -> impl Display + '_ {
        FmtFn(move |f| {
            writedoc! {f, "
                fn from_dynamic(source: &eqlog_runtime::dynamic::DynamicModel)
                    -> std::result::Result<(Self, eqlog_runtime::dynamic::ElementMap), eqlog_runtime::dynamic::Error>
                {{
                    if source.signature() != &<Self as eqlog_runtime::dynamic::CompiledModel>::dynamic_signature() {{
                        return Err(eqlog_runtime::dynamic::Error::SignatureMismatch);
                    }}
                    let mut model = Self::new();
                    let mut elements = eqlog_runtime::dynamic::ElementMap::new();
            "}?;
            let types = self
                .ctx
                .signature()
                .iter_types()
                .sorted_by_key(|&typ| self.ctx.signature().type_(typ).parents.len());
            for typ in types {
                let snake = self.ctx.type_name(typ).to_case(Case::Snake);
                let sort = self.sort(typ);
                let target = self.element(typ, "target.0");
                let parents = &self.ctx.signature().type_(typ).parents;
                let parent_binding = if parents.is_empty() {
                    ""
                } else {
                    "let parents = source.parents(el)?;"
                };
                let args = parents
                    .iter()
                    .enumerate()
                    .map(|(i, &parent)| {
                        let camel = self.ctx.type_name(parent).to_case(Case::UpperCamel);
                        format!("{camel}(elements[&parents[{i}]].index)")
                    })
                    .join(", ");
                writedoc! {f, "
                    for el in source.elements({sort})? {{
                        {parent_binding}
                        let target = model.new_{snake}_internal({args});
                        elements.insert(el, {target});
                    }}
                    for el in source.handles({sort})? {{
                        let target = elements[&source.root(el)?];
                        elements.insert(el, target);
                    }}
                "}?;
            }
            for (i, rel) in iter_flat_rels(self.ctx.signature()).enumerate() {
                let insert = self.ctx.internal_insert_name(rel);
                let args = rel
                    .arity(self.ctx.signature())
                    .iter()
                    .enumerate()
                    .map(|(i, &typ)| {
                        let camel = self.ctx.type_name(typ).to_case(Case::UpperCamel);
                        format!("{camel}(elements[&tuple[{i}]].index)")
                    })
                    .join(", ");
                writedoc! {f, "
                    for tuple in source.tuples(eqlog_runtime::dynamic::RelationId({i}))? {{
                        let _ = &tuple;
                        model.{insert}({args});
                    }}
                "}?;
            }
            writedoc! {f, "
                    Ok((model, elements))
                }}
            "}
        })
    }
}

pub(super) fn display_dynamic_impl<'a>(
    name: &'a str,
    ctx: &'a RustGenCtx<'a>,
) -> impl Display + 'a {
    FmtFn(move |f| {
        let dynamic = DynamicContext {
            ctx,
            sorts: ctx
                .signature()
                .iter_types()
                .enumerate()
                .map(|(i, typ)| (typ, i))
                .collect(),
        };
        let signature = dynamic.signature();
        let export = dynamic.export();
        let import = dynamic.import();
        writedoc! {f, "
            #[allow(unused_mut)]
            impl eqlog_runtime::dynamic::CompiledModel for {name} {{
                {signature}
                {export}
                {import}
            }}
        "}
    })
}

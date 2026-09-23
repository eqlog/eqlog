use std::collections::BTreeMap;
use std::fmt::Display;

use convert_case::{Case, Casing};
use indoc::writedoc;
use itertools::Itertools;

use crate::algebra::signature::{FuncId, TypeId, TypeKind};
use crate::flat_eqlog::{
    iter_flat_rels, FlatInRel, FlatRel, IndexAge, IndexSelection, IndexSpec, QuerySpec,
};
use crate::fmt_util::FmtFn;

use super::{
    display_all_index_field_name, display_element_index_field_name, display_index_expr,
    display_index_field_name, display_own_index_field_name, display_weight_static_name, RustGenCtx,
};

struct DynamicContext<'a> {
    ctx: &'a RustGenCtx<'a>,
    indices: &'a IndexSelection,
    types: BTreeMap<TypeId, usize>,
}

impl DynamicContext<'_> {
    fn type_(&self, typ: TypeId) -> String {
        let id = self.types[&typ];
        format!("eqlog_runtime::TypeId({id})")
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
            let morphism = self.type_(types.morphism_type);
            let member = self.type_(types.member_type);
            format!("MorphismApplication {{ morphism: {morphism}, member: {member} }}")
        } else if let Some((_, ids)) = signature
            .iter_model_decls()
            .find(|(_, ids)| ids.dom == func || ids.cod == func)
        {
            let model = self.type_(ids.type_);
            if ids.dom == func {
                format!("MorphismDomain({model})")
            } else {
                format!("MorphismCodomain({model})")
            }
        } else {
            "Ordinary".to_owned()
        };
        format!("eqlog_runtime::FunctionKind::{kind}")
    }

    fn signature(&self) -> impl Display + '_ {
        FmtFn(move |f| {
            writedoc! {f, "
                fn dynamic_signature() -> std::sync::Arc<eqlog_runtime::Signature> {{
                    static SIGNATURE: std::sync::OnceLock<std::sync::Arc<eqlog_runtime::Signature>> = std::sync::OnceLock::new();
                    SIGNATURE.get_or_init(|| std::sync::Arc::new(
                        eqlog_runtime::Signature::new(vec![
            "}?;
            for typ in self.ctx.signature().iter_types() {
                let descriptor = self.ctx.signature().type_(typ);
                let name = self.qualified(&descriptor.parents, &self.ctx.type_name(typ));
                let parents = descriptor
                    .parents
                    .iter()
                    .map(|&parent| self.type_(parent))
                    .join(", ");
                let kind = match descriptor.kind {
                    TypeKind::Plain => "Plain".to_owned(),
                    TypeKind::Model => "Model".to_owned(),
                    TypeKind::Enum => "Enum".to_owned(),
                    TypeKind::Mor(model) => format!("Morphism({})", self.type_(model)),
                };
                writedoc! {f, "
                    eqlog_runtime::Type {{
                        name: {name:?}.into(),
                        kind: eqlog_runtime::TypeKind::{kind},
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
                        format!("Membership({})", self.type_(typ)),
                    ),
                };
                let name = self.qualified(parents, &self.ctx.rel_name(rel));
                let parents = parents.iter().map(|&parent| self.type_(parent)).join(", ");
                let arity = rel
                    .arity(self.ctx.signature())
                    .iter()
                    .map(|&typ| self.type_(typ))
                    .join(", ");
                writedoc! {f, "
                    eqlog_runtime::Relation {{
                        name: {name:?}.into(),
                        kind: eqlog_runtime::RelationKind::{kind},
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

    fn primary(&self, rel: FlatInRel, age: IndexAge) -> &IndexSpec {
        self.indices
            .queries
            .get(&(rel, QuerySpec::all()))
            .expect("primary index query")
            .iter()
            .filter(|index| index.age == age)
            .exactly_one()
            .expect("one primary index per age")
    }

    fn export(&self) -> impl Display + '_ {
        FmtFn(move |f| {
            writedoc! {f, "
                fn to_dynamic(&self) -> eqlog_runtime::Model {{
                    eqlog_runtime::__private::from_parts(
                        <Self as eqlog_runtime::CompiledModel>::dynamic_signature(),
                        vec![
            "}?;
            for typ in self.ctx.signature().iter_types() {
                let snake = self.ctx.type_name(typ).to_case(Case::Snake);
                let rel = FlatInRel::TypeSet(typ);
                let new =
                    display_index_expr(&rel, self.primary(rel.clone(), IndexAge::New), self.ctx);
                let old =
                    display_index_expr(&rel, self.primary(rel.clone(), IndexAge::Old), self.ctx);
                writedoc! {f, "
                    eqlog_runtime::__private::TypeData {{
                        equalities: self.{snake}_equalities.retype(),
                        new: (*{new}).clone(),
                        old: (*{old}).clone(),
                        weights: self.{snake}_weights.clone(),
                        uprooted: self.{snake}_uprooted.iter().map(|el| el.0).collect(),
                    }},
                "}?;
            }
            writeln!(f, "], vec![")?;
            for rel in iter_flat_rels(self.ctx.signature()) {
                let weight = display_weight_static_name(rel, self.ctx);
                writeln!(
                    f,
                    "eqlog_runtime::__private::RelationData {{ weight: {weight},"
                )?;
                for age in [IndexAge::New, IndexAge::Old] {
                    let flat = FlatInRel::Rel(rel);
                    let index = self.primary(flat.clone(), age);
                    let expression = display_index_expr(&flat, index, self.ctx);
                    let order = index.order.iter().join(", ");
                    writedoc! {f, "
                        {age}: eqlog_runtime::__private::RelationIndex {{
                            order: vec![{order}],
                            table: eqlog_runtime::__private::Table::from((*{expression}).clone()),
                        }},
                    "}?;
                }
                writeln!(f, "}},")?;
            }
            writedoc! {f, "
                        ]
                    ).expect(\"compiled indices contain valid handles\")
                }}
            "}
        })
    }

    fn import(&self) -> impl Display + '_ {
        FmtFn(move |f| {
            writedoc! {f, "
                fn from_dynamic(source: &eqlog_runtime::Model)
                    -> std::result::Result<Self, eqlog_runtime::Error>
                {{
                    if source.signature() != &<Self as eqlog_runtime::CompiledModel>::dynamic_signature() {{
                        return Err(eqlog_runtime::Error::SignatureMismatch);
                    }}
                    let mut model = Self::new();
            "}?;
            for typ in self.ctx.signature().iter_types() {
                let snake = self.ctx.type_name(typ).to_case(Case::Snake);
                let camel = self.ctx.type_name(typ).to_case(Case::UpperCamel);
                let type_ = self.type_(typ);
                let rel = FlatInRel::TypeSet(typ);
                let new = display_index_field_name(
                    &rel,
                    self.primary(rel.clone(), IndexAge::New),
                    self.ctx,
                );
                writedoc! {f, "
                    let data = eqlog_runtime::__private::type_data(source, {type_})?;
                    model.{snake}_equalities = data.equalities.retype();
                    model.{snake}_weights = vec![0; data.equalities.len()];
                    model.{new} = data.new.union(&data.old);
                    model.{snake}_uprooted = (0..data.equalities.len() as u32)
                        .filter(|&index| data.equalities.root_const(index) != index)
                        .map({camel})
                        .collect();
                "}?;
            }
            let relations: BTreeMap<_, _> = iter_flat_rels(self.ctx.signature())
                .enumerate()
                .map(|(id, rel)| (rel, id))
                .collect();
            for (flat, indices) in &self.indices.indices {
                let (rel, equalities) = match flat {
                    FlatInRel::Rel(rel) => (*rel, String::new()),
                    FlatInRel::RelWithDiagonals { rel, equalities } => {
                        (*rel, equalities.iter().join(", "))
                    }
                    FlatInRel::TypeSet(_) | FlatInRel::Equality(_) => continue,
                };
                let id = relations[&rel];
                for index in indices {
                    match index.age {
                        IndexAge::Old => continue,
                        IndexAge::New => {}
                    }
                    let order = index.order.iter().join(", ");
                    let own = display_own_index_field_name(flat, index, self.ctx);
                    writedoc! {f, "
                        let index = eqlog_runtime::__private::relation_data(source, eqlog_runtime::RelationId({id}))?
                            .reindex(&[{order}], &[{equalities}])?;
                        model.{own} = (&index).try_into()?;
                    "}?;
                    if self.ctx.has_shared_indices(flat) {
                        let all = display_all_index_field_name(flat, index, self.ctx);
                        writeln!(f, "model.{all} = model.{own}.clone();")?;
                    }
                }
            }
            for (id, rel) in iter_flat_rels(self.ctx.signature()).enumerate() {
                let arity = rel.arity(self.ctx.signature());
                if arity.is_empty() {
                    continue;
                }
                let len = arity.len();
                let weight = display_weight_static_name(rel, self.ctx);
                writedoc! {f, "
                    for row in eqlog_runtime::__private::relation_data(source, eqlog_runtime::RelationId({id}))?
                        .tuples().collect::<std::collections::BTreeSet<_>>()
                    {{
                        let row: [u32; {len}] = row.try_into().expect(\"matching signature arity\");
                "}?;
                let mut positions: BTreeMap<TypeId, Vec<usize>> = BTreeMap::new();
                for (i, &typ) in arity.iter().enumerate() {
                    positions.entry(typ).or_default().push(i);
                    let snake = self.ctx.type_name(typ).to_case(Case::Snake);
                    writedoc! {f, "
                        let weight = &mut model.{snake}_weights[row[{i}] as usize];
                        *weight = weight.saturating_add({weight});
                    "}?;
                }
                for (typ, positions) in positions {
                    let field = display_element_index_field_name(rel, typ, self.ctx);
                    let values = positions.iter().map(|i| format!("row[{i}]")).join(", ");
                    writedoc! {f, "
                        for element in [{values}].into_iter().collect::<std::collections::BTreeSet<_>>() {{
                            model.{field}.entry(element).or_default().push(row);
                    "}?;
                    let is_member = match rel {
                        FlatRel::ModelMember(member) => member == typ,
                        FlatRel::Pred(_) | FlatRel::Func(_) => false,
                    };
                    if is_member {
                        let camel = self.ctx.type_name(typ).to_case(Case::UpperCamel);
                        let snake = self.ctx.type_name(typ).to_case(Case::Snake);
                        // Imported membership may only be recorded under an alias.
                        writedoc! {f, "
                            let root = model.root_{snake}({camel}(element)).0;
                            if root != element {{
                                model.{field}.entry(root).or_default().push(row);
                            }}
                        "}?;
                    }
                    writeln!(f, "}}")?;
                }
                writeln!(f, "}}")?;
            }
            writedoc! {f, "
                    Ok(model)
                }}
            "}
        })
    }
}

pub(super) fn display_dynamic_impl<'a>(
    name: &'a str,
    ctx: &'a RustGenCtx<'a>,
    indices: &'a IndexSelection,
) -> impl Display + 'a {
    FmtFn(move |f| {
        let dynamic = DynamicContext {
            ctx,
            indices,
            types: ctx
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
            impl eqlog_runtime::CompiledModel for {name} {{
                {signature}
                {export}
                {import}
            }}
        "}
    })
}

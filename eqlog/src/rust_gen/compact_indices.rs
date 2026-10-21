use std::collections::BTreeSet;
use std::fmt::Display;

use convert_case::{Case, Casing};
use indoc::writedoc;
use itertools::Itertools;

use super::{
    display_all_index_field_name, display_own_index_field_name, display_rel, display_type, indices,
    RustGenCtx,
};
use crate::algebra::signature::TypeId;
use crate::flat_eqlog::{iter_flat_rels, FlatInRel, FlatRel, IndexSelection, IndexSpec};
use crate::fmt_util::FmtFn;
use crate::ram::NativeIndexPreparation;

pub(super) fn members(model: TypeId, ctx: &RustGenCtx<'_>) -> Vec<TypeId> {
    ctx.signature()
        .iter_types()
        .filter(|&typ| {
            ctx.supports_compact_members(typ)
                && ctx.signature().type_(typ).parents.as_slice() == [model]
        })
        .collect()
}

pub(super) fn supports_model(model: TypeId, ctx: &RustGenCtx<'_>) -> bool {
    ctx.signature().type_(model).parents.is_empty() && !members(model, ctx).is_empty()
}

pub(super) fn owner(rel: &FlatInRel, ctx: &RustGenCtx<'_>) -> Option<TypeId> {
    let rel = match rel {
        FlatInRel::Rel(rel) => *rel,
        FlatInRel::RelWithDiagonals { .. } | FlatInRel::TypeSet(_) | FlatInRel::Equality(_) => {
            return None;
        }
    };
    match rel {
        FlatRel::ModelMember(_) => None,
        FlatRel::Pred(_) | FlatRel::Func(_) => rel
            .parent_model_type(ctx.signature())
            .filter(|&model| supports_model(model, ctx)),
    }
}

pub(super) fn inherited_slot(
    rel: &FlatInRel,
    index: &IndexSpec,
    model: TypeId,
    ctx: &RustGenCtx<'_>,
    selection: &IndexSelection,
) -> Option<usize> {
    if owner(rel, ctx) != Some(model) || index.order.first() != Some(&0) {
        return None;
    }
    let relation = match rel {
        FlatInRel::Rel(rel) => *rel,
        FlatInRel::RelWithDiagonals { .. } | FlatInRel::TypeSet(_) | FlatInRel::Equality(_) => {
            return None;
        }
    };
    let mut order = index.order.to_vec();
    order.sort_unstable();
    if !order
        .iter()
        .copied()
        .eq(0..rel.arity(ctx.signature()).len())
    {
        return None;
    }
    let order = index.order[1..]
        .iter()
        .map(|&column| column - 1)
        .collect_vec();
    layouts(model, ctx, selection)
        .into_iter()
        .find(|layout| layout.rel == relation)?
        .slots
        .into_iter()
        .find_map(|(candidate, slot)| (candidate == order).then_some(slot))
}

struct RelationLayout {
    rel: FlatRel,
    relation: usize,
    member_types: Vec<Option<usize>>,
    slots: Vec<(Vec<usize>, usize)>,
}

impl RelationLayout {
    fn slot(&self, order: &[usize]) -> usize {
        self.slots
            .iter()
            .find_map(|(candidate, slot)| (candidate == order).then_some(*slot))
            .expect("selected compact permutation has a storage slot")
    }

    fn signature_slot(&self) -> usize {
        self.slot(&(0..self.member_types.len()).collect_vec())
    }
}

fn layouts(model: TypeId, ctx: &RustGenCtx<'_>, selection: &IndexSelection) -> Vec<RelationLayout> {
    let members = members(model, ctx);
    let mut next_slot = 0;
    iter_flat_rels(ctx.signature())
        .filter(|&rel| owner(&FlatInRel::Rel(rel), ctx) == Some(model))
        .enumerate()
        .map(|(relation, rel)| {
            let arity = rel.arity(ctx.signature());
            let member_types = arity[1..]
                .iter()
                .enumerate()
                .map(|(column, typ)| {
                    rel.column_maps_under(ctx.signature(), column + 1, model)
                        .then(|| members.iter().position(|member| member == typ))
                        .flatten()
                })
                .collect();
            let mut orders = BTreeSet::from([(0..arity.len() - 1).collect_vec()]);
            for index in &selection.indices[&FlatInRel::Rel(rel)] {
                assert_eq!(index.order.len(), arity.len());
                orders.insert(
                    index
                        .order
                        .iter()
                        .copied()
                        .filter(|&column| column != 0)
                        .map(|column| column - 1)
                        .collect(),
                );
            }
            let slots = orders
                .into_iter()
                .map(|order| {
                    let slot = next_slot;
                    next_slot += 1;
                    (order, slot)
                })
                .collect();
            RelationLayout {
                rel,
                relation,
                member_types,
                slots,
            }
        })
        .collect()
}

fn model_name(model: TypeId, ctx: &RustGenCtx<'_>) -> String {
    display_type(model, ctx).to_string().to_case(Case::Snake)
}

pub(super) fn fields<'a>(ctx: &'a RustGenCtx<'a>, initialize: bool) -> impl Display + 'a {
    FmtFn(move |f| {
        for (_, ids) in ctx.signature().iter_model_decls() {
            let model = ids.type_;
            if !supports_model(model, ctx) {
                continue;
            }
            let name = model_name(model, ctx);
            if initialize {
                writeln!(f, "__compact_indices_{name}: None,")?;
                writeln!(f, "__total_members_{name}: BTreeSet::new(),")?;
            } else {
                writeln!(f, "__compact_indices_{name}: Option<eqlog_runtime::__private::CompactOwnerIndices>,")?;
                writeln!(f, "__total_members_{name}: BTreeSet<u32>,")?;
            }
            for typ in members(model, ctx) {
                let name = model_name(typ, ctx);
                if initialize {
                    writeln!(f, "__compact_domain_{name}: PrefixTree2::new(),")?;
                } else {
                    writeln!(f, "__compact_domain_{name}: PrefixTree2,")?;
                }
            }
        }
        Ok(())
    })
}

fn publish_tree(field: &str, dim: usize) -> String {
    if dim == 0 {
        return format!(
            "if suffix.is_empty() {{ {field}.remove([owner]); }} else {{ {field}.insert([owner]); }}"
        );
    }
    // Rebuilding unchanged owner pivots would make global version publication
    // repeatedly compare all owners visited earlier in the same traversal.
    format!("if suffix.is_empty() {{ {field}.map.remove(&owner); }} else if !{field}.get(owner).is_some_and(|current| eqlog_runtime::__private::SnapshotSet::shares_root(current, &suffix)) {{ {field}.map.insert(owner, suffix); }}")
}

pub(super) fn insert_hook<'a>(rel: FlatRel, ctx: &'a RustGenCtx<'a>) -> impl Display + 'a {
    FmtFn(move |f| {
        if owner(&FlatInRel::Rel(rel), ctx).is_none() {
            return Ok(());
        }
        let name = display_rel(rel, ctx).to_case(Case::Snake);
        let args = (0..rel.arity(ctx.signature()).len())
            .map(|column| format!("el{column}"))
            .join(", ");
        writeln!(
            f,
            "if self.__compact_insert_{name}(retain_support, {args}).is_some() {{ return; }}"
        )
    })
}

pub(super) fn native_guard<'a>(rel: &'a FlatInRel, ctx: &'a RustGenCtx<'a>) -> impl Display + 'a {
    FmtFn(move |f| {
        if let Some(model) = owner(rel, ctx) {
            let name = model_name(model, ctx);
            writeln!(
                f,
                "if self.__compact_indices_{name}.is_some() {{ return; }}"
            )?;
        }
        Ok(())
    })
}

pub(super) fn graph_guard<'a>(model: TypeId, ctx: &'a RustGenCtx<'a>) -> impl Display + 'a {
    FmtFn(move |f| {
        if supports_model(model, ctx) {
            let name = model_name(model, ctx);
            writedoc! {f, "
                if self.__compact_indices_{name}.is_some() {{
                    let mut changed = false;
                    for component in components.iter() {{
                        assert!(component.internal.is_empty(), \"compact inheritance is acyclic\");
                        for morphism in &component.outgoing {{
                            changed |= self.__compact_transport_{name}(morphism.dom, morphism.cod).unwrap();
                        }}
                    }}
                    return changed;
                }}
            "}?;
        }
        Ok(())
    })
}

pub(super) fn component_guard<'a>(model: TypeId, ctx: &'a RustGenCtx<'a>) -> impl Display + 'a {
    FmtFn(move |f| {
        if supports_model(model, ctx) {
            let name = model_name(model, ctx);
            writedoc! {f, "
                if self.__compact_indices_{name}.is_some() {{
                    let mut changed = false;
                    for morphism in morphisms {{
                        changed |= self.__compact_transport_{name}(morphism.dom, morphism.cod).unwrap();
                    }}
                    return changed;
                }}
            "}?;
        }
        Ok(())
    })
}

pub(super) fn selected_guard<'a>(model: TypeId, ctx: &'a RustGenCtx<'a>) -> impl Display + 'a {
    FmtFn(move |f| {
        if supports_model(model, ctx) {
            let name = model_name(model, ctx);
            writedoc! {f, "
                if let Some(changed) = self.__compact_transport_{name}(*dom, *cod) {{
                    inserted.fill(changed);
                    return changed;
                }}
            "}?;
        }
        Ok(())
    })
}

pub(super) fn methods<'a>(
    ctx: &'a RustGenCtx<'a>,
    selection: &'a IndexSelection,
    native: &'a [NativeIndexPreparation],
) -> impl Display + 'a {
    FmtFn(move |f| {
        for (_, ids) in ctx.signature().iter_model_decls() {
            let model = ids.type_;
            if !supports_model(model, ctx) {
                continue;
            }
            let name = model_name(model, ctx);
            let members = members(model, ctx);
            let layouts = layouts(model, ctx, selection);
            let owner_leading = layouts.iter().all(|layout| {
                selection
                    .current_primary(&FlatInRel::Rel(layout.rel))
                    .order
                    .first()
                    == Some(&0)
            }) && native.iter().all(|plan| {
                owner(&plan.rel, ctx) != Some(model) || plan.index.order.first() == Some(&0)
            });
            let specs = layouts
                .iter()
                .flat_map(|layout| {
                    layout.slots.iter().map(move |(order, _)| {
                        let relation = layout.relation;
                        let order = order.iter().join(", ");
                        let columns = layout.member_types.iter().map(|typ| match typ {
                            Some(typ) => format!("Some({typ})"),
                            None => "None".to_owned(),
                        }).join(", ");
                        format!("eqlog_runtime::__private::CompactIndexSpec {{ relation: {relation}, order: vec![{order}], member_types: vec![{columns}] }}")
                    })
                })
                .join(",\n");
            let enable_members = members
                .iter()
                .map(|&typ| {
                    let member = model_name(typ, ctx);
                    format!("self.__enable_compact_{member}();")
                })
                .join("\n");
            let clear_aliases = members
                .iter()
                .map(|&typ| {
                    let member = model_name(typ, ctx);
                    format!("self.{member}_uprooted.clear();")
                })
                .join("\n");
            let ensure_members = members.iter().map(|&typ| {
                let member = model_name(typ, ctx);
                format!("let spaces = self.__compact_members_{member}.as_mut().expect(\"compact owner enables every member type\"); if !spaces.has_owner(owner) {{ spaces.create_owner(owner); }}")
            }).join("\n");
            writedoc! {f, "
                fn __enable_compact_{name}_indices(&mut self) {{
                    if self.__compact_indices_{name}.is_some() {{ return; }}
                    assert!({owner_leading}, \"compact scoped indexes require owner-leading permutations\");
                    self.__canonicalize_relations();
                    {enable_members}
                    let mut indices = eqlog_runtime::__private::CompactOwnerIndices::new(vec![{specs}]);
                    let owners: Vec<_> = self.iter_{name}().map(|owner| owner.0).collect();
                    for &owner in &owners {{ indices.create_owner(owner); }}
            "}?;
            for layout in &layouts {
                let rel = FlatInRel::Rel(layout.rel);
                let primary = selection.current_primary(&rel);
                let own = display_own_index_field_name(&rel, primary, ctx);
                let arity = layout.rel.arity(ctx.signature());
                let args = primary
                    .order
                    .iter()
                    .map(|column| format!("el{column}"))
                    .join(", ");
                let row = (1..arity.len()).map(|column| {
                    if let Some(typ) = layout.member_types[column - 1] {
                        let member = model_name(members[typ], ctx);
                        let camel = display_type(members[typ], ctx).to_string().to_case(Case::UpperCamel);
                        format!("self.__compact_{member}_origin(el0, self.root_{member}({camel}(el{column})))")
                    } else {
                        format!("el{column}")
                    }
                }).join(", ");
                let relation = layout.relation;
                writeln!(f, "for [{args}] in self.{own}.iter() {{ indices.record(el0, {relation}, &[{row}], true); }}")?;
            }
            writedoc! {f, "
                    self.__compact_indices_{name} = Some(indices);
                    {clear_aliases}
                    for owner in owners {{ self.__compact_publish_{name}(owner); }}
                    self.__closed = false;
                }}

                fn __compact_ensure_{name}_owner(&mut self, owner: u32) {{
                    let indices = self.__compact_indices_{name}.as_mut().expect(\"compact owner indices are enabled\");
                    if !indices.has_owner(owner) {{ indices.create_owner(owner); }}
                    {ensure_members}
                }}

                fn __compact_publish_{name}(&mut self, owner: u32) {{
                    let indices = self.__compact_indices_{name}.as_ref().unwrap();
            "}?;
            for layout in &layouts {
                let rel = FlatInRel::Rel(layout.rel);
                let primary = selection.current_primary(&rel);
                if primary.order.first() != Some(&0) {
                    continue;
                }
                let slot = layout.slot(
                    &primary.order[1..]
                        .iter()
                        .map(|column| column - 1)
                        .collect_vec(),
                );
                let dim = layout.member_types.len();
                let field = display_all_index_field_name(&rel, primary, ctx);
                let update = publish_tree(&format!("self.{field}"), dim);
                writedoc! {f, "
                    let suffix = PrefixTree{dim}::try_from(indices.rows(owner, {slot})).expect(\"compact index arity\");
                    {update}
                "}?;
                for (id, preparation) in native
                    .iter()
                    .enumerate()
                    .filter(|(_, plan)| plan.rel == rel)
                {
                    if preparation.index.order.first() != Some(&0) {
                        continue;
                    }
                    let slot = layout.slot(
                        &preparation.index.order[1..]
                            .iter()
                            .map(|column| column - 1)
                            .collect_vec(),
                    );
                    let update = publish_tree("index", dim);
                    writedoc! {f, "
                        let suffix = PrefixTree{dim}::try_from(indices.rows(owner, {slot})).expect(\"compact index arity\");
                        let mut index = self.__native_input_{id}.current().clone();
                        {update}
                        self.__native_input_{id}.publish(&index);
                    "}?;
                }
            }
            for &typ in &members {
                let member = model_name(typ, ctx);
                let update = publish_tree(&format!("self.__compact_domain_{member}"), 1);
                writedoc! {f, "
                    let suffix = PrefixTree1 {{ set: self.__compact_members_{member}.as_ref().unwrap()
                        .get_snapshot(owner).unwrap().canonical_domain().clone() }};
                    {update}
                "}?;
            }
            writeln!(f, "}}")?;
            for layout in &layouts {
                let relation = layout.relation;
                let rel_name = display_rel(layout.rel, ctx).to_case(Case::Snake);
                let arity = layout.rel.arity(ctx.signature());
                let args = arity
                    .iter()
                    .enumerate()
                    .map(|(column, &typ)| {
                        let camel = display_type(typ, ctx).to_string().to_case(Case::UpperCamel);
                        format!("el{column}: {camel}")
                    })
                    .join(", ");
                let row = (1..arity.len()).map(|column| {
                    if let Some(typ) = layout.member_types[column - 1] {
                        let member = model_name(members[typ], ctx);
                        format!("self.__compact_{member}_origin(owner, self.root_{member}(el{column}))")
                    } else {
                        format!("el{column}.0")
                    }
                }).join(", ");
                let signature_slot = layout.signature_slot();
                let invalidate = indices::invalidate(layout.rel, selection, ctx);
                writedoc! {f, "
                    fn __compact_primary_{rel_name}(&self, owner: u32) -> Option<&eqlog_runtime::__private::Table> {{
                        let indices = self.__compact_indices_{name}.as_ref()?;
                        indices.has_owner(owner).then(|| indices.rows(owner, {signature_slot}))
                    }}

                    fn __compact_insert_{rel_name}(&mut self, retain_support: bool, {args}) -> Option<bool> {{
                        self.__compact_indices_{name}.as_ref()?;
                        let owner = el0.0;
                        self.__compact_ensure_{name}_owner(owner);
                        let row = [{row}];
                        let result = self.__compact_indices_{name}.as_mut().unwrap().record(owner, {relation}, &row, retain_support);
                        if result.inserted || result.retained_support {{ self.__closed = false; }}
                        if result.inserted {{
                            self.__compact_publish_{name}(owner);
                            {invalidate}
                        }}
                        Some(result.inserted)
                    }}
                "}?;
            }
            for (member_type, &typ) in members.iter().enumerate() {
                let member = model_name(typ, ctx);
                writedoc! {f, "
                    fn __compact_allocated_{member}(&mut self, owner: u32, _origin: u32) {{
                        self.__compact_ensure_{name}_owner(owner);
                        self.__compact_publish_{name}(owner);
                    }}

                    fn __compact_equate_{member}(&mut self, owner: u32, merge: eqlog_runtime::__private::MemberMerge) {{
                        self.__compact_indices_{name}.as_mut().unwrap().rewrite(owner, {member_type}, merge.loser, merge.winner);
                        self.__compact_publish_{name}(owner);
                    }}
                "}?;
            }
            let refresh_members = members.iter().enumerate().map(|(member_type, &typ)| {
                let member = model_name(typ, ctx);
                format!("let spaces = self.__compact_members_{member}.as_mut().unwrap(); assert_eq!(spaces.source(target), Some(source), \"compact transport requires declared total inheritance\"); force |= spaces.refresh_with_merges(target).is_some(); let source_{member_type} = spaces.snapshot(source); merges.extend(spaces.local_merges(target).iter().map(|merge| ({member_type}, merge.loser, merge.winner))); self.__sync_compact_{member}_weights();")
            }).join("\n");
            let normalize = members.iter().enumerate().map(|(member_type, _)| {
                format!("{member_type} => source_{member_type}.root_origin(origin).unwrap_or(origin),")
            }).join("\n");
            let inherit = members.iter().map(|&typ| {
                let member = model_name(typ, ctx);
                format!("force |= self.__compact_members_{member}.as_mut().unwrap().inherit_total_members_with_merges(source, target).is_some(); self.__sync_compact_{member}_weights();")
            }).join("\n");
            writedoc! {f, "
                fn __compact_refresh_{name}_impl(&mut self, source: u32, target: u32, mut force: bool) -> bool {{
                    self.__compact_ensure_{name}_owner(source);
                    self.__compact_ensure_{name}_owner(target);
                    let mut merges = Vec::new();
                    {refresh_members}
                    let result = self.__compact_indices_{name}.as_mut().unwrap().rebase(target, source, force,
                        |member_type, origin| match member_type {{ {normalize} _ => unreachable!(\"unknown compact member partition\") }}, &merges);
                    if result.refreshed || force {{ self.__compact_publish_{name}(target); }}
                    result.refreshed || force
                }}

                fn __compact_inherit_{name}(&mut self, source: u32, target: u32) -> bool {{
                    self.__compact_ensure_{name}_owner(source);
                    self.__compact_ensure_{name}_owner(target);
                    let mut force = false;
                    {inherit}
                    self.__compact_refresh_{name}_impl(source, target, force)
                }}

                fn __compact_transport_{name}(&mut self, source: u32, target: u32) -> Option<bool> {{
                    self.__compact_indices_{name}.as_ref()?;
                    Some(self.__compact_refresh_{name}_impl(source, target, false))
                }}
            "}?;
        }
        Ok(())
    })
}

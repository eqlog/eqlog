use std::fmt::Display;

use indoc::writedoc;
use itertools::Itertools;

use super::indices::projection;
use super::{
    display_index_type, display_mor_app_map_expr, display_morphism_components,
    display_morphism_index_prefix_walk, display_own_index_field_name, morphism_index_column_kind,
    parent_prefix_len, MorphismIndexColumnKind, RustGenCtx,
};
use crate::algebra::signature::TypeId;
use crate::flat_eqlog::{FlatInRel, IndexSelection, IndexSpec};
use crate::fmt_util::FmtFn;
use crate::ram::NativeIndexPreparation;

pub(super) fn find(
    plans: &[NativeIndexPreparation],
    rel: &FlatInRel,
    index: &IndexSpec,
) -> Option<usize> {
    plans
        .iter()
        .position(|plan| plan.rel == *rel && plan.index.order == index.order)
}

pub(super) fn fields<'a>(
    plans: &'a [NativeIndexPreparation],
    ctx: &'a RustGenCtx<'a>,
) -> impl Display + 'a {
    FmtFn(move |f| {
        for (id, plan) in plans.iter().enumerate() {
            let typ = display_index_type(&plan.rel, ctx);
            writedoc! {f, "
                __native_seed_{id}: eqlog_runtime::__private::IndexSeed<{typ}, {typ}>,
                __native_input_{id}: eqlog_runtime::__private::RelationVersions<{typ}>,
            "}?;
        }
        Ok(())
    })
}

pub(super) fn init(plans: &[NativeIndexPreparation]) -> impl Display + '_ {
    FmtFn(move |f| {
        for id in 0..plans.len() {
            writedoc! {f, "
                __native_seed_{id}: eqlog_runtime::__private::IndexSeed::new(),
                __native_input_{id}: eqlog_runtime::__private::RelationVersions::new(),
            "}?;
        }
        Ok(())
    })
}

pub(super) fn methods<'a>(
    plans: &'a [NativeIndexPreparation],
    indices: &'a IndexSelection,
    ctx: &'a RustGenCtx<'a>,
) -> impl Display + 'a {
    FmtFn(move |f| {
        for (id, plan) in plans.iter().enumerate() {
            let typ = display_index_type(&plan.rel, ctx);
            let primary = indices.current_primary(&plan.rel);
            let owned = display_own_index_field_name(&plan.rel, primary, ctx);
            let project = projection(&plan.rel, &plan.index, primary);
            writedoc! {f, "
                fn __prepare_native_index_{id}(&mut self) {{
                    let mut index = self.__native_seed_{id}.update(&self.{owned}, {project});
                    self.__native_{id}_model_0([], &mut index, false);
                    self.__native_input_{id}.publish(&index);
                }}

                fn __extend_native_index_{id}(&mut self) {{
                    let index = self.__native_seed_{id}.update(&self.{owned}, {project});
                    let index = self.__native_input_{id}.current().union(&index);
                    self.__native_input_{id}.publish(&index);
                }}
            "}?;
            for (level, &model) in plan.models.iter().enumerate() {
                let model_id = level;
                let parent_len = ctx.signature().type_(model).parents.len();
                let components = display_morphism_components(model, ctx, indices, true);
                let children = if level + 1 < plan.models.len() {
                    let child_id = level + 1;
                    let parents = (0..parent_len)
                        .map(|i| format!("parents[{i}]"))
                        .chain(std::iter::once("object".to_string()))
                        .join(", ");
                    format!("component_changed |= self.__native_{id}_model_{child_id}([{parents}], index, track_component);")
                } else {
                    String::new()
                };
                let remap = remap(id, plan, model, level, indices, ctx);
                writedoc! {f, "
                    #[allow(unused_variables)]
                    fn __native_{id}_model_{model_id}(
                        &self, parents: [u32; {parent_len}], index: &mut {typ}, track_changes: bool,
                    ) -> bool {{
                        {components}
                        let mut changed = false;
                        for component in components {{
                            let cyclic = !component.internal.is_empty();
                            let track_component = track_changes || cyclic;
                            loop {{
                                let mut component_changed = false;
                                for &object in &component.objects {{ {children} }}
                                for morphism in &component.internal {{
                                    component_changed |= self.__native_{id}_morphism_{model_id}(
                                        parents, morphism, index, track_component,
                                    );
                                }}
                                changed |= component_changed;
                                if !cyclic || !component_changed {{ break; }}
                            }}
                            for morphism in &component.outgoing {{
                                changed |= self.__native_{id}_morphism_{model_id}(
                                    parents, morphism, index, track_changes,
                                );
                            }}
                        }}
                        changed
                    }}
                    {remap}
                "}?;
            }
        }
        Ok(())
    })
}

fn remap<'a>(
    id: usize,
    plan: &'a NativeIndexPreparation,
    model: TypeId,
    model_id: usize,
    indices: &'a IndexSelection,
    ctx: &'a RustGenCtx<'a>,
) -> impl Display + 'a {
    FmtFn(move |f| {
        let parent_len = ctx.signature().type_(model).parents.len();
        let arity = plan.rel.arity(ctx.signature());
        let parent_cols = parent_prefix_len(&plan.rel, ctx);
        let columns: Vec<_> = plan
            .index
            .order
            .iter()
            .map(|&column| {
                morphism_index_column_kind(model, column, parent_cols, arity[column], ctx)
            })
            .collect();
        let prefix_len = columns
            .iter()
            .rposition(|column| column.needs_mapping())
            .unwrap()
            + 1;
        let suffix_len = arity.len() - prefix_len;
        let typ = display_index_type(&plan.rel, ctx);
        let maps = columns[..prefix_len]
            .iter()
            .enumerate()
            .filter_map(|(i, column)| match column {
                MorphismIndexColumnKind::Member(member) => {
                    let expr = display_mor_app_map_expr(model, *member, ctx, indices, true);
                    Some(format!("let map_el{i} = {expr};"))
                }
                MorphismIndexColumnKind::OuterParent(_)
                | MorphismIndexColumnKind::Parent
                | MorphismIndexColumnKind::Copy => None,
            })
            .join("\n");
        let collect = display_morphism_index_prefix_walk(
            &columns[..prefix_len],
            arity.len(),
            "source".to_string(),
            false,
        );
        let prefix = (0..prefix_len).map(|i| format!("el{i}")).join(", ");
        let wrap = (1..prefix_len).rev().map(|i| {
            let dim = arity.len() - i;
            format!("let mapped = {{ let mut tree = PrefixTree{dim}::new(); tree.insert_restriction(el{i}, mapped); tree }};")
        }).join("\n");
        writedoc! {f, "
            #[allow(unused_variables)]
            fn __native_{id}_morphism_{model_id}(
                &self, parents: [u32; {parent_len}],
                MorphismWithSignature {{ morph, dom, cod }}: &MorphismWithSignature,
                index: &mut {typ}, track_changes: bool,
            ) -> bool {{
                {maps}
                let source = index.clone();
                let mut propagated: Vec<([u32; {prefix_len}], PrefixTree{suffix_len})> = Vec::new();
                {collect}
                let mut changed = false;
                for ([{prefix}], mapped) in propagated {{
                    {wrap}
                    if index.get(el0).is_some_and(|existing| mapped.is_subset(existing)) {{
                        continue;
                    }}
                    changed |= track_changes && !mapped.is_empty();
                    index.insert_restriction(el0, mapped);
                }}
                changed
            }}
        "}
    })
}

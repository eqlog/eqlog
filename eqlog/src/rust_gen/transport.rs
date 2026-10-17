use super::*;

pub(super) fn field(rel: &FlatInRel, model: TypeId, ctx: &RustGenCtx<'_>) -> String {
    let name = match rel {
        FlatInRel::Rel(rel) => display_rel(*rel, ctx).to_case(Snake),
        FlatInRel::RelWithDiagonals { .. } | FlatInRel::TypeSet(_) | FlatInRel::Equality(_) => {
            unreachable!("transport checkpoints belong to primary relations")
        }
    };
    let model = display_type(model, ctx).to_string().to_case(Snake);
    format!("__transport_{model}_{name}")
}

fn is_leaf(model: TypeId, ctx: &RustGenCtx<'_>) -> bool {
    !ctx.signature()
        .iter_model_decls()
        .any(|(_, ids)| ctx.signature().type_(ids.type_).parents.last() == Some(&model))
}

fn member_maps(
    rel: &FlatInRel,
    index: &IndexSpec,
    model: TypeId,
    ctx: &RustGenCtx<'_>,
) -> Vec<TypeId> {
    let arity = rel.arity(ctx.signature());
    index
        .order
        .iter()
        .filter_map(|&column| {
            match morphism_index_column_kind(
                rel,
                model,
                column,
                parent_prefix_len(rel, ctx),
                arity[column],
                ctx,
            ) {
                MorphismIndexColumnKind::Member(member) => Some(member),
                MorphismIndexColumnKind::Parent
                | MorphismIndexColumnKind::OuterParent(_)
                | MorphismIndexColumnKind::Copy => None,
            }
        })
        .collect()
}

fn checkpoint_indices<'a>(
    ctx: &'a RustGenCtx<'a>,
    selection: &'a IndexSelection,
    model: TypeId,
) -> Vec<(&'a FlatInRel, &'a IndexSpec)> {
    let parent_len = ctx.signature().type_(model).parents.len();
    let mut result = Vec::new();
    for (rel, index) in selection.current_indices() {
        if !ctx.has_shared_indices(rel) || !selection.is_primary(rel, index) {
            continue;
        }
        if !index
            .order
            .iter()
            .take(parent_len + 1)
            .copied()
            .eq(0..parent_len + 1)
        {
            continue;
        }
        let relation = match rel {
            FlatInRel::Rel(rel) => *rel,
            FlatInRel::RelWithDiagonals { .. } | FlatInRel::TypeSet(_) | FlatInRel::Equality(_) => {
                continue
            }
        };
        let Some(owner) = relation.parent_model_type(ctx.signature()) else {
            continue;
        };
        if owner != model && !ctx.signature().type_(owner).parents.contains(&model) {
            continue;
        }
        result.push((rel, index));
    }
    result
}

pub(super) fn fields<'a>(
    ctx: &'a RustGenCtx<'a>,
    selection: &'a IndexSelection,
    initialize: bool,
) -> impl Display + 'a {
    FmtFn(move |f| {
        for (_, ids) in ctx.signature().iter_model_decls() {
            let model = ids.type_;
            let parent_len = ctx.signature().type_(model).parents.len();
            let name = display_type(model, ctx).to_string().to_case(Snake);
            if ctx.model_mode() == ModelMode::Native {
                if initialize {
                    writeln!(f, "__morphism_graph_{name}: eqlog_runtime::__private::MorphismGraphCache::new(),")?;
                } else {
                    writeln!(f, "__morphism_graph_{name}: eqlog_runtime::__private::MorphismGraphCache<{parent_len}>,")?;
                }
            }
            for (rel, index) in checkpoint_indices(ctx, selection, model) {
                let name = field(rel, model, ctx);
                if initialize {
                    writeln!(f, "{name}: BTreeMap::new(),")?;
                    if is_leaf(model, ctx) {
                        writeln!(f, "{name}_frontier: BTreeMap::new(),")?;
                    }
                    continue;
                }
                let arity = rel.arity(ctx.signature());
                let map_count = member_maps(rel, index, model, ctx).len();
                let dim = arity.len() - parent_len - 1;
                let key_len = parent_len + 3;
                writeln!(f, "{name}: BTreeMap<[u32; {key_len}], eqlog_runtime::__private::TransportCheckpoint<PrefixTree{dim}, {map_count}>>,")?;
                if is_leaf(model, ctx) {
                    let dim = dim + 1;
                    writeln!(f, "{name}_frontier: BTreeMap<[u32; {parent_len}], eqlog_runtime::__private::TransportFrontier<PrefixTree{dim}, {map_count}>>,")?;
                }
            }
        }
        Ok(())
    })
}

pub(super) fn prepare_frontier<'a>(
    model: TypeId,
    relations: &'a [&'a FlatInRel],
    plan: Option<&'a PropagationPlan>,
    ctx: &'a RustGenCtx<'a>,
    selection: &'a IndexSelection,
) -> impl Display + 'a {
    FmtFn(move |f| {
        let relation_count = relations.len();
        writeln!(f, "let mut transport_work: [eqlog_runtime::__private::TransportWork; {relation_count}] = std::array::from_fn(|_| eqlog_runtime::__private::TransportWork::default());")?;
        let checkpoints = checkpoint_indices(ctx, selection, model);
        if !is_leaf(model, ctx)
            || relations
                .iter()
                .any(|rel| !checkpoints.iter().any(|(candidate, _)| candidate == rel))
        {
            return writeln!(f, "let transport_all = true;");
        }
        if let Some(plan) = plan {
            let maps: BTreeSet<_> = relations
                .iter()
                .flat_map(|rel| plan.map_indices.get(&(model, (*rel).clone())))
                .flatten()
                .collect();
            for (rel, index) in maps {
                write!(f, "{}", indices::prepare(rel, index, selection, ctx))?;
            }
        }
        writeln!(f, "let transport_all = false;")?;
        let parent_len = ctx.signature().type_(model).parents.len();
        for (relation_index, &rel) in relations.iter().enumerate() {
            let index = selection.current_primary(rel);
            let field = field(rel, model, ctx);
            let source = display_all_index_field_name(rel, index, ctx).to_string();
            let source = if parent_len == 0 {
                format!("self.{source}().clone()")
            } else {
                let dim = rel.arity(ctx.signature()).len() - parent_len;
                format!(
                    "{}.clone()",
                    display_tree_prefix_slice(&source, parent_len, dim)
                )
            };
            let maps = member_maps(rel, index, model, ctx)
                .into_iter()
                .map(|member| {
                    let morphism_type = ctx.signature().ids_for_model_type(model).unwrap().mor;
                    let app = ctx
                        .signature()
                        .mor_app_func(MorphismMemberTypes {
                            morphism_type,
                            member_type: member,
                        })
                        .unwrap();
                    let app_rel = FlatInRel::Rel(FlatRel::Func(app));
                    let order: Vec<_> = (0..parent_len + 3).collect();
                    let app_index = index_with_order(&selection.indices[&app_rel], &order);
                    let name =
                        indices::read_method(&app_rel, app_index, selection, ctx, plan.is_some());
                    if parent_len == 0 {
                        format!("self.{name}().clone()")
                    } else {
                        format!(
                            "{}.clone()",
                            display_tree_prefix_slice(&name, parent_len, 3)
                        )
                    }
                })
                .join(", ");
            writedoc! {f, "
                let source = {source};
                let maps = [{maps}];
                self.{field}_frontier.entry(parents)
                    .or_insert_with(eqlog_runtime::__private::TransportFrontier::new)
                    .prepare(&source, &maps, &components, retain_own, &mut transport_work[{relation_index}]);
            "}?;
        }
        Ok(())
    })
}

pub(super) fn finish_frontier<'a>(
    model: TypeId,
    relations: &'a [&'a FlatInRel],
    ctx: &'a RustGenCtx<'a>,
    selection: &'a IndexSelection,
) -> impl Display + 'a {
    FmtFn(move |f| {
        let checkpoints = checkpoint_indices(ctx, selection, model);
        if !is_leaf(model, ctx)
            || relations
                .iter()
                .any(|rel| !checkpoints.iter().any(|(candidate, _)| candidate == rel))
        {
            return Ok(());
        }
        let parent_len = ctx.signature().type_(model).parents.len();
        for &rel in relations {
            let index = selection.current_primary(rel);
            let field = field(rel, model, ctx);
            let source = display_all_index_field_name(rel, index, ctx).to_string();
            let source = if parent_len == 0 {
                format!("self.{source}().clone()")
            } else {
                let dim = rel.arity(ctx.signature()).len() - parent_len;
                format!(
                    "{}.clone()",
                    display_tree_prefix_slice(&source, parent_len, dim)
                )
            };
            writedoc! {f, "
                let source = {source};
                self.{field}_frontier.get_mut(&parents).unwrap().finish(&source);
            "}?;
        }
        Ok(())
    })
}

pub(super) fn prune<'a>(
    ctx: &'a RustGenCtx<'a>,
    selection: &'a IndexSelection,
) -> impl Display + 'a {
    FmtFn(move |f| {
        if ctx.model_mode() != ModelMode::Native {
            return Ok(());
        }
        for (_, ids) in ctx.signature().iter_model_decls() {
            let model = ids.type_;
            let parents = &ctx.signature().type_(model).parents;
            let name = display_type(model, ctx).to_string().to_case(Snake);
            let checkpoints = checkpoint_indices(ctx, selection, model);
            if checkpoints.is_empty() && parents.is_empty() {
                continue;
            }
            let key_types: Vec<_> = parents
                .iter()
                .copied()
                .chain(
                    checkpoints
                        .first()
                        .into_iter()
                        .flat_map(|_| [ids.mor, model, model]),
                )
                .collect();
            let changed = key_types
                .iter()
                .map(|&typ| {
                    let name = display_type(typ, ctx).to_string().to_case(Snake);
                    format!("!self.{name}_uprooted.is_empty()")
                })
                .unique()
                .join(" || ");
            let roots = key_types
                .iter()
                .enumerate()
                .map(|(i, &typ)| {
                    let name = display_type(typ, ctx).to_string().to_case(Snake);
                    format!("let root_{i} = &self.{name}_equalities;")
                })
                .join("\n");
            let canonical = (0..key_types.len())
                .map(|i| format!("root_{i}.root_const(key[{i}].into()).0 == key[{i}]"))
                .join(" && ");
            writeln!(f, "if {changed} {{ {roots}")?;
            if !parents.is_empty() {
                let canonical = (0..parents.len())
                    .map(|i| format!("root_{i}.root_const(key[{i}].into()).0 == key[{i}]"))
                    .join(" && ");
                writeln!(
                    f,
                    "self.__morphism_graph_{name}.retain_owners(|key| {canonical});"
                )?;
            }
            for (rel, _) in checkpoints {
                let checkpoint = field(rel, model, ctx);
                writeln!(f, "self.{checkpoint}.retain(|key, _| {canonical});")?;
                if is_leaf(model, ctx) && !parents.is_empty() {
                    let canonical = (0..parents.len())
                        .map(|i| format!("root_{i}.root_const(key[{i}].into()).0 == key[{i}]"))
                        .join(" && ");
                    writeln!(
                        f,
                        "self.{checkpoint}_frontier.retain(|key, _| {canonical});"
                    )?;
                }
            }
            writeln!(f, "}}")?;
        }
        Ok(())
    })
}

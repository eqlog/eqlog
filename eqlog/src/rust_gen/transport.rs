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

pub(super) fn fields<'a>(
    ctx: &'a RustGenCtx<'a>,
    _selection: &'a IndexSelection,
    initialize: bool,
) -> impl Display + 'a {
    FmtFn(move |f| {
        for &model in &ctx.transport().model_order {
            let plan = &ctx.transport().models[&model];
            let parent_len = plan.parents.len();
            let name = display_type(model, ctx).to_string().to_case(Snake);
            if ctx.model_mode() == ModelMode::Native {
                if initialize {
                    writeln!(f, "__morphism_graph_{name}: eqlog_runtime::__private::MorphismGraphCache::new(),")?;
                } else {
                    writeln!(f, "__morphism_graph_{name}: eqlog_runtime::__private::MorphismGraphCache<{parent_len}>,")?;
                }
            }
            for checkpoint in &plan.checkpoints {
                let rel = &checkpoint.rel;
                let name = field(rel, model, ctx);
                if initialize {
                    writeln!(f, "{name}: BTreeMap::new(),")?;
                    if plan.frontier {
                        writeln!(f, "{name}_frontier: BTreeMap::new(),")?;
                    }
                    continue;
                }
                let map_count = checkpoint.maps.len();
                let dim = checkpoint.suffix;
                let key_len = parent_len + 3;
                writeln!(f, "{name}: BTreeMap<[u32; {key_len}], eqlog_runtime::__private::TransportCheckpoint<PrefixTree{dim}, {map_count}>>,")?;
                if plan.frontier {
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
    prepare_frontier_impl(model, relations, plan, ctx, selection, false)
}

pub(super) fn stage_frontier<'a>(
    model: TypeId,
    relations: &'a [&'a FlatInRel],
    plan: &'a PropagationPlan,
    ctx: &'a RustGenCtx<'a>,
    selection: &'a IndexSelection,
) -> impl Display + 'a {
    prepare_frontier_impl(model, relations, Some(plan), ctx, selection, true)
}

fn prepare_frontier_impl<'a>(
    model: TypeId,
    relations: &'a [&'a FlatInRel],
    plan: Option<&'a PropagationPlan>,
    ctx: &'a RustGenCtx<'a>,
    selection: &'a IndexSelection,
    staged: bool,
) -> impl Display + 'a {
    FmtFn(move |f| {
        let relation_count = relations.len();
        writeln!(f, "let mut transport_work: [eqlog_runtime::__private::TransportWork; {relation_count}] = std::array::from_fn(|_| eqlog_runtime::__private::TransportWork::default());")?;
        let propagation = &ctx.transport().group(plan).models[&model];
        let Some(frontier) = &propagation.frontier else {
            assert!(!staged, "staged frontiers require checkpointed leaf models");
            return writeln!(f, "let transport_all = true;");
        };
        for (rel, index) in &frontier.prepare_maps {
            write!(f, "{}", indices::prepare(rel, index, selection, ctx))?;
        }
        if !staged {
            writeln!(f, "let transport_all = false;")?;
        }
        let parent_len = ctx.transport().models[&model].parents.len();
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
            let remap = ctx.transport().index(rel, index, model);
            let maps = remap
                .maps
                .iter()
                .map(|(_, read)| {
                    let name = indices::read_method(
                        &read.rel,
                        &read.index,
                        selection,
                        ctx,
                        plan.is_some(),
                    );
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
            let frontier = if staged {
                writeln!(f, "let mut frontier_{relation_index} = self.{field}_frontier.get(&parents).cloned().unwrap_or_else(eqlog_runtime::__private::TransportFrontier::new);")?;
                format!("frontier_{relation_index}")
            } else {
                format!("self.{field}_frontier.entry(parents).or_insert_with(eqlog_runtime::__private::TransportFrontier::new)")
            };
            writedoc! {f, "
                let source = {source};
                let maps = [{maps}];
                {frontier}.prepare(&source, &maps, &components, retain_own, &mut transport_work[{relation_index}]);
            "}?;
        }
        Ok(())
    })
}

pub(super) fn finish_frontier<'a>(
    model: TypeId,
    relations: &'a [&'a FlatInRel],
    plan: Option<&'a PropagationPlan>,
    ctx: &'a RustGenCtx<'a>,
    selection: &'a IndexSelection,
) -> impl Display + 'a {
    FmtFn(move |f| {
        if ctx.transport().group(plan).models[&model]
            .frontier
            .is_none()
        {
            return Ok(());
        }
        let parent_len = ctx.transport().models[&model].parents.len();
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
    _selection: &'a IndexSelection,
) -> impl Display + 'a {
    FmtFn(move |f| {
        if ctx.model_mode() != ModelMode::Native {
            return Ok(());
        }
        for &model in &ctx.transport().model_order {
            let plan = &ctx.transport().models[&model];
            let parents = &plan.parents;
            let name = display_type(model, ctx).to_string().to_case(Snake);
            let checkpoints = &plan.checkpoints;
            if checkpoints.is_empty() && parents.is_empty() {
                continue;
            }
            let key_types = &plan.key_types;
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
            let suffix_unchanged = key_types
                .iter()
                .skip(1)
                .map(|&typ| {
                    let name = display_type(typ, ctx).to_string().to_case(Snake);
                    format!("self.{name}_uprooted.is_empty()")
                })
                .unique()
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
            for checkpoint in checkpoints {
                let checkpoint = field(&checkpoint.rel, model, ctx);
                let first = display_type(key_types[0], ctx).to_string().to_case(Snake);
                let key_len = key_types.len();
                writedoc! {f, "
                    if {suffix_unchanged} {{
                        for alias in &self.{first}_uprooted {{
                            let mut lower = [0; {key_len}];
                            let mut upper = [u32::MAX; {key_len}];
                            lower[0] = alias.0;
                            upper[0] = alias.0;
                            let keys: Vec<_> = self.{checkpoint}.range(lower..=upper)
                                .map(|(key, _)| *key).collect();
                            for key in keys {{ self.{checkpoint}.remove(&key); }}
                        }}
                    }} else {{
                        self.{checkpoint}.retain(|key, _| {canonical});
                    }}
                "}?;
                if plan.frontier && !parents.is_empty() {
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

pub(super) enum DriverKind<'a> {
    Propagation {
        suffix: &'a str,
        plan: Option<&'a PropagationPlan>,
    },
    Native {
        id: usize,
        level: usize,
    },
}

pub(super) struct Driver<'a> {
    pub model: TypeId,
    pub kind: DriverKind<'a>,
}

fn changed_name(changes: TransportChanges) -> &'static str {
    match changes {
        TransportChanges::All => "changed",
        TransportChanges::Component => "component_changed",
    }
}

fn retention_name(retain: TransportRetention, driver: &Driver<'_>) -> &'static str {
    match (&driver.kind, retain) {
        (DriverKind::Propagation { .. }, TransportRetention::Outer) => "retain_own",
        (DriverKind::Propagation { .. }, TransportRetention::Component) => "retain_component_own",
        (DriverKind::Native { .. }, TransportRetention::Outer) => "track_changes",
        (DriverKind::Native { .. }, TransportRetention::Component) => "track_component",
    }
}

pub(super) fn display_driver<'a>(
    body: &'a [TransportInstruction],
    driver: &'a Driver<'a>,
    ctx: &'a RustGenCtx<'a>,
    selection: &'a IndexSelection,
) -> impl Display + 'a {
    FmtFn(move |f| {
        for instruction in body {
            match instruction {
                TransportInstruction::PrepareGraph => match &driver.kind {
                    DriverKind::Propagation { plan, .. } => {
                        let group = &ctx.transport().group(*plan).models[&driver.model];
                        for (rel, index) in &group.graph_indices {
                            write!(f, "{}", indices::prepare(rel, index, selection, ctx))?;
                        }
                    }
                    DriverKind::Native { .. } => {
                        unreachable!("native inputs prepare graph indices before traversal")
                    }
                },
                TransportInstruction::ComputeComponents => {
                    let prepared = match &driver.kind {
                        DriverKind::Propagation { plan, .. } => plan.is_some(),
                        DriverKind::Native { .. } => true,
                    };
                    write!(
                        f,
                        "{}",
                        display_morphism_components(driver.model, ctx, selection, prepared)
                    )?;
                }
                TransportInstruction::CompactBlock(body) => {
                    write!(
                        f,
                        "{}",
                        compact_indices::transport_body(body, driver.model, ctx)
                    )?;
                }
                TransportInstruction::PrepareFrontier | TransportInstruction::FinishFrontier => {
                    let plan = match &driver.kind {
                        DriverKind::Propagation { plan, .. } => *plan,
                        DriverKind::Native { .. } => {
                            unreachable!("secondary index traversal does not retain frontiers")
                        }
                    };
                    let relations = ctx.transport().group(plan).models[&driver.model]
                        .relations
                        .iter()
                        .collect_vec();
                    match instruction {
                        TransportInstruction::PrepareFrontier => write!(
                            f,
                            "{}",
                            prepare_frontier(driver.model, &relations, plan, ctx, selection)
                        )?,
                        TransportInstruction::FinishFrontier => write!(
                            f,
                            "{}",
                            finish_frontier(driver.model, &relations, plan, ctx, selection)
                        )?,
                        TransportInstruction::PrepareGraph
                        | TransportInstruction::ComputeComponents
                        | TransportInstruction::CompactBlock(_)
                        | TransportInstruction::ReturnUnlessWork
                        | TransportInstruction::InitializeChanges(_)
                        | TransportInstruction::ForEach { .. }
                        | TransportInstruction::Loop(_)
                        | TransportInstruction::RetainComponent
                        | TransportInstruction::CallChild { .. }
                        | TransportInstruction::SelectRelations
                        | TransportInstruction::ContinueUnlessActive
                        | TransportInstruction::InitializeInserted
                        | TransportInstruction::CallMorphism { .. }
                        | TransportInstruction::MarkWorkChanged
                        | TransportInstruction::AccumulateChanges
                        | TransportInstruction::BreakUnlessCyclicChanged
                        | TransportInstruction::ReturnChanged => {
                            unreachable!("frontier instruction was selected")
                        }
                    }
                }
                TransportInstruction::ReturnUnlessWork => writedoc! {f, "
                    if !transport_all && transport_work.iter().all(|work| work.is_empty()) {{
                        return false;
                    }}
                "}?,
                TransportInstruction::InitializeChanges(changes) => {
                    let name = changed_name(*changes);
                    writeln!(f, "let mut {name} = false;")?;
                }
                TransportInstruction::ForEach { iteration, body } => {
                    let head = match iteration {
                        TransportIteration::Components => "component in components.iter()",
                        TransportIteration::Objects => "&object in &component.objects",
                        TransportIteration::Internal => "morphism in &component.internal",
                        TransportIteration::Outgoing => "morphism in &component.outgoing",
                    };
                    let body = display_driver(body, driver, ctx, selection);
                    writeln!(f, "for {head} {{ {body} }}")?;
                }
                TransportInstruction::Loop(body) => {
                    let body = display_driver(body, driver, ctx, selection);
                    writeln!(f, "loop {{ {body} }}")?;
                }
                TransportInstruction::RetainComponent => {
                    let outer = retention_name(TransportRetention::Outer, driver);
                    let component = retention_name(TransportRetention::Component, driver);
                    writedoc! {f, "
                        let cyclic = !component.internal.is_empty();
                        let {component} = {outer} || cyclic;
                    "}?;
                }
                TransportInstruction::CallChild { model } => {
                    let parents = (0..ctx.transport().models[&driver.model].parents.len())
                        .map(|i| format!("parents[{i}]"))
                        .chain(once("object".to_owned()))
                        .join(", ");
                    let retain = retention_name(TransportRetention::Component, driver);
                    match &driver.kind {
                        DriverKind::Propagation { suffix, .. } => {
                            let name = display_type(*model, ctx).to_string().to_case(Snake);
                            writeln!(f, "component_changed |= self.__propagate_{name}_morphisms{suffix}([{parents}], {retain});")?;
                        }
                        DriverKind::Native { id, level } => {
                            let child = level + 1;
                            writeln!(f, "component_changed |= self.__native_{id}_model_{child}([{parents}], index, {retain});")?;
                        }
                    }
                }
                TransportInstruction::SelectRelations => {
                    let count = match &driver.kind {
                        DriverKind::Propagation { plan, .. } => ctx.transport().group(*plan).models
                            [&driver.model]
                            .relations
                            .len(),
                        DriverKind::Native { .. } => {
                            unreachable!("native traversal remaps one index")
                        }
                    };
                    writedoc! {f, "
                        let active: [bool; {count}] = std::array::from_fn(
                            |i| transport_all || transport_work[i].needs_visit(morphism),
                        );
                    "}?;
                }
                TransportInstruction::ContinueUnlessActive => {
                    writeln!(f, "if !active.iter().any(|&active| active) {{ continue; }}")?
                }
                TransportInstruction::InitializeInserted => {
                    let count = match &driver.kind {
                        DriverKind::Propagation { plan, .. } => ctx.transport().group(*plan).models
                            [&driver.model]
                            .relations
                            .len(),
                        DriverKind::Native { .. } => {
                            unreachable!("native traversal remaps one index")
                        }
                    };
                    writeln!(f, "let mut inserted = [false; {count}];")?;
                }
                TransportInstruction::CallMorphism { changes, retain } => {
                    let changed = changed_name(*changes);
                    let retain = retention_name(*retain, driver);
                    match &driver.kind {
                        DriverKind::Propagation { suffix, .. } => {
                            let name = display_type(driver.model, ctx).to_string().to_case(Snake);
                            writeln!(f, "{changed} |= self.__propagate_{name}_morphism_selected{suffix}(parents, morphism, {retain}, &active, &mut inserted);")?;
                        }
                        DriverKind::Native { id, level } => writeln!(f, "{changed} |= self.__native_{id}_morphism_{level}(parents, morphism, index, {retain});")?,
                    }
                }
                TransportInstruction::MarkWorkChanged => writedoc! {f, "
                    if !transport_all {{
                        for (work, inserted) in transport_work.iter_mut().zip(inserted) {{
                            if inserted {{ work.mark_changed(morphism.cod); }}
                        }}
                    }}
                "}?,
                TransportInstruction::AccumulateChanges => {
                    writeln!(f, "changed |= component_changed;")?
                }
                TransportInstruction::BreakUnlessCyclicChanged => {
                    writeln!(f, "if !cyclic || !component_changed {{ break; }}")?
                }
                TransportInstruction::ReturnChanged => writeln!(f, "changed")?,
            }
        }
        Ok(())
    })
}

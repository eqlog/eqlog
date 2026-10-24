use std::fmt::Display;

use convert_case::{Case, Casing};
use indoc::{formatdoc, writedoc};
use itertools::Itertools;

use super::{
    display_all_index_field_name, display_own_index_field_name, display_rel, display_type, indices,
    RustGenCtx,
};
use crate::algebra::signature::TypeId;
use crate::flat_eqlog::{FlatInRel, FlatRel, IndexSelection};
use crate::fmt_util::FmtFn;
use crate::ram::{
    CompactTransportBinding, CompactTransportCall, CompactTransportCondition,
    CompactTransportInstruction, CompactTransportIteration, CompactTransportLocal,
    CompactTransportOptional, CompactTransportReturn, RamProgram,
};

fn model_name(model: TypeId, ctx: &RustGenCtx<'_>) -> String {
    display_type(model, ctx).to_string().to_case(Case::Snake)
}

fn witnesses(rel: FlatRel, keys: &[(FlatRel, usize)], owner: &str, ctx: &RustGenCtx<'_>) -> String {
    let arity = rel.arity(ctx.signature());
    keys.iter().filter(|&&(candidate, _)| candidate == rel).map(|&(_, column)| {
        let member = model_name(arity[column], ctx);
        let column = column - 1;
        format!("self.__compact_members_{member}.as_mut().unwrap().witness({owner}, row[{column}]);")
    }).join("\n")
}

pub(super) fn fields<'a>(ctx: &'a RustGenCtx<'a>, initialize: bool) -> impl Display + 'a {
    FmtFn(move |f| {
        for (_, ids) in ctx.signature().iter_model_decls() {
            let model = ids.type_;
            if !ctx.compact().supports_model(model) {
                continue;
            }
            let name = model_name(model, ctx);
            if initialize {
                writeln!(f, "__compact_indices_{name}: None,")?;
                writeln!(f, "__total_members_{name}: BTreeSet::new(),")?;
                writeln!(f, "__compact_adopted_{name}: BTreeSet::new(),")?;
            } else {
                writeln!(f, "__compact_indices_{name}: Option<eqlog_runtime::__private::CompactOwnerIndices>,")?;
                writeln!(f, "__total_members_{name}: BTreeSet<u32>,")?;
                writeln!(f, "__compact_adopted_{name}: BTreeSet<u32>,")?;
            }
            for &typ in ctx.compact().members(model) {
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
        if ctx.compact().owner(&FlatInRel::Rel(rel)).is_none() {
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
        if let Some(model) = ctx.compact().owner(rel) {
            let name = model_name(model, ctx);
            writeln!(
                f,
                "if self.__compact_indices_{name}.is_some() {{ return; }}"
            )?;
        }
        Ok(())
    })
}

pub(super) fn component_guard<'a>(model: TypeId, ctx: &'a RustGenCtx<'a>) -> impl Display + 'a {
    transport_body(
        &ctx.transport().models[&model].compact.component,
        model,
        ctx,
    )
}

pub(super) fn selected_guard<'a>(model: TypeId, ctx: &'a RustGenCtx<'a>) -> impl Display + 'a {
    transport_body(&ctx.transport().models[&model].compact.selected, model, ctx)
}

fn binding_name(binding: CompactTransportBinding) -> &'static str {
    match binding {
        CompactTransportBinding::Incoming => "incoming",
        CompactTransportBinding::Morphisms => "morphisms",
        CompactTransportBinding::Indices => "indices",
        CompactTransportBinding::Next => "next",
        CompactTransportBinding::Changed => "changed",
        CompactTransportBinding::Position => "position",
    }
}

fn optional_value(source: CompactTransportOptional, name: &str) -> String {
    match source {
        CompactTransportOptional::Call(call) => match call {
            CompactTransportCall::Incoming => {
                format!("self.__compact_incoming_{name}(&components)")
            }
            CompactTransportCall::Batch => {
                format!("self.__compact_transport_batch_{name}(morphisms)")
            }
            CompactTransportCall::Morphism => format!(
                "self.__compact_transport_{name}(morphism.morph, morphism.dom, morphism.cod)"
            ),
            CompactTransportCall::Selected => {
                format!("self.__compact_transport_{name}(*morph, *dom, *cod)")
            }
        },
        CompactTransportOptional::IncomingForObject => "incoming.get(object)".to_owned(),
        CompactTransportOptional::Indices => format!("self.__compact_indices_{name}.as_ref()"),
        CompactTransportOptional::Position => "primary_position".to_owned(),
    }
}

fn transport_condition(condition: &CompactTransportCondition, name: &str) -> String {
    match condition {
        CompactTransportCondition::Active => format!("self.__compact_indices_{name}.is_some()"),
        CompactTransportCondition::CyclicComponent => "!component.internal.is_empty()".to_owned(),
        CompactTransportCondition::Batch => "batch".to_owned(),
        CompactTransportCondition::DifferentTarget => "morphism.cod != target".to_owned(),
        CompactTransportCondition::SelfEdge => "morphism.dom == target".to_owned(),
        CompactTransportCondition::PrimarySource => "Some(morphism.dom) == primary".to_owned(),
        CompactTransportCondition::Adopted => {
            format!("self.__compact_adopted_{name}.contains(&morphism.morph)")
        }
        CompactTransportCondition::And(left, right) => {
            let left = transport_condition(left, name);
            let right = transport_condition(right, name);
            format!("({left}) && ({right})")
        }
        CompactTransportCondition::Or(left, right) => {
            let left = transport_condition(left, name);
            let right = transport_condition(right, name);
            format!("({left}) || ({right})")
        }
    }
}

pub(super) fn transport_body<'a>(
    body: &'a [CompactTransportInstruction],
    model: TypeId,
    ctx: &'a RustGenCtx<'a>,
) -> impl Display + 'a {
    FmtFn(move |f| {
        let name = model_name(model, ctx);
        for instruction in body {
            match instruction {
                CompactTransportInstruction::ForEach { iteration, labeled, body } => {
                    let label = if *labeled { "'compact: " } else { "" };
                    let head = match iteration {
                        CompactTransportIteration::Components => "component in components.iter()",
                        CompactTransportIteration::Objects => "object in &component.objects",
                        CompactTransportIteration::Outgoing => "morphism in &component.outgoing",
                        CompactTransportIteration::Morphisms => "morphism in morphisms",
                        CompactTransportIteration::IncomingGroups => "(&target, morphisms) in &mut incoming",
                        CompactTransportIteration::EnumeratedMorphisms => "(position, morphism) in morphisms.iter().enumerate()",
                    };
                    let body = transport_body(body, model, ctx);
                    writeln!(f, "{label}for {head} {{ {body} }}")?;
                }
                CompactTransportInstruction::If { condition, then_body, else_body } => {
                    let condition = transport_condition(condition, &name);
                    let then_body = transport_body(then_body, model, ctx);
                    writeln!(f, "if {condition} {{ {then_body}")?;
                    if !else_body.is_empty() {
                        let else_body = transport_body(else_body, model, ctx);
                        writeln!(f, "}} else {{ {else_body}")?;
                    }
                    writeln!(f, "}}")?;
                }
                CompactTransportInstruction::IfSome { binding, source, then_body, else_body } => {
                    let binding = binding_name(*binding);
                    let source = optional_value(*source, &name);
                    let then_body = transport_body(then_body, model, ctx);
                    writeln!(f, "if let Some({binding}) = {source} {{ {then_body}")?;
                    if !else_body.is_empty() {
                        let else_body = transport_body(else_body, model, ctx);
                        writeln!(f, "}} else {{ {else_body}")?;
                    }
                    writeln!(f, "}}")?;
                }
                CompactTransportInstruction::RequireSome { binding, source, else_body } => {
                    let binding = binding_name(*binding);
                    let source = optional_value(*source, &name);
                    let else_body = transport_body(else_body, model, ctx);
                    writeln!(f, "let Some({binding}) = {source} else {{ {else_body} }};")?;
                }
                CompactTransportInstruction::Initialize(local) => match local {
                    CompactTransportLocal::Changed => writeln!(f, "let mut changed = false;")?,
                    CompactTransportLocal::Batch => writeln!(f, "let mut batch = true;")?,
                    CompactTransportLocal::Target => writeln!(f, "let target = morphisms[0].cod;")?,
                    CompactTransportLocal::Incoming => writeln!(f, "let mut incoming = BTreeMap::<u32, Vec<MorphismWithSignature>>::new();")?,
                    CompactTransportLocal::Primary => writeln!(f, "let primary = indices.has_owner(target).then(|| indices.source(target)).flatten();")?,
                    CompactTransportLocal::Position => writeln!(f, "let mut primary_position = None;")?,
                },
                CompactTransportInstruction::AccumulateChanged => writeln!(f, "changed |= next;")?,
                CompactTransportInstruction::RejectBatch => writeln!(f, "batch = false;")?,
                CompactTransportInstruction::RecordIncoming => writeln!(f, "incoming.entry(morphism.cod).or_default().push(morphism.clone());")?,
                CompactTransportInstruction::RememberPosition => writeln!(f, "primary_position = Some(position);")?,
                CompactTransportInstruction::RotatePrimary => writeln!(f, "morphisms[..=position].rotate_right(1);")?,
                CompactTransportInstruction::FillInserted => writeln!(f, "inserted.fill(changed);")?,
                CompactTransportInstruction::Break { labeled } => {
                    let label = if *labeled { " 'compact" } else { "" };
                    writeln!(f, "break{label};")?;
                }
                CompactTransportInstruction::Return(result) => match result {
                    CompactTransportReturn::None => writeln!(f, "return None;")?,
                    CompactTransportReturn::Changed => writeln!(f, "return changed;")?,
                    CompactTransportReturn::Incoming => writeln!(f, "return Some(incoming);")?,
                },
            }
        }
        Ok(())
    })
}

pub(super) fn methods<'a>(
    ctx: &'a RustGenCtx<'a>,
    selection: &'a IndexSelection,
    program: &'a RamProgram,
) -> impl Display + 'a {
    FmtFn(move |f| {
        let native = &program.native_indices;
        for (_, ids) in ctx.signature().iter_model_decls() {
            let model = ids.type_;
            if !ctx.compact().supports_model(model) {
                continue;
            }
            let name = model_name(model, ctx);
            let members = ctx.compact().members(model);
            let plan = ctx.compact().model(model).unwrap();
            let layouts = &plan.layouts;
            let keys = &plan.keys;
            let owner_leading = plan.owner_leading;
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
            for layout in layouts {
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
                let witnesses = witnesses(layout.rel, keys, "el0", ctx);
                writeln!(f, "for [{args}] in self.{own}.iter() {{ let row = [{row}]; indices.record(el0, {relation}, &row, true); {witnesses} }}")?;
            }
            let incoming_body =
                transport_body(&ctx.transport().models[&model].compact.incoming, model, ctx);
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

                fn __compact_incoming_{name}(&self, components: &[MorphismComponent])
                    -> Option<BTreeMap<u32, Vec<MorphismWithSignature>>>
                {{
                    {incoming_body}
                }}

                fn __compact_publish_{name}(&mut self, owner: u32) {{
                    let indices = self.__compact_indices_{name}.as_ref().unwrap();
            "}?;
            for layout in layouts {
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
            for &typ in members {
                let member = model_name(typ, ctx);
                let update = publish_tree(&format!("self.__compact_domain_{member}"), 1);
                writedoc! {f, "
                    let suffix = PrefixTree1 {{ set: self.__compact_members_{member}.as_ref().unwrap()
                        .get_snapshot(owner).unwrap().canonical_domain().clone() }};
                    {update}
                "}?;
            }
            writeln!(f, "}}")?;
            for layout in layouts {
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
                let witnesses = witnesses(layout.rel, keys, "owner", ctx);
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
                        {witnesses}
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
                format!("let spaces = self.__compact_members_{member}.as_mut().unwrap(); force |= spaces.refresh_with_merges(target).is_some(); let source_{member_type} = spaces.snapshot(source); merges.extend(spaces.local_merges(target).iter().map(|merge| ({member_type}, merge.loser, merge.winner))); self.__sync_compact_{member}_weights();")
            }).join("\n");
            let normalize = members.iter().enumerate().map(|(member_type, _)| {
                format!("{member_type} => source_{member_type}.root_origin(origin).unwrap_or(origin),")
            }).join("\n");
            let inherit = members.iter().map(|&typ| {
                let member = model_name(typ, ctx);
                format!("force |= self.__compact_members_{member}.as_mut().unwrap().inherit_total_members_with_merges(source, target).is_some(); self.__sync_compact_{member}_weights();")
            }).join("\n");
            let register = members.iter().map(|&typ| {
                let member = model_name(typ, ctx);
                format!("self.__compact_members_{member}.as_mut().unwrap().register_edge(source, target);")
            }).join("\n");
            let share = members.iter().map(|&typ| {
                let member = model_name(typ, ctx);
                format!("self.__compact_members_{member}.as_mut().unwrap().install_shared_inheritance(shared_{member}); self.__sync_compact_{member}_weights();")
            }).join("\n");
            let prepare = |method: &str, arguments: &str| {
                members.iter().map(|&typ| {
                    let member = model_name(typ, ctx);
                    formatdoc!("
                        let Some(shared_{member}) = self.__compact_members_{member}.as_ref().unwrap().{method}({arguments}, target) else {{
                            self.__materialize_compact_members();
                            self.__complete_total_members();
                            return None;
                        }};")
                }).join("\n")
            };
            let prepare_shared = prepare("prepare_shared_inheritance", "source");
            let prepare_shared_many = prepare("prepare_shared_inheritance_many", "&sources");
            let can_refresh = members
                .iter()
                .map(|&typ| {
                    let member = model_name(typ, ctx);
                    format!("self.__compact_members_{member}.as_ref().unwrap().can_refresh(target)")
                })
                .join(" && ");
            let first_member = model_name(members[0], ctx);
            let refresh = formatdoc! {"
                if !({can_refresh}) {{
                    self.__materialize_compact_members();
                    self.__complete_total_members();
                    return None;
                }}
                let source = self.__compact_members_{first_member}.as_ref().unwrap().source(target).unwrap();
                Some(self.__compact_refresh_{name}_impl(source, target, false))
            "};
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

                fn __compact_register_{name}(&mut self, morphism: u32, source: u32, target: u32) -> bool {{
                    self.__compact_ensure_{name}_owner(source);
                    self.__compact_ensure_{name}_owner(target);
                    {register}
                    self.__compact_indices_{name}.as_mut().unwrap().register_edge(source, target);
                    if self.__compact_members_{first_member}.as_ref().unwrap().source(target).is_none() {{
                        let changed = self.__compact_inherit_{name}(source, target);
                        self.__compact_adopted_{name}.insert(morphism);
                        return changed;
                    }}
                    false
                }}

                fn __compact_transport_{name}(&mut self, morphism: u32, source: u32, target: u32) -> Option<bool> {{
                    self.__compact_indices_{name}.as_ref()?;
                    if !self.__compact_adopted_{name}.contains(&morphism) {{
                        {prepare_shared}
                        {share}
                        self.__compact_indices_{name}.as_mut().unwrap().inherit_shared(target, source);
                        self.__compact_adopted_{name}.insert(morphism);
                        self.__compact_publish_{name}(target);
                        return Some(true);
                    }}
                    {refresh}
                }}

                fn __compact_transport_batch_{name}(&mut self, morphisms: &[MorphismWithSignature]) -> Option<bool> {{
                    self.__compact_indices_{name}.as_ref()?;
                    let Some(first) = morphisms.first() else {{ return Some(false); }};
                    let target = first.cod;
                    let mut seen_morphisms = BTreeSet::new();
                    let (new_morphisms, sources): (Vec<_>, Vec<_>) = morphisms.iter()
                        .filter(|morphism| !self.__compact_adopted_{name}.contains(&morphism.morph) && seen_morphisms.insert(morphism.morph))
                        .map(|morphism| (morphism.morph, morphism.dom))
                        .unzip();
                    if !sources.is_empty() {{
                        {prepare_shared_many}
                        {share}
                        self.__compact_indices_{name}.as_mut().unwrap().inherit_shared_many(target, &sources);
                        self.__compact_adopted_{name}.extend(new_morphisms);
                        self.__compact_publish_{name}(target);
                        return Some(true);
                    }}
                    {refresh}
                }}
            "}?;
        }
        Ok(())
    })
}

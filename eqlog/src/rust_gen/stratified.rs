use convert_case::{Case, Casing};
use itertools::Itertools;
use std::collections::{BTreeMap, BTreeSet};
use std::fmt::Display;

use indoc::{formatdoc, writedoc};

use super::indices::{projection, source_relation};
use super::native_indices;
use super::{compact_indices, compact_policy};
use super::{
    display_all_index_field_name, display_index_field_name, display_index_type,
    display_module_env_struct_name, display_morphism_components, display_out_set_field_name,
    display_type, module_env_out_rels, RustGenCtx,
};
use crate::algebra::signature::TypeId;
use crate::flat_eqlog::{FlatInRel, FlatOutRel, FlatRel, IndexAge, IndexSelection, IndexSpec};
use crate::fmt_util::FmtFn;
use crate::ram::{
    input_key, CanonicalInput, EvaluationCondition, EvaluationIteration, EvaluationPlan,
    EvaluationStmt, IndexPreparation, InheritedInput, InheritedRows, InputStorage,
    NativeIndexPreparation, NativePreparation, ProofRows, RamFunction, RamProgram, RetainedOwners,
    StratumEvaluation, TransportBaseline, TransportEdges,
};

pub struct Codegen<'s> {
    evaluation: &'s EvaluationPlan,
    strata: &'s [StratumEvaluation],
    body: &'s [EvaluationStmt],
    models: &'s BTreeMap<TypeId, usize>,
    inputs: &'s BTreeMap<FlatInRel, usize>,
    indices: &'s BTreeMap<(FlatInRel, IndexSpec), usize>,
    old_indices: &'s BTreeSet<(FlatInRel, IndexSpec)>,
    preparations: &'s [IndexPreparation],
    native_indices: &'s [NativeIndexPreparation],
    model_preparations: &'s BTreeMap<TypeId, NativePreparation>,
}

fn input_name(storage: InputStorage) -> String {
    match storage {
        InputStorage::Relation(id) => format!("input_{id}"),
        InputStorage::Index(id) => format!("index_{id}"),
        InputStorage::Native(id) => format!("native_input_{id}"),
    }
}

fn history_name(storage: InputStorage, count: usize) -> String {
    match storage {
        InputStorage::Relation(id) => format!("__scope_input_{id}_{count}"),
        InputStorage::Index(id) => format!("__scope_index_{id}_{count}"),
        InputStorage::Native(id) => format!("__scope_native_{id}_{count}"),
    }
}

impl<'s> Codegen<'s> {
    fn diagonal_input(
        &self,
        stratum: usize,
        source: &FlatInRel,
        selection: &IndexSelection,
        ctx: &RustGenCtx<'_>,
    ) -> Option<String> {
        if !self.evaluation.strata[stratum]
            .diagonal_inputs
            .contains(source)
        {
            return None;
        }
        let primary = selection.current_primary(source);
        let field = display_all_index_field_name(source, primary, ctx);
        let arity = primary.order.len();
        let suffix = arity - 1;
        Some(formatdoc! {"
            {{
                let mut filtered = PrefixTree{arity}::new();
                for (key, rows) in self.{field}.map.iter() {{
                    if let Some(rows) = rows.get(key) {{
                        let mut suffix = PrefixTree{suffix}::new();
                        suffix.insert_restriction(key, rows.clone());
                        filtered.insert_restriction(key, suffix);
                    }}
                }}
                filtered
            }}
        "})
    }

    fn transport_baseline(&self, model: TypeId) -> Option<&TransportBaseline> {
        self.evaluation.transport_baselines.get(&model)
    }

    pub fn tracks_owner(&self, typ: TypeId, _ctx: &RustGenCtx<'_>) -> bool {
        self.evaluation.tracked_owners.contains(&typ)
    }

    fn stratum_inputs(&self, s: usize) -> BTreeSet<FlatInRel> {
        self.evaluation.strata[s].inputs.clone()
    }

    fn has_stable_inputs(&self, s: usize) -> bool {
        !self.evaluation.strata[s].stable_fields.is_empty()
    }

    fn consume_method(&self, s: usize, rel: &FlatInRel, index: &IndexSpec) -> &'static str {
        if self.preparations[s]
            .membership_only
            .contains(&input_key(rel.clone(), index.clone()))
        {
            "consume_membership"
        } else {
            "consume_required"
        }
    }

    fn inherited_rows(&self, input: &InheritedInput, ctx: &RustGenCtx<'_>) -> String {
        match input.rows {
            InheritedRows::MemberDomain(typ) => {
                let name = display_type(typ, ctx).to_string().to_case(Case::Snake);
                format!("PrefixTree1 {{ set: source_{name}.canonical_domain().clone() }}")
            }
            InheritedRows::CompactIndex(slot) => {
                let arity = input.arity;
                format!("<&PrefixTree{arity}>::try_from(rows.get({slot})?).expect(\"inherited index arity\").clone()")
            }
            InheritedRows::Global => {
                let field = display_all_index_field_name(&input.rel, &input.index, ctx);
                format!("self.{field}.clone()")
            }
        }
    }

    fn matching_rows(&self, input: &InheritedInput, ctx: &RustGenCtx<'_>) -> String {
        match input.rows {
            InheritedRows::MemberDomain(typ) => {
                let name = display_type(typ, ctx).to_string().to_case(Case::Snake);
                format!("PrefixTree1 {{ set: self.__compact_members_{name}.as_ref()?.get_snapshot(owners[0])?.canonical_domain().clone() }}")
            }
            InheritedRows::CompactIndex(slot) => {
                let arity = input.arity;
                format!("<&PrefixTree{arity}>::try_from(indices.rows(owners[0], {slot})).expect(\"matching index arity\").clone()")
            }
            InheritedRows::Global => {
                let field = display_all_index_field_name(&input.rel, &input.index, ctx);
                format!("self.{field}.clone()")
            }
        }
    }

    fn inherited_plan(&self, s: usize) -> Option<BTreeMap<String, &InheritedInput>> {
        self.evaluation.strata[s].inherited.as_ref().map(|fields| {
            fields
                .iter()
                .map(|(&storage, input)| (input_name(storage), input))
                .collect()
        })
    }

    pub fn loop_input_types<'a>(
        &'a self,
        _selection: &'a IndexSelection,
        ctx: &'a RustGenCtx<'a>,
    ) -> impl Display + 'a {
        FmtFn(move |f| {
            for (&model, &m) in self.models {
                let Some(baseline) = self.transport_baseline(model) else {
                    continue;
                };
                writeln!(f, "struct __TransportBaseline{m} {{")?;
                let count = baseline.relations.len();
                writeln!(
                    f,
                    "work: [eqlog_runtime::__private::TransportWork; {count}],"
                )?;
                for (i, rel) in baseline.relations.iter().enumerate() {
                    let typ = display_index_type(rel, ctx);
                    writeln!(f, "source_{i}: {typ},")?;
                }
                for (i, (rel, _)) in baseline.maps.iter().enumerate() {
                    let typ = display_index_type(rel, ctx);
                    writeln!(f, "map_{i}: {typ},")?;
                }
                writeln!(f, "}}")?;
            }
            for (s, stratum) in self.strata.iter().enumerate() {
                let inherited = self.inherited_plan(s);
                if let Some(model) = stratum.model {
                    writeln!(f, "struct __OwnerInputs{s} {{")?;
                    if inherited.is_some() {
                        let members = compact_indices::members(model, ctx).len();
                        writeln!(f, "inherited: Option<(u32, u64, [u64; {members}])>,")?;
                        writeln!(f, "inherited_seen: std::rc::Rc<std::collections::BTreeMap<u32, (u64, [u64; {members}])>>,")?;
                        writeln!(f, "matching_proof: Option<__InheritedInputs{s}>,")?;
                    }
                    for rel in self.stratum_inputs(s) {
                        let i = self.inputs[&rel];
                        let arity =
                            rel.arity(ctx.signature()).len() - scope_prefix(&rel, model, ctx);
                        writeln!(f, "input_{i}: PrefixTree{arity},")?;
                    }
                    writeln!(f, "}}")?;
                    if let Some(fields) = inherited {
                        let members = compact_indices::members(model, ctx).len();
                        writeln!(f, "#[derive(Clone)] struct __InheritedInputs{s} {{ revision: (u32, u64, [u64; {members}]),")?;
                        for (name, input) in fields {
                            let arity = input.arity;
                            writeln!(f, "{name}: PrefixTree{arity},")?;
                        }
                        writeln!(f, "}}")?;
                    }
                }
                let fields = &self.evaluation.strata[s].stable_fields;
                if fields.is_empty() {
                    continue;
                }
                writeln!(f, "#[derive(Default)] struct __StableInputs{s} {{")?;
                if self.preparations[s].stable.is_some() {
                    writeln!(f, "propagated: bool,")?;
                }
                for (&storage, rel) in fields {
                    let name = input_name(storage);
                    let typ = display_index_type(&rel, ctx);
                    writeln!(f, "{name}: Option<{typ}>,")?;
                }
                writeln!(f, "}}")?;
            }
            Ok(())
        })
    }

    fn scoped_histories(&self) -> BTreeMap<String, (Vec<TypeId>, usize)> {
        self.evaluation
            .scoped_histories
            .iter()
            .map(|history| {
                (
                    history_name(history.storage, history.owners.len()),
                    (history.owners.clone(), history.arity),
                )
            })
            .collect()
    }

    pub fn new(program: &'s RamProgram) -> Self {
        let evaluation = &program.evaluation;
        Self {
            evaluation,
            strata: &evaluation.strata,
            body: &evaluation.body,
            models: &evaluation.models,
            preparations: &program.preparations,
            native_indices: &program.native_indices,
            model_preparations: &program.model_preparations,
            old_indices: &evaluation.old_indices,
            inputs: &evaluation.inputs,
            indices: &evaluation.indices,
        }
    }

    pub fn fields<'a>(
        &'a self,
        ctx: &'a RustGenCtx<'a>,
        selection: &'a IndexSelection,
    ) -> impl Display + 'a {
        FmtFn(move |f| {
            let count = self.strata.len();
            writeln!(f, "__stratum_initialized: [bool; {count}],")?;
            writeln!(f, "__model_owners_changed: bool,")?;
            for (_, ids) in ctx
                .signature()
                .iter_model_decls()
                .filter(|(_, ids)| self.tracks_owner(ids.type_, ctx))
            {
                let name = display_type(ids.type_, ctx)
                    .to_string()
                    .to_case(Case::Snake);
                writeln!(f, "__merged_{name}: std::collections::BTreeSet<u32>,")?;
            }
            for (s, stratum) in self.strata.iter().enumerate() {
                if let Some(model) = stratum.model {
                    let count = ctx.signature().type_(model).parents.len() + 1;
                    writeln!(
                        f,
                        "__owner_inputs_{s}: std::collections::BTreeMap<[u32; {count}], __OwnerInputs{s}>,"
                    )?;
                }
            }
            for (field, (owners, arity)) in self.scoped_histories() {
                let count = owners.len();
                writeln!(f, "{field}: std::collections::BTreeMap<[u32; {count}], eqlog_runtime::__private::RelationVersions<PrefixTree{arity}, (usize, Vec<u32>)>>,")?;
            }
            for (rel, i) in self.inputs {
                let typ = display_index_type(rel, ctx);
                writeln!(
                    f,
                    "__rule_input_{i}: eqlog_runtime::__private::RelationVersions<{typ}, (usize, Vec<u32>)>,"
                )?;
            }
            for ((rel, index), i) in self.indices {
                if selection.is_primary(rel, index)
                    || native_indices::find(self.native_indices, rel, index).is_some()
                {
                    continue;
                }
                let source = source_relation(rel);
                let source_type = display_index_type(&source, ctx);
                let target = display_index_type(rel, ctx);
                writeln!(f, "__rule_index_{i}: eqlog_runtime::__private::IndexSeed<{source_type}, {target}>,")?;
                if self.old_indices.contains(&(rel.clone(), index.clone())) {
                    writeln!(f, "__rule_index_{i}_versions: eqlog_runtime::__private::RelationVersions<{target}, (usize, Vec<u32>)>,")?;
                }
            }
            Ok(())
        })
    }

    pub fn init<'a>(
        &'a self,
        selection: &'a IndexSelection,
        ctx: &'a RustGenCtx<'a>,
    ) -> impl Display + 'a {
        FmtFn(move |f| {
            let count = self.strata.len();
            writeln!(f, "__stratum_initialized: [false; {count}],")?;
            writeln!(f, "__model_owners_changed: false,")?;
            for (_, ids) in ctx
                .signature()
                .iter_model_decls()
                .filter(|(_, ids)| self.tracks_owner(ids.type_, ctx))
            {
                let name = display_type(ids.type_, ctx)
                    .to_string()
                    .to_case(Case::Snake);
                writeln!(f, "__merged_{name}: std::collections::BTreeSet::new(),")?;
            }
            for (s, stratum) in self.strata.iter().enumerate() {
                if stratum.model.is_some() {
                    writeln!(f, "__owner_inputs_{s}: std::collections::BTreeMap::new(),")?;
                }
            }
            for field in self.scoped_histories().keys() {
                writeln!(f, "{field}: std::collections::BTreeMap::new(),")?;
            }
            for i in self.inputs.values() {
                writeln!(
                    f,
                    "__rule_input_{i}: eqlog_runtime::__private::RelationVersions::new(),"
                )?;
            }
            for ((rel, index), i) in self.indices {
                if selection.is_primary(rel, index)
                    || native_indices::find(self.native_indices, rel, index).is_some()
                {
                    continue;
                }
                writeln!(
                    f,
                    "__rule_index_{i}: eqlog_runtime::__private::IndexSeed::new(),"
                )?;
                if self.old_indices.contains(&(rel.clone(), index.clone())) {
                    writeln!(
                        f,
                        "__rule_index_{i}_versions: eqlog_runtime::__private::RelationVersions::new(),"
                    )?;
                }
            }
            Ok(())
        })
    }

    pub fn methods<'a>(
        &'a self,
        modules: &'a [RamFunction],
        ctx: &'a RustGenCtx<'a>,
        selection: &'a IndexSelection,
    ) -> impl Display + 'a {
        FmtFn(move |f| {
            for (s, stratum) in self.strata.iter().enumerate() {
                let inputs = self.stratum_inputs(s);
                let inherited_plan = self.inherited_plan(s);
                if let Some(fields) = &inherited_plan {
                    // A matching checkpoint proves only its exact input roots.
                    // The source revision also covers transported conclusions.
                    let model = stratum.model.unwrap();
                    let name = display_type(model, ctx).to_string().to_case(Case::Snake);
                    let members = compact_indices::members(model, ctx).len();
                    writedoc! {f, "
                        fn __matching_inputs_{s}(&self, owners: [u32; 1]) -> Option<__InheritedInputs{s}> {{
                            let indices = self.__compact_indices_{name}.as_ref()?;
                            if !indices.has_owner(owners[0]) {{ return None; }}
                            let revision = (owners[0], 0, [0; {members}]);
                    "}?;
                    for (field, input) in fields {
                        let rows = self.matching_rows(input, ctx);
                        writeln!(f, "let {field} = {rows};")?;
                    }
                    let names = fields.keys().join(", ");
                    writeln!(f, "Some(__InheritedInputs{s} {{ revision, {names} }}) }}")?;
                    writedoc! {f, "
                        fn __inherited_inputs_{s}(&self, owners: [u32; 1]) -> Option<(Option<__InheritedInputs{s}>, Vec<__InheritedInputs{s}>)> {{
                            let indices = self.__compact_indices_{name}.as_ref()?;
                            if !indices.has_owner(owners[0]) {{ return None; }}
                    "}?;
                    let member_types = compact_indices::members(model, ctx);
                    for &typ in &member_types {
                        let name = display_type(typ, ctx).to_string().to_case(Case::Snake);
                        writedoc! {f, "
                            let spaces_{name} = self.__compact_members_{name}.as_ref()?;
                            let inputs_{name} = spaces_{name}.inherited_inputs(owners[0])?;
                        "}?;
                    }
                    writedoc! {f, "
                        let mut best: Option<(u64, usize)> = None;
                        let mut certified = Vec::new();
                        for (position, (source, revision, rows)) in indices.inherited_inputs(owners[0]).enumerate() {{
                            let candidate = (|| {{
                                if indices.revision(source) != revision {{ return None; }}
                                let mut score = 0u64;
                    "}?;
                    let mut revisions = Vec::new();
                    for &typ in &member_types {
                        let name = display_type(typ, ctx).to_string().to_case(Case::Snake);
                        writedoc! {f, "
                            let (member_source, revision_{name}, domain_{name}) = inputs_{name}.get(position)?;
                            if member_source != source {{ return None; }}
                            let source_{name} = spaces_{name}.get_snapshot(source)?;
                            if source_{name}.revision() != revision_{name} {{ return None; }}
                            score = score.checked_add(u64::try_from(domain_{name}.len()).unwrap())
                                .expect(\"inherited matching score overflow\");
                        "}?;
                        revisions.push(format!("revision_{name}"));
                    }
                    let revisions = revisions.join(", ");
                    writedoc! {f, "
                        let revision = (source, revision, [{revisions}]);
                        let proved = self.__owner_inputs_{s}.get(&[source])?;
                    "}?;
                    for (name, input) in fields {
                        let arity = input.arity;
                        let rows = self.inherited_rows(input, ctx);
                        writeln!(f, "let {name}: PrefixTree{arity} = {rows};")?;
                    }
                    for rel in &inputs {
                        let i = self.inputs[rel];
                        match rel {
                            FlatInRel::TypeSet(_) => {
                                writeln!(f, "if !input_{i}.contains([source]) || !input_{i}.contains([owners[0]]) {{ return None; }}")?;
                            }
                            FlatInRel::Rel(_)
                            | FlatInRel::RelWithDiagonals { .. }
                            | FlatInRel::Equality(_) => {
                                writeln!(f, "if !eqlog_runtime::__private::SnapshotSet::shares_root(&input_{i}, &proved.input_{i}) {{ return None; }}")?;
                            }
                        }
                    }
                    let names = fields.keys().join(", ");
                    writedoc! {f, "
                                Some((score, __InheritedInputs{s} {{ revision, {names} }}))
                            }})();
                            let Some((score, candidate)) = candidate else {{ continue; }};
                            if best.as_ref().is_none_or(|(previous, _)| score > *previous) {{
                                best = Some((score, certified.len()));
                            }}
                            certified.push(candidate);
                        }}
                        let (_, best) = best?;
                        let previous = self.__owner_inputs_{s}.get(&owners)?;
                        let baseline = (previous.inherited != Some(certified[best].revision))
                            .then(|| certified[best].clone());
                        certified.retain(|proof| {{
                            let (source, revision, members) = proof.revision;
                            previous.inherited_seen.get(&source) != Some(&(revision, members))
                        }});
                        Some((baseline, certified))
                    }}
                    "}?;
                }
                let evaluation = &self.evaluation.strata[s];
                let outputs = &evaluation.outputs;
                let stable = if self.has_stable_inputs(s) {
                    format!("stable: &mut __StableInputs{s}, ")
                } else {
                    String::new()
                };
                writeln!(f, "#[allow(unused_variables)]")?;
                if let Some(model) = stratum.model {
                    let count = ctx.signature().type_(model).parents.len() + 1;
                    let retain = if !self.preparations[s].reads_descendants() {
                        ""
                    } else {
                        "retain_own: bool, "
                    };
                    writedoc! {f, "
                        fn __run_stratum_{s}_at(&mut self, owners: [u32; {count}], {retain}{stable}delta: &mut ModelDelta) -> bool {{
                    "}?;
                } else {
                    writedoc! {f, "
                        fn __run_stratum_{s}(&mut self, {stable}delta: &mut ModelDelta) -> bool {{
                            #[allow(unused_mut)]
                            let mut dirty = !self.__stratum_initialized[{s}];
                    "}?;
                }
                for conversion in &evaluation.output_conversions {
                    if conversion.pending {
                        let field = display_out_set_field_name(&conversion.output, ctx);
                        writeln!(f, "let __compact_start_{field} = delta.{field}.len();")?;
                    }
                }
                if let Some(plan) = &self.preparations[s].stable {
                    writeln!(f, "if !stable.propagated {{")?;
                    if stratum.model.is_none() {
                        writeln!(f, "self.recompute_model_indices_stratum_stable_{s}();")?;
                    } else if !plan.descendants.is_empty() {
                        writeln!(
                            f,
                            "self.__prepare_descendants_stable_{s}(owners, retain_own);"
                        )?;
                    }
                    if plan.descendants.is_empty() {
                        for (rel, index) in &plan.support_indices {
                            write!(f, "{}", super::indices::prepare(rel, index, selection, ctx))?;
                        }
                    }
                    writeln!(f, "stable.propagated = true; }}")?;
                }
                let native = &self.preparations[s].native;
                if !native.descendants.is_empty() {
                    writeln!(f, "self.__prepare_descendants_{s}(owners, retain_own);")?;
                }
                if stratum.model.is_none() && !native.propagation.relations.is_empty() {
                    writeln!(f, "self.recompute_model_indices_stratum_{s}();")?;
                }
                if let Some(model) = stratum.model {
                    // Most owners have no new input on an incremental visit.
                    // Comparing roots avoids constructing their consumer views.
                    let mut unchanged = vec!["true".to_owned()];
                    let mut snapshots = Vec::new();
                    for rel in &inputs {
                        let i = self.inputs[rel];
                        let field =
                            display_all_index_field_name(rel, selection.current_primary(rel), ctx);
                        let source = scoped_tree(&format!("&self.{field}"), rel, model, ctx);
                        writeln!(f, "let input_{i} = {source};")?;
                        unchanged.push(format!("eqlog_runtime::__private::SnapshotSet::shares_root(input_{i}, &_previous.input_{i})"));
                        snapshots.push(format!("input_{i}: input_{i}.clone()"));
                    }
                    let unchanged = unchanged.join(" && ");
                    if inherited_plan.is_some() {
                        snapshots.push(
                            "inherited: previous.and_then(|previous| previous.inherited)"
                                .to_owned(),
                        );
                        snapshots.push("inherited_seen: previous.map(|previous| previous.inherited_seen.clone()).unwrap_or_default()".to_owned());
                        snapshots.push(format!(
                            "matching_proof: self.__matching_inputs_{s}(owners)"
                        ));
                    }
                    let snapshots = snapshots.join(", ");
                    let previous_proof = if inherited_plan.is_some() {
                        "let previous_matching_proof = previous.and_then(|previous| previous.matching_proof.clone());"
                    } else {
                        ""
                    };
                    writedoc! {f, "
                        let previous = self.__owner_inputs_{s}.get(&owners);
                        #[allow(unused_mut)]
                        let mut dirty = previous.is_none();
                        if previous.is_some_and(|_previous| {unchanged}) {{
                            return false;
                        }}
                        {previous_proof}
                        let checkpoint = __OwnerInputs{s} {{ {snapshots} }};
                        self.__owner_inputs_{s}.insert(owners, checkpoint);
                    "}?;
                    if let Some(possible) = &evaluation.possible_inputs {
                        let terms: BTreeSet<_> = possible
                            .iter()
                            .map(|sources| {
                                sources
                                    .iter()
                                    .map(|i| format!("!input_{i}.is_empty()"))
                                    .join(" && ")
                            })
                            .collect();
                        let possible = if terms.is_empty() {
                            "false".to_owned()
                        } else {
                            terms.iter().map(|expr| format!("({expr})")).join(" || ")
                        };
                        writeln!(f, "if !({possible}) {{ return false; }}")?;
                    }
                }
                if inherited_plan.is_some() {
                    // New inherited facts can join local facts matched earlier.
                    // Reset every index together, then resume temporal deltas.
                    writedoc! {f, "
                        let (inherited_baseline, mut matching_proofs) = if delta.has_pending_func_defs() {{
                            (None, Vec::new())
                        }} else {{ self.__inherited_inputs_{s}(owners).unwrap_or_default() }};
                        if !matching_proofs.is_empty() {{
                            let seen = &mut self.__owner_inputs_{s}.get_mut(&owners).unwrap().inherited_seen;
                            let seen = std::rc::Rc::make_mut(seen);
                            for proof in &matching_proofs {{
                                let (source, revision, members) = proof.revision;
                                seen.insert(source, (revision, members));
                            }}
                        }}
                        if let Some(baseline) = &inherited_baseline {{
                            self.__owner_inputs_{s}.get_mut(&owners).unwrap().inherited = Some(baseline.revision);
                            matching_proofs.retain(|proof| proof.revision != baseline.revision);
                            if let Some(previous) = previous_matching_proof {{ matching_proofs.push(previous); }}
                            dirty = true;
                    "}?;
                    if self.has_stable_inputs(s) {
                        writeln!(f, "*stable = __StableInputs{s}::default();")?;
                    }
                    writeln!(f, "}}")?;
                }
                for rel in inputs {
                    let i = self.inputs[&rel];
                    let consume = self.consume_method(s, &rel, selection.current_primary(&rel));
                    let old = self.preparations[s].indices.iter().any(|(input, index)| {
                        input == &rel
                            && index.age == IndexAge::Old
                            && selection.is_primary(input, index)
                    });
                    let stable = stratum.stable_inputs.contains(&rel);
                    let stable_global = stable && stratum.model.is_none();
                    if stable && !stable_global {
                        begin_stable_input(f, &format!("input_{i}"), &rel, ctx)?;
                    }
                    if stable_global {
                        writedoc! {f, "
                            if let Some(current) = &stable.input_{i} {{
                                self.__rule_input_{i}.publish(current);
                            }} else {{
                        "}?;
                    }
                    let current =
                        display_all_index_field_name(&rel, selection.current_primary(&rel), ctx);
                    if let Some(filtered) = self.diagonal_input(s, &rel, selection, ctx) {
                        // Every consumer in this stratum requires this diagonal.
                        // Restrict before computing differences or projecting rows.
                        writeln!(f, "let filtered_input_{i} = {filtered};")?;
                        writeln!(f, "self.__rule_input_{i}.publish(&filtered_input_{i});")?;
                    } else {
                        writeln!(f, "self.__rule_input_{i}.publish(&self.{current});")?;
                    }
                    if stable_global {
                        writeln!(f, "}}")?;
                        begin_stable_input(f, &format!("input_{i}"), &rel, ctx)?;
                    }
                    if let Some(model) = stratum.model {
                        consume_scoped(
                            f,
                            &format!("__scope_input_{i}"),
                            &format!("self.__rule_input_{i}.current()"),
                            &format!("__rule_input_{i}"),
                            &format!("input_{i}"),
                            &rel,
                            model,
                            s,
                            old,
                            true,
                            consume,
                            inherited_plan.as_ref().map(|_| format!("inherited_baseline.as_ref().map(|baseline| &baseline.input_{i})")).as_deref(),
                            ctx,
                        )?;
                    } else {
                        writeln!(
                            f,
                            "let input_{i} = self.__rule_input_{i}.{consume}::<{old}, true>(({s}, Vec::new()));"
                        )?;
                    }
                    if stable {
                        end_stable_input(
                            f,
                            &format!("input_{i}"),
                            &format!("self.__rule_input_{i}.current()"),
                            &rel,
                            stratum.model,
                            ctx,
                        )?;
                    }
                    writeln!(f, "dirty |= !input_{i}.new.is_empty();")?;
                }
                writeln!(f, "if !dirty {{ return false; }}")?;
                if stratum.model.is_none() {
                    writeln!(f, "self.__stratum_initialized[{s}] = true;")?;
                }
                writeln!(f, "{{")?;
                if native.descendants.is_empty() {
                    for (rel, index) in &native.support_indices {
                        write!(f, "{}", super::indices::prepare(rel, index, selection, ctx))?;
                    }
                }
                for id in self.preparations[s].native_indices() {
                    let rel = &self.native_indices[*id].rel;
                    let consume = self.consume_method(s, rel, &self.native_indices[*id].index);
                    let stable = stratum.stable_inputs.contains(&source_relation(rel));
                    if stable {
                        begin_stable_input(f, &format!("native_input_{id}"), rel, ctx)?;
                    }
                    if self.native_indices[*id].from_primary {
                        writeln!(f, "self.__prepare_native_index_from_primary_{id}();")?;
                    } else if stratum.model.is_some() {
                        writeln!(f, "self.__extend_native_index_{id}();")?;
                    } else {
                        writeln!(f, "self.__prepare_native_index_{id}();")?;
                    }
                    if let Some(model) = stratum.model {
                        consume_scoped(
                            f,
                            &format!("__scope_native_{id}"),
                            &format!("self.__native_input_{id}.current()"),
                            &format!("__native_input_{id}"),
                            &format!("native_input_{id}"),
                            &self.native_indices[*id].rel,
                            model,
                            s,
                            true,
                            true,
                            consume,
                            inherited_plan.as_ref().map(|_| format!("inherited_baseline.as_ref().map(|baseline| &baseline.native_input_{id})")).as_deref(),
                            ctx,
                        )?;
                    } else {
                        writeln!(
                            f,
                            "let native_input_{id} = self.__native_input_{id}.{consume}::<true, true>({s});"
                        )?;
                    }
                    if stable {
                        end_stable_input(
                            f,
                            &format!("native_input_{id}"),
                            &format!("self.__native_input_{id}.current()"),
                            rel,
                            stratum.model,
                            ctx,
                        )?;
                    }
                }
                let required_indices: BTreeSet<_> = self.preparations[s]
                    .indices
                    .iter()
                    .cloned()
                    .map(|(rel, index)| input_key(rel, index))
                    .collect();
                for (rel, index) in &required_indices {
                    let consume = self.consume_method(s, rel, index);
                    if native_indices::find(self.native_indices, rel, index).is_some() {
                        continue;
                    }
                    if selection.is_primary(rel, index) {
                        continue;
                    }
                    let source = source_relation(rel);
                    let i = self.inputs[&source];
                    let j = self.indices[&input_key(rel.clone(), index.clone())];
                    let primary = selection.current_primary(&source);
                    let project = projection(rel, index, primary);
                    let stable = stratum.stable_inputs.contains(&source);
                    if self.old_indices.contains(&(rel.clone(), index.clone())) {
                        if stable {
                            begin_stable_input(f, &format!("index_{j}"), rel, ctx)?;
                        }
                        let old = self.preparations[s]
                            .indices
                            .contains(&(rel.clone(), index.clone()));
                        let new = self.preparations[s].indices.contains(&(
                            rel.clone(),
                            IndexSpec {
                                age: IndexAge::New,
                                order: index.order.clone(),
                            },
                        ));
                        writedoc! {f, "
                            let index_{j} = self.__rule_index_{j}.update(self.__rule_input_{i}.current(), {project});
                            self.__rule_index_{j}_versions.publish(&index_{j});
                        "}?;
                        if let Some(model) = stratum.model {
                            consume_scoped(
                                f,
                                &format!("__scope_index_{j}"),
                                &format!("&index_{j}"),
                                &format!("__rule_index_{j}_versions"),
                                &format!("index_{j}"),
                                rel,
                                model,
                                s,
                                old,
                                new,
                                consume,
                                inherited_plan.as_ref().map(|_| format!("inherited_baseline.as_ref().map(|baseline| &baseline.index_{j})")).as_deref(),
                                ctx,
                            )?;
                        } else {
                            writeln!(f, "let index_{j} = self.__rule_index_{j}_versions.{consume}::<{old}, {new}>(({s}, Vec::new()));")?;
                        }
                        if stable {
                            end_stable_input(
                                f,
                                &format!("index_{j}"),
                                &format!("self.__rule_index_{j}_versions.current()"),
                                rel,
                                stratum.model,
                                ctx,
                            )?;
                        }
                    } else {
                        // A delta-only reader does not need the full relation reordered.
                        if stable {
                            let typ = display_index_type(rel, ctx);
                            writeln!(f, "let index_{j} = if input_{i}.new.is_empty() {{ {typ}::new() }} else {{ self.__rule_index_{j}.update(&input_{i}.new, {project}) }};")?;
                        } else {
                            writeln!(f, "let index_{j} = self.__rule_index_{j}.update(&input_{i}.new, {project});")?;
                        }
                    }
                }
                for call in &evaluation.calls {
                    let m = call.module;
                    let module = &modules[m];
                    let env = display_module_env_struct_name(module);
                    let name = &module.name;
                    if inherited_plan.is_some() {
                        writeln!(f, "let matching_proofs_{m}: Vec<Vec<eqlog_runtime::__private::Table>> = matching_proofs.iter().map(|proof| {{ vec![")?;
                        for input in &call.inputs {
                            let field = input_name(input.storage);
                            writeln!(f, "{{ let rows = proof.{field}.clone();")?;
                            match input.proof_rows {
                                ProofRows::Direct => {}
                                ProofRows::RestrictOwner { suffix } => writeln!(f, "let rows = rows.get(owners[0]).cloned().unwrap_or_else(PrefixTree{suffix}::new);")?,
                                ProofRows::RestoreOwners { prefix, arity } => {
                                    for i in (0..prefix).rev() {
                                        let dim = arity - i;
                                        writeln!(f, "let rows = {{ let mut tree = PrefixTree{dim}::new(); tree.insert_restriction(owners[{i}], rows); tree }};")?;
                                    }
                                }
                            }
                            writeln!(f, "eqlog_runtime::__private::Table::from(rows) }},")?;
                        }
                        writeln!(f, "] }}).collect();")?;
                    }
                    writeln!(f, "let env = {env} {{ phantom: std::marker::PhantomData,")?;
                    if module.owner_count() > 0 {
                        if inherited_plan.is_some() {
                            writeln!(f, "__proofs: &matching_proofs_{m},")?;
                        } else {
                            writeln!(f, "__proofs: &[],")?;
                        }
                    }
                    if stratum.model.is_some() {
                        writeln!(f, "__owners: owners,")?;
                    }
                    for (&typ, source) in &call.canonical {
                        let name = display_type(typ, ctx).to_string().to_case(Case::Snake);
                        let roots = format!("self.{name}_equalities.canonical_roots()");
                        let roots = match source {
                            CanonicalInput::Global => roots,
                            CanonicalInput::CompactOwner => formatdoc! {"
                                match &self.__compact_members_{name} {{
                                    Some(spaces) => spaces.get_snapshot(owners[0])
                                        .map_or(eqlog_runtime::__private::CanonicalMask::Dense(&[]),
                                            eqlog_runtime::__private::CanonicalMask::Origins),
                                    None => eqlog_runtime::__private::CanonicalMask::Dense({roots}),
                                }}
                            "},
                            CanonicalInput::CompactMembers => formatdoc! {"
                                match &self.__compact_members_{name} {{
                                    Some(spaces) => eqlog_runtime::__private::CanonicalMask::Members(spaces),
                                    None => eqlog_runtime::__private::CanonicalMask::Dense({roots}),
                                }}
                            "},
                        };
                        writeln!(f, "__canonical_{name}: {roots},")?;
                    }
                    for input in &call.inputs {
                        let field = display_index_field_name(&input.rel, &input.index, ctx);
                        let storage = input_name(input.storage);
                        let version = input.version.map_or("", |age| match age {
                            IndexAge::Old => ".old",
                            IndexAge::New => ".new",
                            IndexAge::All => unreachable!("native rules read ages separately"),
                        });
                        writeln!(f, "{field}: &{storage}{version},")?;
                    }
                    for rel in module_env_out_rels(module) {
                        let field = display_out_set_field_name(&rel, ctx);
                        writeln!(f, "{field}: &mut delta.{field},")?;
                    }
                    writeln!(f, "}}; {name}(env);")?;
                }
                writeln!(f, "}}")?;
                for conversion in &evaluation.output_conversions {
                    let field = display_out_set_field_name(&conversion.output, ctx);
                    let suffix = if conversion.pending {
                        format!("[__compact_start_{field}..]")
                    } else {
                        String::new()
                    };
                    writeln!(f, "for args in &mut delta.{field}{suffix} {{")?;
                    for &(column, typ) in &conversion.columns {
                        let name = display_type(typ, ctx).to_string().to_case(Case::Snake);
                        writeln!(f, "args[{column}] = self.__compact_{name}_uid(owners[0], args[{column}]).0;")?;
                    }
                    writeln!(f, "}}")?;
                }
                let mut equalities = Vec::new();
                for output in outputs {
                    match output {
                        FlatOutRel::Equality(typ) => {
                            let name = display_type(*typ, ctx).to_string().to_case(Case::Snake);
                            writedoc! {f, "
                                for [lhs, rhs] in delta.new_{name}_equalities.drain(..) {{
                                    self.__equate_{name}(lhs.into(), rhs.into());
                                }}
                            "}?;
                            equalities.push(format!("!self.{name}_uprooted.is_empty()"));
                        }
                        FlatOutRel::Rel(_) | FlatOutRel::FuncDomain(_) => {}
                    }
                }
                if !equalities.is_empty() {
                    let changed = equalities.join(" || ");
                    writeln!(f, "if {changed} {{ self.__canonicalize_relations(); }}")?;
                }
                for output in outputs {
                    match output {
                        FlatOutRel::Rel(rel) => {
                            let field = display_out_set_field_name(output, ctx);
                            let insert = ctx.internal_insert_name(*rel);
                            let args = (0..rel.arity(ctx.signature()).len())
                                .map(|i| format!("arg{i}"))
                                .collect::<Vec<_>>();
                            let converted =
                                args.iter().map(|arg| format!("{arg}.into()")).join(", ");
                            let args = args.join(", ");
                            writedoc! {f, "
                                delta.{field}.sort_unstable();
                                delta.{field}.dedup();
                                for [{args}] in delta.{field}.drain(..) {{ self.{insert}({converted}); }}
                            "}?;
                        }
                        FlatOutRel::Equality(_) | FlatOutRel::FuncDomain(_) => {}
                    }
                }
                if stratum.model.is_none() && !compact_policy::models(ctx).is_empty() {
                    writeln!(f, "self.__prepare_total_member_policies();")?;
                }
                writeln!(f, "true }}")?;
            }
            for (&root, &m) in self.models {
                let plan = &self.model_preparations[&root];
                let baseline = self.transport_baseline(root);
                for &model in &plan.propagation.models {
                    let name = display_type(model, ctx).to_string().to_case(Case::Snake);
                    let count = ctx.signature().type_(model).parents.len();
                    let baseline_arg = if baseline.is_some() {
                        format!("baseline: &__TransportBaseline{m}, ")
                    } else {
                        String::new()
                    };
                    let compact_guard = super::compact_indices::component_guard(model, ctx);
                    writedoc! {f, "
                    fn __transport_component_{m}_{name}(&mut self, {baseline_arg}parents: [u32; {count}], morphisms: &[MorphismWithSignature], retain_own: bool) -> bool {{
                        if morphisms.is_empty() {{ return false; }}
                        {compact_guard}
                        let mut changed = false;
                "}?;
                    if let Some(baseline) = &baseline {
                        emit_transport_since_baseline(f, baseline, model, m, selection, ctx)?;
                    } else {
                        writeln!(f, "for morphism in morphisms {{ changed |= self.__propagate_{name}_morphism_model_{m}(parents, morphism, retain_own); }}")?;
                    }
                    for (rel, index) in &plan.support_indices {
                        write!(f, "{}", super::indices::prepare(rel, index, selection, ctx))?;
                    }
                    for id in &plan.native_indices {
                        let native = &self.native_indices[*id];
                        if native.from_primary {
                            continue;
                        }
                        if let Some(level) = native.models.iter().position(|&typ| typ == model) {
                            writedoc! {f, "
                            self.__extend_native_index_{id}();
                            let mut index = self.__native_input_{id}.current().clone();
                            for morphism in morphisms {{ changed |= self.__native_{id}_morphism_{level}(parents, morphism, &mut index, retain_own); }}
                            self.__native_input_{id}.publish(&index);
                        "}?;
                        }
                    }
                    writeln!(f, "changed }}")?;
                }
            }
            for (s, stratum) in self.strata.iter().enumerate() {
                let preparation = &self.preparations[s];
                let plans = std::iter::once((s.to_string(), &preparation.native)).chain(
                    preparation
                        .stable
                        .iter()
                        .map(|plan| (format!("stable_{s}"), plan)),
                );
                for (suffix, plan) in plans {
                    if plan.descendants.is_empty() {
                        continue;
                    }
                    let model = stratum
                        .model
                        .expect("descendant preparation needs a bound owner");
                    let count = ctx.signature().type_(model).parents.len() + 1;
                    writeln!(f, "fn __prepare_descendants_{suffix}(&mut self, owners: [u32; {count}], retain_own: bool) {{")?;
                    for &child in &plan.descendants {
                        let name = display_type(child, ctx).to_string().to_case(Case::Snake);
                        writeln!(
                            f,
                            "self.__propagate_{name}_morphisms_stratum_{suffix}(owners, retain_own);"
                        )?;
                    }
                    for (rel, index) in &plan.support_indices {
                        write!(f, "{}", super::indices::prepare(rel, index, selection, ctx))?;
                    }
                    for id in &plan.native_indices {
                        let native = &self.native_indices[*id];
                        if native.from_primary {
                            continue;
                        }
                        if native
                            .models
                            .get(count)
                            .is_some_and(|child| plan.descendants.contains(child))
                        {
                            writedoc! {f, "
                                self.__extend_native_index_{id}();
                                let mut index = self.__native_input_{id}.current().clone();
                                self.__native_{id}_model_{count}(owners, &mut index, retain_own);
                                self.__native_input_{id}.publish(&index);
                            "}?;
                        }
                    }
                    writeln!(f, "}}")?;
                }
            }
            writedoc! {f, "
                #[allow(unused_variables)]
                fn __refresh_model_consumers(&mut self) {{
                    if !self.__model_owners_changed {{ return; }}
                    self.__model_owners_changed = false;
            "}?;
            for (_, ids) in ctx
                .signature()
                .iter_model_decls()
                .filter(|(_, ids)| self.tracks_owner(ids.type_, ctx))
            {
                let name = display_type(ids.type_, ctx)
                    .to_string()
                    .to_case(Case::Snake);
                writeln!(
                    f,
                    "#[allow(unused_variables)] let merged_{name} = &self.__merged_{name};"
                )?;
            }
            writeln!(f, "let retain_consumer = |(stratum, owners): &(usize, Vec<u32>)| {{ match *stratum {{")?;
            for (s, stratum) in self.strata.iter().enumerate() {
                if let Some(model) = stratum.model {
                    let owners: Vec<_> = ctx
                        .signature()
                        .type_(model)
                        .parents
                        .iter()
                        .copied()
                        .chain(std::iter::once(model))
                        .collect();
                    let retain = retain_owners(&owners, ctx);
                    writeln!(f, "{s} => {retain},")?;
                }
            }
            writeln!(f, "_ => true, }} }};")?;
            for (s, stratum) in self.strata.iter().enumerate() {
                if let Some(model) = stratum.model {
                    let owners: Vec<_> = ctx
                        .signature()
                        .type_(model)
                        .parents
                        .iter()
                        .copied()
                        .chain(std::iter::once(model))
                        .collect();
                    let retain = retain_owners(&owners, ctx);
                    writeln!(f, "self.__owner_inputs_{s}.retain(|owners, _| {retain});")?;
                }
            }
            for (field, (owners, _)) in self.scoped_histories() {
                let retain = retain_owners(&owners, ctx);
                writedoc! {f, "
                    self.{field}.retain(|owners, history| {{
                        history.retain_consumers(&retain_consumer);
                        {retain}
                    }});
                "}?;
            }
            for i in self.inputs.values() {
                writeln!(
                    f,
                    "self.__rule_input_{i}.retain_consumers(&retain_consumer);"
                )?;
            }
            for ((rel, index), i) in self.indices {
                if self.old_indices.contains(&(rel.clone(), index.clone()))
                    && !selection.is_primary(rel, index)
                    && native_indices::find(self.native_indices, rel, index).is_none()
                {
                    writeln!(
                        f,
                        "self.__rule_index_{i}_versions.retain_consumers(&retain_consumer);"
                    )?;
                }
            }
            for (_, ids) in ctx
                .signature()
                .iter_model_decls()
                .filter(|(_, ids)| self.tracks_owner(ids.type_, ctx))
            {
                let name = display_type(ids.type_, ctx)
                    .to_string()
                    .to_case(Case::Snake);
                writeln!(f, "self.__merged_{name}.clear();")?;
            }
            writeln!(f, "}}")?;
            Ok(())
        })
    }

    pub fn close<'a>(
        &'a self,
        ctx: &'a RustGenCtx<'a>,
        selection: &'a IndexSelection,
    ) -> impl Display + 'a {
        FmtFn(move |f| {
            let (prepare_policy, complete_policy) = if compact_policy::models(ctx).is_empty() {
                ("", "")
            } else {
                (
                    "self.__prepare_total_member_policies();",
                    "self.__complete_total_members();",
                )
            };
            writedoc! {f, "
                /// Closes the model until the condition holds or all rules are satisfied.
                /// Depending on the axioms, this may run indefinitely.
                #[allow(dead_code)]
                pub fn close_until(&mut self, condition: impl Fn(&Self) -> bool) -> bool {{
                    self.__close_until(Some(&condition))
                }}

                fn __close_until(&mut self, condition: Option<&dyn Fn(&Self) -> bool>) -> bool {{
                    if self.__closed {{
                        return condition.is_some_and(|condition| condition(self));
                    }}
                    {prepare_policy}
                    self.__canonicalize_relations();
                    if self.__check_condition(condition) {{ return true; }}
                    let mut delta = std::mem::replace(&mut self.__pending_delta, ModelDelta::new());
                    loop {{
                        {prepare_policy}
            "}?;
            emit_schedule(f, self.body, self, ctx, selection)?;
            writedoc! {f, "
                        self.__allocated = false;
                        delta.apply_func_defs(self);
                        {complete_policy}
                        if !self.__allocated {{
                            std::mem::swap(&mut self.__pending_delta, &mut delta);
                            self.canonicalize();
                            self.__closed = true;
                            return false;
                        }}
                        self.__canonicalize_relations();
                    }}
                }}
            "}
        })
    }
}

fn retain_owners(owners: &[TypeId], ctx: &RustGenCtx<'_>) -> String {
    owners
        .iter()
        .enumerate()
        .map(|(i, &model)| {
            let name = display_type(model, ctx).to_string().to_case(Case::Snake);
            format!("!merged_{name}.contains(&owners[{i}])")
        })
        .join(" && ")
}

fn emit_transport_since_baseline(
    f: &mut std::fmt::Formatter<'_>,
    baseline: &TransportBaseline,
    model: TypeId,
    m: usize,
    selection: &IndexSelection,
    ctx: &RustGenCtx<'_>,
) -> std::fmt::Result {
    let name = display_type(model, ctx).to_string().to_case(Case::Snake);
    let mut unchanged = Vec::new();
    for (i, (rel, index)) in baseline.maps.iter().enumerate() {
        write!(f, "{}", super::indices::prepare(rel, index, selection, ctx))?;
        let read = super::indices::read_method(rel, index, selection, ctx, true);
        writeln!(f, "let same_map_{i} = eqlog_runtime::__private::SnapshotSet::shares_root(self.{read}(), &baseline.map_{i});")?;
        unchanged.push(format!("same_map_{i}"));
    }
    let sources: Vec<_> = baseline
        .relations
        .iter()
        .enumerate()
        .map(|(i, rel)| {
            let index = selection.current_primary(rel);
            let field = display_all_index_field_name(rel, index, ctx);
            let same = format!("eqlog_runtime::__private::SnapshotSet::shares_root(&self.{field}, &baseline.source_{i})");
            unchanged.push(same.clone());
            (field.to_string(), same)
        })
        .collect();
    let unchanged = if unchanged.is_empty() {
        "true".to_owned()
    } else {
        unchanged.join(" && ")
    };
    writeln!(
        f,
        "if baseline.work.iter().all(|work| work.is_empty()) && {unchanged} {{ return false; }}"
    )?;
    writeln!(f, "for morphism in morphisms {{")?;
    for (i, (rel, index)) in baseline.maps.iter().enumerate() {
        let read = super::indices::read_method(rel, index, selection, ctx, true);
        writedoc! {f, "
            let changed_map_{i} = !same_map_{i} && !eqlog_runtime::__private::SnapshotSet::shares_root(
                self.{read}().get(morphism.morph).unwrap_or_else(|| PrefixTree2::empty()),
                baseline.map_{i}.get(morphism.morph).unwrap_or_else(|| PrefixTree2::empty()),
            );
        "}?;
    }
    let mut active = Vec::new();
    for (i, rel) in baseline.relations.iter().enumerate() {
        let (field, same) = &sources[i];
        let dim = rel.arity(ctx.signature()).len() - 1;
        let mut changed = vec![format!("baseline.work[{i}].needs_visit(morphism)"), format!(
            "(!({same}) && !eqlog_runtime::__private::SnapshotSet::shares_root(self.{field}.get(morphism.dom).unwrap_or_else(|| PrefixTree{dim}::empty()), baseline.source_{i}.get(morphism.dom).unwrap_or_else(|| PrefixTree{dim}::empty())))"
        )];
        changed.extend(
            baseline.relation_maps[i]
                .iter()
                .map(|j| format!("changed_map_{j}")),
        );
        active.push(changed.join(" || "));
    }
    let count = baseline.relations.len();
    let active = active.join(", ");
    writedoc! {f, "
        let active = [{active}];
        if active.iter().any(|&active| active) {{
            changed |= self.__propagate_{name}_morphism_selected_model_{m}(
                parents, morphism, retain_own, &active, &mut [false; {count}],
            );
        }}
    }}
    "}
}

fn begin_stable_input(
    f: &mut std::fmt::Formatter<'_>,
    name: &str,
    rel: &FlatInRel,
    ctx: &RustGenCtx<'_>,
) -> std::fmt::Result {
    let typ = display_index_type(rel, ctx);
    writedoc! {f, "
        let {name} = if let Some(current) = &stable.{name} {{
            eqlog_runtime::__private::RelationView {{ old: current.clone(), new: {typ}::new() }}
        }} else {{
    "}
}

fn end_stable_input(
    f: &mut std::fmt::Formatter<'_>,
    name: &str,
    source: &str,
    rel: &FlatInRel,
    model: Option<TypeId>,
    ctx: &RustGenCtx<'_>,
) -> std::fmt::Result {
    let prefix = model.map_or(0, |model| scope_prefix(rel, model, ctx));
    let arity = rel.arity(ctx.signature()).len();
    let current = model.map_or_else(
        || source.to_owned(),
        |model| scoped_tree(source, rel, model, ctx),
    );
    writeln!(f, "let full = ({current}).clone();")?;
    for i in (0..prefix).rev() {
        let dim = arity - i;
        writeln!(f, "let full = {{ let mut tree = PrefixTree{dim}::new(); tree.insert_restriction(owners[{i}], full); tree }};")?;
    }
    writeln!(f, "stable.{name} = Some(full); {name} }};")
}

fn scope_prefix(rel: &FlatInRel, model: TypeId, ctx: &RustGenCtx<'_>) -> usize {
    crate::ram::scope_prefix(rel, model, ctx.signature())
}

fn scoped_tree(source: &str, rel: &FlatInRel, model: TypeId, ctx: &RustGenCtx<'_>) -> String {
    let arity = rel.arity(ctx.signature()).len();
    if scope_prefix(rel, model, ctx) == 0 {
        return source.to_owned();
    }
    let mut current = format!("({source})");
    for i in 0..scope_prefix(rel, model, ctx) {
        let dim = arity - i - 1;
        current = format!("{current}.get(owners[{i}]).unwrap_or_else(|| PrefixTree{dim}::empty())");
    }
    match rel {
        FlatInRel::Rel(FlatRel::ModelMember(typ)) => {
            if ctx.supports_compact_members(*typ)
                && ctx.signature().type_(*typ).parents.as_slice() == [model]
            {
                let name = display_type(*typ, ctx).to_string().to_case(Case::Snake);
                return format!("if self.__compact_members_{name}.is_some() {{ self.__compact_domain_{name}.get(owners[0]).unwrap_or_else(|| PrefixTree1::empty()) }} else {{ {current} }}");
            }
        }
        FlatInRel::Rel(FlatRel::Pred(_) | FlatRel::Func(_))
        | FlatInRel::RelWithDiagonals { .. }
        | FlatInRel::TypeSet(_)
        | FlatInRel::Equality(_) => {}
    }
    current
}

fn consume_scoped(
    f: &mut std::fmt::Formatter<'_>,
    field: &str,
    source: &str,
    global: &str,
    name: &str,
    rel: &FlatInRel,
    model: TypeId,
    stratum: usize,
    old: bool,
    new: bool,
    consume: &str,
    inherited: Option<&str>,
    ctx: &RustGenCtx<'_>,
) -> std::fmt::Result {
    let arity = rel.arity(ctx.signature()).len();
    let prefix = scope_prefix(rel, model, ctx);
    if prefix == 0 {
        if let Some(inherited) = inherited {
            let suffix = consume.strip_prefix("consume_").unwrap();
            return writedoc! {f, "
                let {name} = if let Some(baseline) = {inherited} {{
                    self.{global}.consume_inherited_{suffix}::<{old}, {new}>(({stratum}, owners.to_vec()), baseline)
                }} else {{
                    self.{global}.{consume}::<{old}, {new}>(({stratum}, owners.to_vec()))
                }};
            "};
        }
        return writeln!(
            f,
            "let {name} = self.{global}.{consume}::<{old}, {new}>(({stratum}, owners.to_vec()));"
        );
    }
    let field = format!("{field}_{prefix}");
    let key = (0..prefix).map(|i| format!("owners[{i}]")).join(", ");
    let current = scoped_tree(source, rel, model, ctx);
    writedoc! {f, "
        let {name} = {{
            let current = {current};
            let history = self.{field}.entry([{key}]).or_insert_with(eqlog_runtime::__private::RelationVersions::new);
            history.publish(current);
    "}?;
    if let Some(inherited) = inherited {
        let suffix = consume.strip_prefix("consume_").unwrap();
        writedoc! {f, "
            let view = if let Some(baseline) = {inherited} {{
                history.consume_inherited_{suffix}::<{old}, {new}>(({stratum}, owners.to_vec()), baseline)
            }} else {{
                history.{consume}::<{old}, {new}>(({stratum}, owners.to_vec()))
            }};
        "}?;
    } else {
        writeln!(
            f,
            "let view = history.{consume}::<{old}, {new}>(({stratum}, owners.to_vec()));"
        )?;
    }
    for age in ["old", "new"] {
        writeln!(f, "let {age} = view.{age};")?;
        for i in (0..prefix).rev() {
            let dim = arity - i;
            writeln!(f, "let {age} = {{ let mut tree = PrefixTree{dim}::new(); tree.insert_restriction(owners[{i}], {age}); tree }};")?;
        }
    }
    writedoc! {f, "
            eqlog_runtime::__private::RelationView {{ old, new }}
        }};
    "}
}

fn retained_owners(retain: RetainedOwners) -> String {
    match retain {
        RetainedOwners::None => "false".to_owned(),
        RetainedOwners::Always => "true".to_owned(),
        RetainedOwners::Component(id) => format!("retain_component_{id}"),
    }
}

fn emit_schedule(
    f: &mut std::fmt::Formatter<'_>,
    body: &[EvaluationStmt],
    codegen: &Codegen<'_>,
    ctx: &RustGenCtx<'_>,
    selection: &IndexSelection,
) -> std::fmt::Result {
    for stmt in body {
        match stmt {
            EvaluationStmt::Block(body) => {
                writeln!(f, "{{")?;
                emit_schedule(f, body, codegen, ctx, selection)?;
                writeln!(f, "}}")?;
            }
            EvaluationStmt::Loop(body) => {
                writeln!(f, "loop {{")?;
                emit_schedule(f, body, codegen, ctx, selection)?;
                writeln!(f, "}}")?;
            }
            EvaluationStmt::ForEach { iteration, body } => {
                match iteration {
                    EvaluationIteration::Components => {
                        writeln!(f, "for component in components.iter() {{")?
                    }
                    EvaluationIteration::ComponentObjects => {
                        writeln!(f, "for &object in &component.objects {{")?
                    }
                    EvaluationIteration::IncomingObjects => {
                        writeln!(f, "for object in &component.objects {{")?
                    }
                }
                emit_schedule(f, body, codegen, ctx, selection)?;
                writeln!(f, "}}")?;
            }
            EvaluationStmt::When { condition, body } => {
                match condition {
                    EvaluationCondition::StratumChanged {
                        stratum,
                        scoped,
                        stable,
                        retain,
                    } => {
                        let stable = if *stable {
                            format!("&mut stable_{stratum}, ")
                        } else {
                            String::new()
                        };
                        let retain = retain.map_or_else(String::new, |retain| {
                            format!("{}, ", retained_owners(retain))
                        });
                        if *scoped {
                            writeln!(f, "if self.__run_stratum_{stratum}_at(owners, {retain}{stable}&mut delta) {{")?;
                        } else {
                            writeln!(f, "if self.__run_stratum_{stratum}({stable}&mut delta) {{")?;
                        }
                    }
                    EvaluationCondition::IncomingPresent => {
                        writeln!(f, "if let Some(incoming) = &compact_incoming {{")?
                    }
                    EvaluationCondition::IncomingForObject => {
                        writeln!(f, "if let Some(morphisms) = incoming.get(object) {{")?
                    }
                    EvaluationCondition::IncomingAbsent => {
                        writeln!(f, "if compact_incoming.is_none() {{")?
                    }
                }
                emit_schedule(f, body, codegen, ctx, selection)?;
                writeln!(f, "}}")?;
            }
            EvaluationStmt::AllocateStable(id) => {
                writeln!(f, "let mut stable_{id} = __StableInputs{id}::default();")?
            }
            EvaluationStmt::InitializeChanges(id) => writeln!(f, "let mut active_{id} = false;")?,
            EvaluationStmt::MarkChanged(id) => writeln!(f, "active_{id} = true;")?,
            EvaluationStmt::PropagateChanges { source, target } => {
                writeln!(f, "active_{target} |= active_{source};")?
            }
            EvaluationStmt::BreakUnlessChanged {
                id,
                require_internal,
            } => {
                let guard = if *require_internal {
                    "component.internal.is_empty() || "
                } else {
                    ""
                };
                writeln!(f, "if {guard}!active_{id} {{ break; }}")?;
            }
            EvaluationStmt::CheckCondition => {
                // Moving the delta at each exit grows debug stack frames with the number of strata.
                writedoc! {f, "
                    if self.__check_condition(condition) {{
                        std::mem::swap(&mut self.__pending_delta, &mut delta);
                        return true;
                    }}
                "}?;
            }
            EvaluationStmt::SetParents { from_owners } => {
                let value = if *from_owners { "owners" } else { "[]" };
                writeln!(f, "let parents = {value};")?;
            }
            EvaluationStmt::SetOwners { parent_count } => {
                let owners = (0..*parent_count)
                    .map(|i| format!("parents[{i}]"))
                    .chain(std::iter::once("object".to_owned()))
                    .join(", ");
                writeln!(f, "let owners = [{owners}];")?;
            }
            EvaluationStmt::RefreshConsumers => writeln!(f, "self.__refresh_model_consumers();")?,
            EvaluationStmt::RecomputeModelIndices(id) => {
                writeln!(f, "self.recompute_model_indices_model_{id}();")?
            }
            EvaluationStmt::PrepareIndex { rel, index } => {
                write!(f, "{}", super::indices::prepare(rel, index, selection, ctx))?
            }
            EvaluationStmt::PrepareNative(id) => {
                writeln!(f, "self.__prepare_native_index_{id}();")?
            }
            EvaluationStmt::CaptureBaseline { model } => {
                let id = codegen.models[model];
                let baseline = &codegen.evaluation.transport_baselines[model];
                writeln!(f, "let mut baseline_{id} = __TransportBaseline{id} {{ work: std::array::from_fn(|_| eqlog_runtime::__private::TransportWork::default()),")?;
                for (i, rel) in baseline.relations.iter().enumerate() {
                    let field =
                        display_all_index_field_name(rel, selection.current_primary(rel), ctx);
                    writeln!(f, "source_{i}: self.{field}.clone(),")?;
                }
                for (i, (rel, index)) in baseline.maps.iter().enumerate() {
                    let read = super::indices::read_method(rel, index, selection, ctx, true);
                    writeln!(f, "map_{i}: self.{read}().clone(),")?;
                }
                writeln!(f, "}};")?;
            }
            EvaluationStmt::ComputeComponents { model } => write!(
                f,
                "{}",
                display_morphism_components(*model, ctx, selection, true)
            )?,
            EvaluationStmt::StageFrontier {
                model,
                root,
                retain,
            } => {
                let id = codegen.models[root];
                let baseline = &codegen.evaluation.transport_baselines[root];
                let plan = &codegen.model_preparations[root];
                let relations = baseline.relations.iter().collect_vec();
                let retain = retained_owners(*retain);
                writeln!(f, "let retain_own = {retain};")?;
                write!(
                    f,
                    "{}",
                    super::transport::stage_frontier(
                        *model,
                        &relations,
                        &plan.propagation,
                        ctx,
                        selection
                    )
                )?;
                writeln!(f, "baseline_{id}.work = transport_work;")?;
            }
            EvaluationStmt::ComputeIncoming { model } => {
                let name = display_type(*model, ctx).to_string().to_case(Case::Snake);
                writeln!(
                    f,
                    "let compact_incoming = self.__compact_incoming_{name}(&components);"
                )?;
            }
            EvaluationStmt::DefineRetention { id, parent } => {
                let retain = retained_owners(*parent);
                writeln!(f, "#[allow(unused_variables)] let retain_component_{id} = {retain} || !component.internal.is_empty();")?;
            }
            EvaluationStmt::Transport {
                model,
                root,
                edges,
                retain,
                changed,
            } => {
                let id = codegen.models[root];
                let name = display_type(*model, ctx).to_string().to_case(Case::Snake);
                let baseline = if codegen.evaluation.transport_baselines.contains_key(root) {
                    format!("&baseline_{id}, ")
                } else {
                    String::new()
                };
                let edges = match edges {
                    TransportEdges::Incoming => "morphisms",
                    TransportEdges::Internal => "&component.internal",
                    TransportEdges::Outgoing => "&component.outgoing",
                };
                let retain = retained_owners(*retain);
                if let Some(id) = changed {
                    write!(f, "active_{id} |= ")?;
                }
                writeln!(
                    f,
                    "self.__transport_component_{id}_{name}({baseline}parents, {edges}, {retain});"
                )?;
            }
            EvaluationStmt::SaveFrontier { model, root } => {
                let baseline = &codegen.evaluation.transport_baselines[root];
                for (i, rel) in baseline.relations.iter().enumerate() {
                    let field = super::transport::field(rel, *model, ctx);
                    writeln!(f, "self.{field}_frontier.insert(parents, frontier_{i});")?;
                }
            }
        }
    }
    Ok(())
}

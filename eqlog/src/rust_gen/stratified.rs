use convert_case::{Case, Casing};
use itertools::Itertools;
use std::collections::{BTreeMap, BTreeSet};
use std::fmt::Display;

use indoc::{formatdoc, writedoc};

use super::compact_indices;
use super::indices::source_relation;
use super::native_indices;
use super::{
    display_all_index_field_name, display_index_field_name, display_index_type,
    display_module_env_struct_name, display_morphism_components, display_out_set_field_name,
    display_type, module_env_out_rels, RustGenCtx,
};
use crate::algebra::signature::TypeId;
use crate::flat_eqlog::{FlatInRel, FlatOutRel, IndexAge, IndexSelection, IndexSpec};
use crate::fmt_util::FmtFn;
use crate::ram::{
    BaselineRelation, CanonicalInput, Consumption, EvaluationCondition, EvaluationHelperCondition,
    EvaluationHelperStmt, EvaluationIteration, EvaluationLifecycle, EvaluationPlan, EvaluationStmt,
    IndexPreparation, InheritedEvidence, InheritedInput, InheritedInstruction, InheritedRows,
    InputProjection, InputRead, InputReadSource, InputStorage, NativeIndexPreparation,
    NativePreparation, NativeReadPreparation, ProofRows, RamFunction, RamProgram, RetainedOwners,
    ScopedInput, StratumEvaluation, StratumInstruction, TransportBaseline, TransportEdges,
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
                        let scope = &stratum.owner_inputs[&rel];
                        let arity = scope.arity - scope.prefix;
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

    fn emit_inherited(
        &self,
        f: &mut std::fmt::Formatter<'_>,
        body: &[InheritedInstruction],
        s: usize,
        ctx: &RustGenCtx<'_>,
    ) -> std::fmt::Result {
        let fields = self.inherited_plan(s).unwrap();
        for instruction in body {
            match instruction {
                InheritedInstruction::RequireTarget(model) => {
                    let name=display_type(*model,ctx).to_string().to_case(Case::Snake);
                    writeln!(f,"let indices = self.__compact_indices_{name}.as_ref()?; if !indices.has_owner(owners[0]) {{ return None; }}")?;
                }
                InheritedInstruction::LoadMemberInheritance(typ) => {
                    let name=display_type(*typ,ctx).to_string().to_case(Case::Snake);
                    writeln!(f,"let spaces_{name} = self.__compact_members_{name}.as_ref()?; let inputs_{name} = spaces_{name}.inherited_inputs(owners[0])?;")?;
                }
                InheritedInstruction::InitializeCandidates => writeln!(f,"let mut best: Option<(u64, usize)> = None; let mut certified = Vec::new();")?,
                InheritedInstruction::ForCandidates(body) => {
                    writeln!(f,"for (position, (source, revision, rows)) in indices.inherited_inputs(owners[0]).enumerate() {{")?;
                    self.emit_inherited(f,body,s,ctx)?;
                    writeln!(f,"}}")?;
                }
                InheritedInstruction::Candidate(body) => {
                    writeln!(f,"let candidate = (|| {{")?;
                    self.emit_inherited(f,body,s,ctx)?;
                    writeln!(f,"}})();")?;
                }
                InheritedInstruction::CheckSourceRevision => writeln!(f,"if indices.revision(source) != revision {{ return None; }}")?,
                InheritedInstruction::InitializeScore => writeln!(f,"let mut score = 0u64;")?,
                InheritedInstruction::LoadMemberSource(typ) => {
                    let name=display_type(*typ,ctx).to_string().to_case(Case::Snake);
                    writedoc! {f, "
                        let (member_source, revision_{name}, domain_{name}) = inputs_{name}.get(position)?;
                        if member_source != source {{ return None; }}
                        let source_{name} = spaces_{name}.get_snapshot(source)?;
                        if source_{name}.revision() != revision_{name} {{ return None; }}
                    "}?;
                }
                InheritedInstruction::AddMemberScore(typ) => {
                    let name=display_type(*typ,ctx).to_string().to_case(Case::Snake);
                    writedoc! {f, "
                        score = score.checked_add(u64::try_from(domain_{name}.len()).unwrap())
                            .expect(\"inherited matching score overflow\");
                    "}?;
                }
                InheritedInstruction::BuildRevision(types) => {
                    let revisions=types.iter().map(|&typ| { let name=display_type(typ,ctx).to_string().to_case(Case::Snake); format!("revision_{name}") }).join(", ");
                    writeln!(f,"let revision = (source, revision, [{revisions}]);")?;
                }
                InheritedInstruction::LoadSourceCheckpoint => writeln!(f,"let proved = self.__owner_inputs_{s}.get(&[source])?;")?,
                InheritedInstruction::LoadInputs => {
                    for (name,input) in &fields {
                        let arity=input.arity; let rows=self.inherited_rows(input,ctx);
                        writeln!(f,"let {name}: PrefixTree{arity} = {rows};")?;
                    }
                }
                InheritedInstruction::VerifyInput { input,evidence } => match evidence {
                    InheritedEvidence::OwnersPresent => writeln!(f,"if !input_{input}.contains([source]) || !input_{input}.contains([owners[0]]) {{ return None; }}")?,
                    InheritedEvidence::CheckpointRoot => writeln!(f,"if !eqlog_runtime::__private::SnapshotSet::shares_root(&input_{input}, &proved.input_{input}) {{ return None; }}")?,
                },
                InheritedInstruction::ReturnCandidate => {
                    let names=fields.keys().join(", ");
                    writeln!(f,"Some((score, __InheritedInputs{s} {{ revision, {names} }}))")?;
                }
                InheritedInstruction::SkipUncertified => writeln!(f,"let Some((score, candidate)) = candidate else {{ continue; }};")?,
                InheritedInstruction::ChooseLargest => writedoc! {f, "
                    if best.as_ref().is_none_or(|(previous, _)| score > *previous) {{
                        best = Some((score, certified.len()));
                    }}
                "}?,
                InheritedInstruction::SaveCandidate => writeln!(f,"certified.push(candidate);")?,
                InheritedInstruction::RequireBest => writeln!(f,"let (_, best) = best?;")?,
                InheritedInstruction::LoadPreviousTarget => writeln!(f,"let previous = self.__owner_inputs_{s}.get(&owners)?;")?,
                InheritedInstruction::SelectChangedBaseline => writedoc! {f, "
                    let baseline = (previous.inherited != Some(certified[best].revision))
                        .then(|| certified[best].clone());
                "}?,
                InheritedInstruction::RetainUnseenProofs => writedoc! {f, "
                    certified.retain(|proof| {{
                        let (source, revision, members) = proof.revision;
                        previous.inherited_seen.get(&source) != Some(&(revision, members))
                    }});
                "}?,
                InheritedInstruction::ReturnProofs => writeln!(f,"Some((baseline, certified))")?,
            }
        }
        Ok(())
    }

    fn emit_stratum(
        &self,
        f: &mut std::fmt::Formatter<'_>,
        body: &[StratumInstruction],
        s: usize,
        modules: &[RamFunction],
        ctx: &RustGenCtx<'_>,
        selection: &IndexSelection,
    ) -> std::fmt::Result {
        let evaluation = &self.evaluation.strata[s];
        let stratum = evaluation;
        let inputs = &evaluation.inputs;
        let inherited_plan = self.inherited_plan(s);
        for instruction in body {
            match instruction {
                StratumInstruction::InitializeDirty => writeln!(
                    f,
                    "#[allow(unused_mut)] let mut dirty = !self.__stratum_initialized[{s}];"
                )?,
                StratumInstruction::RecordPendingOutput(output) => {
                    let field = display_out_set_field_name(output, ctx);
                    writeln!(f, "let __compact_start_{field} = delta.{field}.len();")?;
                }
                StratumInstruction::WhenUnpropagated(body) => {
                    writeln!(f, "if !stable.propagated {{")?;
                    self.emit_stratum(f, body, s, modules, ctx, selection)?;
                    writeln!(f, "}}")?;
                }
                StratumInstruction::MarkPropagated => writeln!(f, "stable.propagated = true;")?,
                StratumInstruction::PrepareDescendants { stable } => {
                    let suffix = if *stable { "_stable" } else { "" };
                    writeln!(
                        f,
                        "self.__prepare_descendants{suffix}_{s}(owners, retain_own);"
                    )?;
                }
                StratumInstruction::RecomputeIndices { stable } => {
                    let suffix = if *stable { "_stable" } else { "" };
                    writeln!(f, "self.recompute_model_indices_stratum{suffix}_{s}();")?;
                }
                StratumInstruction::PrepareIndex { rel, index } => {
                    write!(f, "{}", super::indices::prepare(rel, index, selection, ctx))?
                }
                StratumInstruction::OwnerCheckpoint => {
                    // Most owners have no new input on an incremental visit.
                    // Comparing roots avoids constructing their consumer views.
                    let mut unchanged = vec!["true".to_owned()];
                    let mut snapshots = Vec::new();
                    for rel in inputs {
                        let i = self.inputs[rel];
                        let field =
                            display_all_index_field_name(rel, selection.current_primary(rel), ctx);
                        let source = scoped_tree(
                            &format!("&self.{field}"),
                            &evaluation.owner_inputs[rel],
                            ctx,
                        );
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
                }
                StratumInstruction::PossibleInputGuard => {
                    let possible = evaluation.possible_inputs.as_ref().unwrap();
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
                StratumInstruction::LoadInheritedInputs => writedoc! {f, "
                    let (inherited_baseline, mut matching_proofs) = if delta.has_pending_func_defs() {{
                        (None, Vec::new())
                    }} else {{ self.__inherited_inputs_{s}(owners).unwrap_or_default() }};
                "}?,
                StratumInstruction::RecordInheritedProofs => writedoc! {f, "
                    if !matching_proofs.is_empty() {{
                        let seen = &mut self.__owner_inputs_{s}.get_mut(&owners).unwrap().inherited_seen;
                        let seen = std::rc::Rc::make_mut(seen);
                        for proof in &matching_proofs {{
                            let (source, revision, members) = proof.revision;
                            seen.insert(source, (revision, members));
                        }}
                    }}
                "}?,
                StratumInstruction::WhenInheritedBaseline(body) => {
                    writeln!(f,"if let Some(baseline) = &inherited_baseline {{")?;
                    self.emit_stratum(f,body,s,modules,ctx,selection)?;
                    writeln!(f,"}}")?;
                }
                StratumInstruction::SaveInheritedRevision => writeln!(f,"self.__owner_inputs_{s}.get_mut(&owners).unwrap().inherited = Some(baseline.revision);")?,
                StratumInstruction::RemoveBaselineProof => writeln!(f,"matching_proofs.retain(|proof| proof.revision != baseline.revision);")?,
                StratumInstruction::RetainPreviousProof => writeln!(f,"if let Some(previous) = previous_matching_proof {{ matching_proofs.push(previous); }}")?,
                StratumInstruction::MarkDirty => writeln!(f,"dirty = true;")?,
                StratumInstruction::ResetStable => writeln!(f,"*stable = __StableInputs{s}::default();")?,
                StratumInstruction::ReadInput(read) => emit_input_read(f, read, s, ctx)?,
                StratumInstruction::ReturnUnlessDirty => {
                    writeln!(f, "if !dirty {{ return false; }}")?
                }
                StratumInstruction::MarkInitialized => {
                    writeln!(f, "self.__stratum_initialized[{s}] = true;")?
                }
                StratumInstruction::Block(body) => {
                    writeln!(f, "{{")?;
                    self.emit_stratum(f, body, s, modules, ctx, selection)?;
                    writeln!(f, "}}")?;
                }
                StratumInstruction::Call(id) => {
                    let call = &evaluation.calls[*id];
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
                StratumInstruction::ConvertOutput(id) => {
                    let conversion = &evaluation.output_conversions[*id];
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
                StratumInstruction::ApplyEqualities(typ) => {
                    let name = display_type(*typ, ctx).to_string().to_case(Case::Snake);
                    writedoc! {f, "
                        for [lhs, rhs] in delta.new_{name}_equalities.drain(..) {{
                            self.__equate_{name}(lhs.into(), rhs.into());
                        }}
                    "}?;
                }
                StratumInstruction::CanonicalizeEqualities(types) => {
                    let changed = types
                        .iter()
                        .map(|&typ| {
                            let name = display_type(typ, ctx).to_string().to_case(Case::Snake);
                            format!("!self.{name}_uprooted.is_empty()")
                        })
                        .join(" || ");
                    writeln!(f, "if {changed} {{ self.__canonicalize_relations(); }}")?;
                }
                StratumInstruction::Insert(rel) => {
                    let output = FlatOutRel::Rel(*rel);
                    let field = display_out_set_field_name(&output, ctx);
                    let insert = ctx.internal_insert_name(*rel);
                    let args = (0..rel.arity(ctx.signature()).len())
                        .map(|i| format!("arg{i}"))
                        .collect::<Vec<_>>();
                    let converted = args.iter().map(|arg| format!("{arg}.into()")).join(", ");
                    let args = args.join(", ");
                    writedoc! {f, "
                        delta.{field}.sort_unstable();
                        delta.{field}.dedup();
                        for [{args}] in delta.{field}.drain(..) {{ self.{insert}({converted}); }}
                    "}?;
                }
                StratumInstruction::PreparePolicies => {
                    writeln!(f, "self.__prepare_total_member_policies();")?
                }
                StratumInstruction::ReturnChanged => writeln!(f, "true")?,
            }
        }
        Ok(())
    }

    pub fn methods<'a>(
        &'a self,
        modules: &'a [RamFunction],
        ctx: &'a RustGenCtx<'a>,
        selection: &'a IndexSelection,
    ) -> impl Display + 'a {
        FmtFn(move |f| {
            for (s, stratum) in self.strata.iter().enumerate() {
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
                    writeln!(f,"fn __inherited_inputs_{s}(&self, owners: [u32; 1]) -> Option<(Option<__InheritedInputs{s}>, Vec<__InheritedInputs{s}>)> {{")?;
                    self.emit_inherited(f, &stratum.inheritance, s, ctx)?;
                    writeln!(f, "}}")?;
                }
                let evaluation = &self.evaluation.strata[s];
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
                    "}?;
                }
                self.emit_stratum(f, &evaluation.body, s, modules, ctx, selection)?;
                writeln!(f, "}}")?;
            }
            for helper in &self.evaluation.component_helpers {
                let m = helper.root;
                let name = display_type(helper.model, ctx)
                    .to_string()
                    .to_case(Case::Snake);
                let count = helper.parents;
                let baseline_arg = if helper.baseline {
                    format!("baseline: &__TransportBaseline{m}, ")
                } else {
                    String::new()
                };
                writeln!(f,"fn __transport_component_{m}_{name}(&mut self, {baseline_arg}parents: [u32; {count}], morphisms: &[MorphismWithSignature], retain_own: bool) -> bool {{")?;
                emit_helper(f, &helper.body, ctx, selection)?;
                writeln!(f, "}}")?;
            }
            for helper in &self.evaluation.descendant_helpers {
                let stable = if helper.stable { "stable_" } else { "" };
                let stratum = helper.stratum;
                let count = helper.owners;
                writeln!(f,"fn __prepare_descendants_{stable}{stratum}(&mut self, owners: [u32; {count}], retain_own: bool) {{")?;
                emit_helper(f, &helper.body, ctx, selection)?;
                writeln!(f, "}}")?;
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
            writedoc! {f, "
                /// Closes the model until the condition holds or all rules are satisfied.
                /// Depending on the axioms, this may run indefinitely.
                #[allow(dead_code)]
                pub fn close_until(&mut self, condition: impl Fn(&Self) -> bool) -> bool {{
                    self.__close_until(Some(&condition))
                }}

                fn __close_until(&mut self, condition: Option<&dyn Fn(&Self) -> bool>) -> bool {{
            "}?;
            emit_schedule(f, self.body, self, ctx, selection)?;
            writeln!(f, "}}")
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

fn baseline_relation_fields(relation: &BaselineRelation, ctx: &RustGenCtx<'_>) -> (String, String) {
    let id = relation.id;
    let field = display_all_index_field_name(&relation.rel, &relation.index, ctx).to_string();
    let unchanged = format!(
        "eqlog_runtime::__private::SnapshotSet::shares_root(&self.{field}, &baseline.source_{id})"
    );
    (field, unchanged)
}

fn emit_helper(
    f: &mut std::fmt::Formatter<'_>,
    body: &[EvaluationHelperStmt],
    ctx: &RustGenCtx<'_>,
    selection: &IndexSelection,
) -> std::fmt::Result {
    for instruction in body {
        match instruction {
            EvaluationHelperStmt::When { condition, body } => {
                let condition = match condition {
                    EvaluationHelperCondition::NoMorphisms => "morphisms.is_empty()".to_owned(),
                    EvaluationHelperCondition::AnyActive => "active.iter().any(|&active| active)".to_owned(),
                    EvaluationHelperCondition::BaselineUnchanged { maps, relations } => {
                        let unchanged: Vec<_> = (0..*maps).map(|id| format!("same_map_{id}")).chain(relations.iter().map(|relation| baseline_relation_fields(relation,ctx).1)).collect();
                        let unchanged = if unchanged.is_empty() { "true".to_owned() } else { unchanged.join(" && ") };
                        format!("baseline.work.iter().all(|work| work.is_empty()) && {unchanged}")
                    }
                };
                writeln!(f,"if {condition} {{")?;
                emit_helper(f,body,ctx,selection)?;
                writeln!(f,"}}")?;
            }
            EvaluationHelperStmt::ForMorphisms(body) => {
                writeln!(f,"for morphism in morphisms {{")?;
                emit_helper(f,body,ctx,selection)?;
                writeln!(f,"}}")?;
            }
            EvaluationHelperStmt::ReturnFalse => writeln!(f,"return false;")?,
            EvaluationHelperStmt::CompactComponent(model) => write!(f,"{}",compact_indices::component_guard(*model,ctx))?,
            EvaluationHelperStmt::InitializeChanged => writeln!(f,"let mut changed = false;")?,
            EvaluationHelperStmt::PrepareIndex { rel,index } => write!(f,"{}",super::indices::prepare(rel,index,selection,ctx))?,
            EvaluationHelperStmt::CompareBaselineMap { id,rel,index } => {
                let read=super::indices::read_method(rel,index,selection,ctx,true);
                writeln!(f,"let same_map_{id} = eqlog_runtime::__private::SnapshotSet::shares_root(self.{read}(), &baseline.map_{id});")?;
            }
            EvaluationHelperStmt::CompareMorphismMap { id,rel,index } => {
                let read=super::indices::read_method(rel,index,selection,ctx,true);
                writedoc! {f, "
                    let changed_map_{id} = !same_map_{id} && !eqlog_runtime::__private::SnapshotSet::shares_root(
                        self.{read}().get(morphism.morph).unwrap_or_else(|| PrefixTree2::empty()),
                        baseline.map_{id}.get(morphism.morph).unwrap_or_else(|| PrefixTree2::empty()),
                    );
                "}?;
            }
            EvaluationHelperStmt::ComputeActive(relations) => {
                let active=relations.iter().map(|relation| {
                    let id=relation.id; let dim=relation.suffix;
                    let (field,same)=baseline_relation_fields(relation,ctx);
                    let mut changed=vec![format!("baseline.work[{id}].needs_visit(morphism)"),format!("(!({same}) && !eqlog_runtime::__private::SnapshotSet::shares_root(self.{field}.get(morphism.dom).unwrap_or_else(|| PrefixTree{dim}::empty()), baseline.source_{id}.get(morphism.dom).unwrap_or_else(|| PrefixTree{dim}::empty())))")];
                    changed.extend(relation.maps.iter().map(|id|format!("changed_map_{id}")));
                    changed.join(" || ")
                }).join(", ");
                writeln!(f,"let active = [{active}];")?;
            }
            EvaluationHelperStmt::PropagateMorphism { root,model,selected } => {
                let name=display_type(*model,ctx).to_string().to_case(Case::Snake);
                if let Some(count)=selected {
                    writeln!(f,"changed |= self.__propagate_{name}_morphism_selected_model_{root}(parents, morphism, retain_own, &active, &mut [false; {count}]);")?;
                } else { writeln!(f,"changed |= self.__propagate_{name}_morphism_model_{root}(parents, morphism, retain_own);")?; }
            }
            EvaluationHelperStmt::ExtendNative(id) => writeln!(f,"self.__extend_native_index_{id}();")?,
            EvaluationHelperStmt::ReadNative(id) => writeln!(f,"let mut index = self.__native_input_{id}.current().clone();")?,
            EvaluationHelperStmt::NativeMorphism { id,level } => writeln!(f,"changed |= self.__native_{id}_morphism_{level}(parents, morphism, &mut index, retain_own);")?,
            EvaluationHelperStmt::PublishNative(id) => writeln!(f,"self.__native_input_{id}.publish(&index);")?,
            EvaluationHelperStmt::PropagateDescendant { model,stratum,stable } => {
                let name=display_type(*model,ctx).to_string().to_case(Case::Snake);
                let stable=if *stable { "stable_" } else { "" };
                writeln!(f,"self.__propagate_{name}_morphisms_stratum_{stable}{stratum}(owners, retain_own);")?;
            }
            EvaluationHelperStmt::NativeModel { id,level } => writeln!(f,"self.__native_{id}_model_{level}(owners, &mut index, retain_own);")?,
            EvaluationHelperStmt::ReturnChanged => writeln!(f,"changed")?,
        }
    }
    Ok(())
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
    scope: Option<&ScopedInput>,
    ctx: &RustGenCtx<'_>,
) -> std::fmt::Result {
    let prefix = scope.map_or(0, |scope| scope.prefix);
    let arity = rel.arity(ctx.signature()).len();
    let current = scope.map_or_else(
        || source.to_owned(),
        |scope| scoped_tree(source, scope, ctx),
    );
    writeln!(f, "let full = ({current}).clone();")?;
    for i in (0..prefix).rev() {
        let dim = arity - i;
        writeln!(f, "let full = {{ let mut tree = PrefixTree{dim}::new(); tree.insert_restriction(owners[{i}], full); tree }};")?;
    }
    writeln!(f, "stable.{name} = Some(full); {name} }};")
}

fn scoped_tree(source: &str, scope: &ScopedInput, ctx: &RustGenCtx<'_>) -> String {
    if scope.prefix == 0 {
        return source.to_owned();
    }
    let mut current = format!("({source})");
    for i in 0..scope.prefix {
        let dim = scope.arity - i - 1;
        current = format!("{current}.get(owners[{i}]).unwrap_or_else(|| PrefixTree{dim}::empty())");
    }
    if let Some(typ) = scope.compact_domain {
        let name = display_type(typ, ctx).to_string().to_case(Case::Snake);
        return format!("if self.__compact_members_{name}.is_some() {{ self.__compact_domain_{name}.get(owners[0]).unwrap_or_else(|| PrefixTree1::empty()) }} else {{ {current} }}");
    }
    current
}

fn consume_scoped(
    f: &mut std::fmt::Formatter<'_>,
    field: &str,
    source: &str,
    global: &str,
    name: &str,
    scope: &ScopedInput,
    stratum: usize,
    old: bool,
    new: bool,
    consume: &str,
    inherited: Option<&str>,
    ctx: &RustGenCtx<'_>,
) -> std::fmt::Result {
    let arity = scope.arity;
    let prefix = scope.prefix;
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
    let current = scoped_tree(source, scope, ctx);
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

fn display_projection(plan: &InputProjection) -> String {
    let row = plan.source.iter().map(|i| format!("el{i}")).join(", ");
    let result = plan.target.iter().map(|i| format!("el{i}")).join(", ");
    let checks = plan
        .equalities
        .iter()
        .map(|(i, j)| format!("el{i} == el{j}"))
        .join(" && ");
    if checks.is_empty() {
        format!("|[{row}]| Some([{result}])")
    } else {
        format!("|[{row}]| ({checks}).then_some([{result}])")
    }
}

fn emit_input_read(
    f: &mut std::fmt::Formatter<'_>,
    read: &InputRead,
    s: usize,
    ctx: &RustGenCtx<'_>,
) -> std::fmt::Result {
    let name = input_name(read.storage);
    let consume = match read.consumption {
        Consumption::Membership => "consume_membership",
        Consumption::Required => "consume_required",
    };
    let old = read.old;
    let new = read.new;
    let inherited = read
        .inherited
        .then(|| format!("inherited_baseline.as_ref().map(|baseline| &baseline.{name})"));
    let (global, scoped) = match read.storage {
        InputStorage::Relation(id) => (format!("__rule_input_{id}"), format!("__scope_input_{id}")),
        InputStorage::Index(id) => (
            format!("__rule_index_{id}_versions"),
            format!("__scope_index_{id}"),
        ),
        InputStorage::Native(id) => (
            format!("__native_input_{id}"),
            format!("__scope_native_{id}"),
        ),
    };
    match &read.source {
        InputReadSource::Relation { diagonal } => {
            let stable_global = read.stable && read.scope.is_none();
            if read.stable && !stable_global {
                begin_stable_input(f, &name, &read.rel, ctx)?;
            }
            if stable_global {
                writeln!(f, "if let Some(current) = &stable.{name} {{ self.{global}.publish(current); }} else {{")?;
            }
            let current = display_all_index_field_name(&read.rel, &read.index, ctx);
            if *diagonal {
                let arity = read.index.order.len();
                let suffix = arity - 1;
                writedoc! {f, "
                    let filtered_{name} = {{
                        let mut filtered = PrefixTree{arity}::new();
                        for (key, rows) in self.{current}.map.iter() {{
                            if let Some(rows) = rows.get(key) {{
                                let mut suffix = PrefixTree{suffix}::new();
                                suffix.insert_restriction(key, rows.clone());
                                filtered.insert_restriction(key, suffix);
                            }}
                        }}
                        filtered
                    }};
                    self.{global}.publish(&filtered_{name});
                "}?;
            } else {
                writeln!(f, "self.{global}.publish(&self.{current});")?;
            }
            if stable_global {
                writeln!(f, "}}")?;
                begin_stable_input(f, &name, &read.rel, ctx)?;
            }
            if let Some(scope) = &read.scope {
                consume_scoped(
                    f,
                    &scoped,
                    &format!("self.{global}.current()"),
                    &global,
                    &name,
                    scope,
                    s,
                    old,
                    new,
                    consume,
                    inherited.as_deref(),
                    ctx,
                )?;
            } else {
                writeln!(
                    f,
                    "let {name} = self.{global}.{consume}::<{old}, {new}>(({s}, Vec::new()));"
                )?;
            }
            if read.stable {
                end_stable_input(
                    f,
                    &name,
                    &format!("self.{global}.current()"),
                    &read.rel,
                    read.scope.as_ref(),
                    ctx,
                )?;
            }
            writeln!(f, "dirty |= !{name}.new.is_empty();")?;
        }
        InputReadSource::Native(preparation) => {
            let id = match read.storage {
                InputStorage::Native(id) => id,
                InputStorage::Relation(_) | InputStorage::Index(_) => {
                    unreachable!("native reads use native storage")
                }
            };
            if read.stable {
                begin_stable_input(f, &name, &read.rel, ctx)?;
            }
            match preparation {
                NativeReadPreparation::Primary => {
                    writeln!(f, "self.__prepare_native_index_from_primary_{id}();")?
                }
                NativeReadPreparation::Extend => writeln!(f, "self.__extend_native_index_{id}();")?,
                NativeReadPreparation::Full => writeln!(f, "self.__prepare_native_index_{id}();")?,
            }
            if let Some(scope) = &read.scope {
                consume_scoped(
                    f,
                    &scoped,
                    &format!("self.{global}.current()"),
                    &global,
                    &name,
                    scope,
                    s,
                    old,
                    new,
                    consume,
                    inherited.as_deref(),
                    ctx,
                )?;
            } else {
                writeln!(
                    f,
                    "let {name} = self.{global}.{consume}::<{old}, {new}>({s});"
                )?;
            }
            if read.stable {
                end_stable_input(
                    f,
                    &name,
                    &format!("self.{global}.current()"),
                    &read.rel,
                    read.scope.as_ref(),
                    ctx,
                )?;
            }
        }
        InputReadSource::Projected {
            source,
            projection,
            history,
        } => {
            let id = match read.storage {
                InputStorage::Index(id) => id,
                InputStorage::Relation(_) | InputStorage::Native(_) => {
                    unreachable!("projected reads use index storage")
                }
            };
            let project = display_projection(projection);
            if *history {
                if read.stable {
                    begin_stable_input(f, &name, &read.rel, ctx)?;
                }
                writeln!(f,"let {name} = self.__rule_index_{id}.update(self.__rule_input_{source}.current(), {project});")?;
                writeln!(f, "self.{global}.publish(&{name});")?;
                if let Some(scope) = &read.scope {
                    consume_scoped(
                        f,
                        &scoped,
                        &format!("&{name}"),
                        &global,
                        &name,
                        scope,
                        s,
                        old,
                        new,
                        consume,
                        inherited.as_deref(),
                        ctx,
                    )?;
                } else {
                    writeln!(
                        f,
                        "let {name} = self.{global}.{consume}::<{old}, {new}>(({s}, Vec::new()));"
                    )?;
                }
                if read.stable {
                    end_stable_input(
                        f,
                        &name,
                        &format!("self.{global}.current()"),
                        &read.rel,
                        read.scope.as_ref(),
                        ctx,
                    )?;
                }
            } else if read.stable {
                let typ = display_index_type(&read.rel, ctx);
                writeln!(f,"let {name} = if input_{source}.new.is_empty() {{ {typ}::new() }} else {{ self.__rule_index_{id}.update(&input_{source}.new, {project}) }};")?;
            } else {
                writeln!(
                    f,
                    "let {name} = self.__rule_index_{id}.update(&input_{source}.new, {project});"
                )?;
            }
        }
    }
    Ok(())
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
            EvaluationStmt::Lifecycle(operation) => {
                let source = match operation {
                    EvaluationLifecycle::PreparePolicies => "self.__prepare_total_member_policies();",
                    EvaluationLifecycle::CompletePolicies => "self.__complete_total_members();",
                    EvaluationLifecycle::CanonicalizeRelations => "self.__canonicalize_relations();",
                    EvaluationLifecycle::TakeDelta => "let mut delta = std::mem::replace(&mut self.__pending_delta, ModelDelta::new());",
                    EvaluationLifecycle::ClearAllocated => "self.__allocated = false;",
                    EvaluationLifecycle::ApplyDeferredFunctions => "delta.apply_func_defs(self);",
                    EvaluationLifecycle::SaveDelta => "std::mem::swap(&mut self.__pending_delta, &mut delta);",
                    EvaluationLifecycle::Canonicalize => "self.canonicalize();",
                    EvaluationLifecycle::MarkClosed => "self.__closed = true;",
                    EvaluationLifecycle::ReturnFalse => "return false;",
                    EvaluationLifecycle::ReturnCondition => "return condition.is_some_and(|condition| condition(self));",
                    EvaluationLifecycle::CheckConditionBeforeDelta => "if self.__check_condition(condition) { return true; }",
                };
                writeln!(f, "{source}")?;
            }

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
                    EvaluationCondition::Closed => writeln!(f, "if self.__closed {{")?,
                    EvaluationCondition::NoAllocations => writeln!(f, "if !self.__allocated {{")?,

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

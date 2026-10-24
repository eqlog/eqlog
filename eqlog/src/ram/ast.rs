use crate::algebra::signature::TypeId;
use crate::flat_eqlog::{FlatInRel, FlatOutRel, FlatRel, FlatRule, IndexSpec};
use std::collections::{BTreeMap, BTreeSet};
use std::sync::Arc;

use super::{CompactPlan, EvaluationPlan, IndexedPlan, TransportPlan};

#[derive(Copy, Clone, PartialEq, Eq, Debug, Hash, PartialOrd, Ord)]
pub enum Strictness {
    Lazy,
    Strict,
}

#[derive(Clone, PartialEq, Eq, Debug, Hash, PartialOrd, Ord)]
pub struct SetVarName {
    pub stmt_index: usize,
    pub rel: FlatInRel,
    pub index: IndexSpec,
    pub restricted: usize,
}

#[derive(Clone, PartialEq, Eq, Debug, Hash, PartialOrd, Ord)]
pub struct SetVar {
    pub name: SetVarName,
    pub arity: usize,
    pub strictness: Strictness,
}

#[derive(Clone, PartialEq, Eq, Debug, Hash, PartialOrd, Ord)]
pub struct ElVar {
    pub name: Arc<str>,
}

#[derive(Clone, PartialEq, Eq, Debug, Hash, PartialOrd, Ord)]
pub struct GetIndexExpr {
    pub rel: FlatInRel,
    pub index_spec: IndexSpec,
}

#[derive(Clone, PartialEq, Eq, Debug, Hash, PartialOrd, Ord)]
pub struct RestrictExpr {
    pub set: SetVar,
    pub first_column_var: ElVar,
}

#[derive(Clone, PartialEq, Eq, Debug, Hash, PartialOrd, Ord)]
pub enum InSetExpr {
    GetIndex(GetIndexExpr),
    Restrict(RestrictExpr),
}

#[derive(Clone, PartialEq, Eq, Debug, Hash, PartialOrd, Ord)]
pub struct DefineSetStmt {
    pub defined_var: SetVar,
    pub expr: InSetExpr,
}

#[derive(Clone, PartialEq, Eq, Debug, Hash, PartialOrd, Ord)]
pub struct IterStmt {
    pub sets: Vec<SetVar>,
    pub lookup_drivers: Vec<SetVar>,
    pub loop_var_el: ElVar,
    pub loop_var_set: SetVar,
    pub first_only: bool,
    pub canonical_filter: bool,
}

#[derive(Clone, PartialEq, Eq, Debug, Hash, PartialOrd, Ord)]
pub struct InsertStmt {
    pub rel: FlatOutRel,
    pub args: Vec<ElVar>,
}

#[derive(Clone, PartialEq, Eq, Debug, Hash, PartialOrd, Ord)]
pub struct GuardInhabitedStmt {
    pub sets: Vec<SetVar>,
}

#[derive(Clone, PartialEq, Eq, Debug, Hash, PartialOrd, Ord)]
pub struct GuardPlanStmt {
    pub original: Vec<SetVar>,
    pub alternative: Vec<SetVar>,
    pub select_alternative: bool,
    pub probe_rows: bool,
}

#[derive(Clone, PartialEq, Eq, Debug, Hash, PartialOrd, Ord)]
pub enum QueryOp {
    DefineSet(DefineSetStmt),
    Iter(IterStmt),
    Insert(InsertStmt),
    GuardInhabited(GuardInhabitedStmt),
    GuardPlan(GuardPlanStmt),
}

#[derive(Clone, PartialEq, Eq, Debug, Hash, PartialOrd, Ord)]
pub struct QueryPlan {
    pub name: String,
    pub flat_rule: FlatRule,
    pub stmts: Vec<QueryOp>,
}

#[derive(Clone, PartialEq, Eq, Debug, Hash, PartialOrd, Ord)]
pub struct RamFunction {
    pub name: String,
    pub rules: Vec<RuleSource>,
    pub interface: FunctionInterface,
    pub body: RamBlock,
    pub procedures: Vec<RamProcedure>,
}

#[derive(Clone, PartialEq, Eq, Debug, Hash, PartialOrd, Ord)]
pub struct RuleSource {
    pub flat_rule: FlatRule,
    pub inputs: BTreeSet<(FlatInRel, IndexSpec)>,
}

impl RuleSource {
    pub fn input_indices(&self) -> BTreeSet<(FlatInRel, IndexSpec)> {
        self.inputs.clone()
    }
}

#[derive(Clone, PartialEq, Eq, Debug, Hash, PartialOrd, Ord, Default)]
pub struct FunctionInterface {
    pub inputs: BTreeSet<(FlatInRel, IndexSpec)>,
    pub outputs: BTreeSet<FlatOutRel>,
    pub canonical_types: BTreeSet<TypeId>,
    pub owners: Vec<TypeId>,
    pub matching_proofs: bool,
    pub proof_owner_prefix: bool,
}

pub type RamBlock = Vec<RamInstruction>;

#[derive(Clone, PartialEq, Eq, Debug, Hash, PartialOrd, Ord)]
pub enum RamCondition {
    Inhabited(GuardInhabitedStmt),
    Scalar(RamScalarExpr),
    Distinct(ElVar, ElVar),
    Absent { rel: FlatRel, args: Vec<ElVar> },
    Uncovered,
    NoProofs,
}

#[derive(Clone, PartialEq, Eq, Debug, Hash, PartialOrd, Ord)]
pub enum RamScalarVar {
    LoopSize(SetVar),
    LookupSelected(SetVar),
    PlanSize,
    PlanLookupCost,
    PlanBudget,
    PlanAlternative,
}

#[derive(Clone, Copy, PartialEq, Eq, Debug, Hash, PartialOrd, Ord)]
pub enum RamScalarOp {
    Add,
    SaturatingAdd,
    SaturatingMul,
    Divide,
    Max,
    GreaterThan,
    LessThan,
    LessEqual,
    Equal,
    And,
}

#[derive(Clone, PartialEq, Eq, Debug, Hash, PartialOrd, Ord)]
pub enum RamScalarExpr {
    Integer(usize),
    Boolean(bool),
    Variable(RamScalarVar),
    KeyCount(Vec<SetVar>),
    RowCount {
        sets: Vec<SetVar>,
        limit: Box<RamScalarExpr>,
    },
    Log2(Box<RamScalarExpr>),
    Binary {
        op: RamScalarOp,
        left: Box<RamScalarExpr>,
        right: Box<RamScalarExpr>,
    },
}

#[derive(Clone, PartialEq, Eq, Debug, Hash, PartialOrd, Ord)]
pub enum IterationStrategy {
    Direct,
    AdaptiveLookup(RamScalarVar),
    Oldest,
}

#[derive(Clone, PartialEq, Eq, Debug, Hash, PartialOrd, Ord)]
pub struct RamIteration {
    pub sets: Vec<SetVar>,
    pub lookup_drivers: Vec<SetVar>,
    pub loop_var_el: ElVar,
    pub loop_var_set: SetVar,
    pub strategy: IterationStrategy,
    pub canonical_type: Option<TypeId>,
    pub limit: Option<usize>,
}

#[derive(Clone, Copy, PartialEq, Eq, Debug, Hash, PartialOrd, Ord)]
pub enum ProofAccess {
    Consume,
    Borrow,
}

#[derive(Clone, PartialEq, Eq, Debug, Hash, PartialOrd, Ord)]
pub enum RamInstruction {
    DefineSet(DefineSetStmt),
    DefineScalar {
        variable: RamScalarVar,
        value: RamScalarExpr,
    },
    Insert(InsertStmt),
    ForEach {
        iteration: RamIteration,
        proof_variable: Option<usize>,
        body: RamBlock,
    },
    If {
        condition: RamCondition,
        then_body: RamBlock,
        else_body: RamBlock,
    },
    Scope(RamBlock),
    Call(usize),
    BeginProof(ProofPlan),
    PrepareProofKeys(usize),
    RestrictProof {
        variable: usize,
        value: ElVar,
        access: ProofAccess,
    },
}

#[derive(Clone, PartialEq, Eq, Debug, Hash, PartialOrd, Ord)]
pub struct RamProcedure {
    pub name: String,
    pub owners: Vec<ElVar>,
    pub rules: Vec<FlatRule>,
    pub body: RamBlock,
}

#[derive(Clone, PartialEq, Eq, Debug, Hash, PartialOrd, Ord)]
pub struct ProofAtom {
    pub inputs: Vec<usize>,
    pub columns: Vec<usize>,
}

#[derive(Clone, PartialEq, Eq, Debug, Hash, PartialOrd, Ord)]
pub struct ProofPlan {
    pub atoms: Vec<ProofAtom>,
    pub relevant: BTreeSet<usize>,
    pub owner_prefix: Option<ElVar>,
}

pub struct RamProgram {
    pub relation_weights: BTreeMap<FlatRel, usize>,
    pub transport: TransportPlan,
    pub compact: CompactPlan,
    pub evaluation: EvaluationPlan,
    pub indexed: Option<IndexedPlan>,
    pub functions: Vec<RamFunction>,
    pub preparations: Vec<IndexPreparation>,
    pub model_preparations: BTreeMap<TypeId, NativePreparation>,
    pub native_indices: Vec<NativeIndexPreparation>,
}

pub struct IndexPreparation {
    pub indices: BTreeSet<(FlatInRel, IndexSpec)>,
    pub membership_only: BTreeSet<(FlatInRel, IndexSpec)>,
    pub native: NativePreparation,
    pub stable: Option<NativePreparation>,
}

pub struct NativePreparation {
    pub native_indices: BTreeSet<usize>,
    pub support_indices: BTreeSet<(FlatInRel, IndexSpec)>,
    pub propagation: PropagationPlan,
    pub descendants: BTreeSet<TypeId>,
}

impl IndexPreparation {
    pub fn reads_descendants(&self) -> bool {
        !self.native.descendants.is_empty()
            || self
                .stable
                .as_ref()
                .is_some_and(|plan| !plan.descendants.is_empty())
    }

    pub fn native_indices(&self) -> impl Iterator<Item = &usize> {
        self.native
            .native_indices
            .iter()
            .chain(self.stable.iter().flat_map(|plan| &plan.native_indices))
    }
}

#[derive(Default)]
pub struct PropagationPlan {
    pub relations: BTreeSet<FlatRel>,
    pub models: BTreeSet<TypeId>,
    pub graph_indices: BTreeMap<TypeId, BTreeSet<(FlatInRel, IndexSpec)>>,
    pub map_indices: BTreeMap<(TypeId, FlatInRel), BTreeSet<(FlatInRel, IndexSpec)>>,
}

pub struct NativeIndexPreparation {
    pub from_primary: bool,
    pub rel: FlatInRel,
    pub index: IndexSpec,
    pub models: Vec<TypeId>,
    pub support_indices: BTreeSet<(FlatInRel, IndexSpec)>,
}

impl RamFunction {
    pub fn flat_rules(&self) -> impl Iterator<Item = &FlatRule> {
        self.rules.iter().map(|source| &source.flat_rule)
    }

    pub fn owner_count(&self) -> usize {
        self.interface.owners.len()
    }

    pub fn input_indices(&self) -> BTreeSet<(FlatInRel, IndexSpec)> {
        self.interface.inputs.clone()
    }
}

impl QueryPlan {
    pub fn input_indices(&self) -> BTreeSet<(FlatInRel, IndexSpec)> {
        self.stmts
            .iter()
            .filter_map(|stmt| match stmt {
                QueryOp::DefineSet(stmt) => match &stmt.expr {
                    InSetExpr::GetIndex(index) => {
                        Some((index.rel.clone(), index.index_spec.clone()))
                    }
                    InSetExpr::Restrict(_) => None,
                },
                QueryOp::Iter(_)
                | QueryOp::Insert(_)
                | QueryOp::GuardInhabited(_)
                | QueryOp::GuardPlan(_) => None,
            })
            .collect()
    }
}

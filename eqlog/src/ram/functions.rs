use std::collections::{BTreeMap, BTreeSet};

use super::*;
use crate::algebra::signature::Signature;
use crate::flat_eqlog::{FlatOutRel, FlatVar};
use crate::options::ModelMode;

struct RulePlans {
    name: String,
    routines: Vec<QueryPlan>,
}

impl RulePlans {
    fn owner_count(&self) -> usize {
        self.routines
            .first()
            .map_or(0, |routine| routine.flat_rule.scope.owners().len())
    }

    fn input_indices(
        &self,
    ) -> BTreeSet<(crate::flat_eqlog::FlatInRel, crate::flat_eqlog::IndexSpec)> {
        self.routines
            .iter()
            .flat_map(QueryPlan::input_indices)
            .collect()
    }
}

fn shared_routine_groups(ram_module: &RulePlans) -> Vec<Vec<&QueryPlan>> {
    let mut groups: BTreeMap<(&[FlatVar], &[QueryOp]), Vec<&QueryPlan>> = BTreeMap::new();
    let mut independent = Vec::new();
    for routine in &ram_module.routines {
        let first_loop = routine.stmts.iter().position(|stmt| match stmt {
            QueryOp::Iter(_) => true,
            QueryOp::DefineSet(_)
            | QueryOp::Insert(_)
            | QueryOp::GuardInhabited(_)
            | QueryOp::GuardPlan(_) => false,
        });
        if let Some(first_loop) = first_loop {
            groups
                .entry((
                    routine.flat_rule.scope.owners(),
                    &routine.stmts[..=first_loop],
                ))
                .or_default()
                .push(routine);
        } else {
            independent.push(vec![routine]);
        }
    }
    independent.extend(groups.into_values());
    independent
}

fn proof_owner_prefix(module: &RulePlans) -> bool {
    if module.owner_count() != 1 {
        return false;
    }
    module.routines.iter().all(|routine| {
        let owner = &routine.flat_rule.scope.owners()[0];
        !routine.flat_rule.premise.is_empty()
            && routine
                .flat_rule
                .premise
                .iter()
                .all(|stmt| stmt.args.first() == Some(owner))
            && routine.stmts.iter().all(|stmt| match stmt {
                QueryOp::DefineSet(stmt) => match &stmt.expr {
                    InSetExpr::GetIndex(index) => index.index_spec.order.first() == Some(&0),
                    InSetExpr::Restrict(_) => true,
                },
                QueryOp::Iter(_)
                | QueryOp::Insert(_)
                | QueryOp::GuardInhabited(_)
                | QueryOp::GuardPlan(_) => true,
            })
    })
}

fn proof_plan(
    routine: &QueryPlan,
    module: &RulePlans,
) -> Option<(ProofPlan, BTreeMap<String, usize>)> {
    let inputs: Vec<_> = module.input_indices().into_iter().collect();
    let mut variables = BTreeMap::new();
    for var in routine.flat_rule.premise.iter().flat_map(|stmt| &stmt.args) {
        let next = variables.len();
        variables.entry(var.name.to_string()).or_insert(next);
    }
    let owner_prefix = proof_owner_prefix(module);
    let mut atoms = Vec::new();
    for (position, premise) in routine.flat_rule.premise.iter().enumerate() {
        let mut reads = Vec::new();
        for stmt in &routine.stmts {
            match stmt {
                QueryOp::DefineSet(stmt) => match &stmt.expr {
                    InSetExpr::GetIndex(index) => {
                        if stmt.defined_var.name.stmt_index == position {
                            reads.push(index);
                        }
                    }
                    InSetExpr::Restrict(_) => {}
                },
                QueryOp::Iter(_)
                | QueryOp::Insert(_)
                | QueryOp::GuardInhabited(_)
                | QueryOp::GuardPlan(_) => {}
            }
        }
        let first = reads.first()?;
        if reads
            .iter()
            .any(|read| read.rel != premise.rel || read.index_spec.order != first.index_spec.order)
        {
            return None;
        }
        atoms.push(ProofAtom {
            inputs: reads
                .iter()
                .map(|read| {
                    inputs
                        .binary_search(&(read.rel.clone(), read.index_spec.clone()))
                        .unwrap()
                })
                .collect(),
            columns: first
                .index_spec
                .order
                .iter()
                .skip(usize::from(owner_prefix))
                .map(|&column| variables[premise.args[column].name.as_ref()])
                .collect(),
        });
    }
    let mut relevant = BTreeSet::new();
    for owner in routine.flat_rule.scope.owners() {
        if let Some(&variable) = variables.get(owner.name.as_ref()) {
            relevant.insert(variable);
        }
    }
    for stmt in &routine.stmts {
        match stmt {
            QueryOp::Iter(iter) => {
                relevant.insert(variables[iter.loop_var_el.name.as_ref()]);
            }
            QueryOp::DefineSet(_)
            | QueryOp::Insert(_)
            | QueryOp::GuardInhabited(_)
            | QueryOp::GuardPlan(_) => {}
        }
    }
    (!atoms.is_empty()).then(|| {
        (
            ProofPlan {
                atoms,
                relevant,
                owner_prefix: owner_prefix.then(|| ElVar {
                    name: routine.flat_rule.scope.owners()[0].name.clone(),
                }),
            },
            variables,
        )
    })
}

fn guard(condition: RamCondition, body: RamBlock) -> RamBlock {
    vec![RamInstruction::If {
        condition,
        then_body: body,
        else_body: Vec::new(),
    }]
}

fn binary(op: RamScalarOp, left: RamScalarExpr, right: RamScalarExpr) -> RamScalarExpr {
    RamScalarExpr::Binary {
        op,
        left: Box::new(left),
        right: Box::new(right),
    }
}

fn scalar(variable: RamScalarVar) -> RamScalarExpr {
    RamScalarExpr::Variable(variable)
}

fn define_scalar(variable: RamScalarVar, value: RamScalarExpr) -> RamInstruction {
    RamInstruction::DefineScalar { variable, value }
}

fn plan_guard(plan: &GuardPlanStmt, body: RamBlock) -> RamBlock {
    let original = RamScalarExpr::KeyCount(plan.original.clone());
    let alternative = RamScalarExpr::KeyCount(plan.alternative.clone());
    let selected = RamScalarExpr::Boolean(plan.select_alternative);
    if !plan.probe_rows {
        let preferred = binary(
            RamScalarOp::LessThan,
            binary(
                RamScalarOp::SaturatingMul,
                alternative,
                RamScalarExpr::Integer(2),
            ),
            original,
        );
        return guard(
            RamCondition::Scalar(binary(RamScalarOp::Equal, preferred, selected)),
            body,
        );
    }
    let lookup_cost = binary(
        RamScalarOp::SaturatingMul,
        binary(
            RamScalarOp::Add,
            RamScalarExpr::Log2(Box::new(binary(
                RamScalarOp::Max,
                scalar(RamScalarVar::PlanSize),
                RamScalarExpr::Integer(1),
            ))),
            RamScalarExpr::Integer(1),
        ),
        RamScalarExpr::Integer(2),
    );
    let budget = binary(
        RamScalarOp::Divide,
        scalar(RamScalarVar::PlanSize),
        scalar(RamScalarVar::PlanLookupCost),
    );
    let row_count = RamScalarExpr::RowCount {
        sets: plan.alternative.clone(),
        limit: Box::new(binary(
            RamScalarOp::SaturatingAdd,
            scalar(RamScalarVar::PlanBudget),
            RamScalarExpr::Integer(1),
        )),
    };
    let preferred = binary(
        RamScalarOp::And,
        binary(
            RamScalarOp::And,
            binary(
                RamScalarOp::GreaterThan,
                scalar(RamScalarVar::PlanSize),
                RamScalarExpr::Integer(1),
            ),
            binary(
                RamScalarOp::LessEqual,
                alternative,
                scalar(RamScalarVar::PlanBudget),
            ),
        ),
        binary(
            RamScalarOp::LessEqual,
            row_count,
            scalar(RamScalarVar::PlanBudget),
        ),
    );
    let mut result = vec![
        define_scalar(RamScalarVar::PlanSize, original),
        define_scalar(RamScalarVar::PlanLookupCost, lookup_cost),
        define_scalar(RamScalarVar::PlanBudget, budget),
        define_scalar(RamScalarVar::PlanAlternative, preferred),
    ];
    result.extend(guard(
        RamCondition::Scalar(binary(
            RamScalarOp::Equal,
            scalar(RamScalarVar::PlanAlternative),
            selected,
        )),
        body,
    ));
    result
}

fn iteration_plan(
    iteration: &IterStmt,
    signature: &Signature,
    mode: ModelMode,
) -> (RamBlock, RamIteration) {
    let mut prelude = Vec::new();
    let mut strategy = IterationStrategy::Direct;
    if !iteration.lookup_drivers.is_empty() {
        let size = RamScalarVar::LoopSize(iteration.loop_var_set.clone());
        let selected = RamScalarVar::LookupSelected(iteration.loop_var_set.clone());
        let lookup_cost = iteration.sets.len() + 1;
        prelude.push(define_scalar(
            size.clone(),
            RamScalarExpr::KeyCount(iteration.sets.clone()),
        ));
        let preferred = binary(
            RamScalarOp::And,
            binary(
                RamScalarOp::GreaterThan,
                scalar(size.clone()),
                RamScalarExpr::Integer(1),
            ),
            binary(
                RamScalarOp::LessThan,
                binary(
                    RamScalarOp::SaturatingMul,
                    RamScalarExpr::KeyCount(iteration.lookup_drivers.clone()),
                    RamScalarExpr::Integer(lookup_cost),
                ),
                scalar(size),
            ),
        );
        prelude.push(define_scalar(selected.clone(), preferred));
        strategy = IterationStrategy::AdaptiveLookup(selected);
    }
    let canonical_type = match mode {
        ModelMode::Native => iteration.canonical_filter.then(|| {
            let set = &iteration.sets[0];
            let column = set.name.index.order[set.name.restricted];
            set.name.rel.arity(signature)[column]
        }),
        ModelMode::Desugared => {
            // Trie row order can change after removals, so functionality needs
            // the age-aware anchor rather than its first current restriction.
            if iteration.first_only {
                assert_eq!(iteration.sets.len(), 1, "desugared anchors read one set");
                strategy = IterationStrategy::Oldest;
            }
            None
        }
    };
    (
        prelude,
        RamIteration {
            sets: iteration.sets.clone(),
            lookup_drivers: iteration.lookup_drivers.clone(),
            loop_var_el: iteration.loop_var_el.clone(),
            loop_var_set: iteration.loop_var_set.clone(),
            strategy,
            canonical_type,
            limit: iteration.first_only.then_some(1),
        },
    )
}

fn insertion_body(stmt: &InsertStmt, mode: ModelMode) -> RamBlock {
    let body = vec![RamInstruction::Insert(stmt.clone())];
    match stmt.rel {
        FlatOutRel::Equality(_) => {
            let [left, right] = stmt.args.as_slice() else {
                unreachable!("equality output has two operands")
            };
            if left == right {
                return Vec::new();
            }
            guard(RamCondition::Distinct(left.clone(), right.clone()), body)
        }
        FlatOutRel::Rel(rel) => match mode {
            ModelMode::Native => body,
            ModelMode::Desugared => guard(
                RamCondition::Absent {
                    rel,
                    args: stmt.args.clone(),
                },
                body,
            ),
        },
        FlatOutRel::FuncDomain(_) => body,
    }
}

fn nest(
    stmts: &[QueryOp],
    mut body: RamBlock,
    proof: Option<&BTreeMap<String, usize>>,
    signature: &Signature,
    mode: ModelMode,
) -> RamBlock {
    for stmt in stmts.iter().rev() {
        match stmt {
            QueryOp::DefineSet(stmt) => {
                let mut stmt = stmt.clone();
                match mode {
                    ModelMode::Native => {}
                    ModelMode::Desugared => stmt.defined_var.strictness = Strictness::Strict,
                }
                body.insert(0, RamInstruction::DefineSet(stmt));
            }
            QueryOp::Insert(stmt) => {
                let insertion = insertion_body(stmt, mode);
                if proof.is_some() {
                    body.splice(0..0, guard(RamCondition::Uncovered, insertion));
                } else {
                    body.splice(0..0, insertion);
                }
            }
            QueryOp::Iter(iteration) => {
                let proof_variable =
                    proof.map(|variables| variables[iteration.loop_var_el.name.as_ref()]);
                if let Some(variable) = proof_variable {
                    body = guard(RamCondition::Uncovered, body);
                    body.insert(
                        0,
                        RamInstruction::RestrictProof {
                            variable,
                            value: iteration.loop_var_el.clone(),
                            access: ProofAccess::Borrow,
                        },
                    );
                }
                let (mut prelude, iteration) = iteration_plan(iteration, signature, mode);
                if let Some(variable) = proof_variable {
                    prelude.insert(0, RamInstruction::PrepareProofKeys(variable));
                }
                prelude.push(RamInstruction::ForEach {
                    iteration,
                    proof_variable,
                    body,
                });
                body = prelude;
            }
            QueryOp::GuardInhabited(condition) => {
                body = guard(RamCondition::Inhabited(condition.clone()), body);
            }
            QueryOp::GuardPlan(condition) => {
                body = plan_guard(condition, body);
            }
        }
    }
    body
}

fn shared_body(routines: &[&[QueryOp]], signature: &Signature, mode: ModelMode) -> RamBlock {
    let first = routines[0];
    if routines.len() == 1 {
        return nest(first, Vec::new(), None, signature, mode);
    }
    let shared = first
        .iter()
        .enumerate()
        .take_while(|(i, stmt)| match stmt {
            QueryOp::Insert(_) => false,
            QueryOp::DefineSet(_)
            | QueryOp::Iter(_)
            | QueryOp::GuardInhabited(_)
            | QueryOp::GuardPlan(_) => routines.iter().all(|routine| routine.get(*i) == Some(stmt)),
        })
        .count();
    let mut branches: BTreeMap<&QueryOp, Vec<&[QueryOp]>> = BTreeMap::new();
    for routine in routines {
        if let Some(stmt) = routine.get(shared) {
            branches.entry(stmt).or_default().push(&routine[shared..]);
        }
    }
    let mut body = Vec::new();
    for (stmt, branch) in branches {
        let branch = match stmt {
            QueryOp::Insert(_) => branch
                .into_iter()
                .map(|suffix| RamInstruction::Scope(shared_body(&[suffix], signature, mode)))
                .collect(),
            QueryOp::DefineSet(_)
            | QueryOp::Iter(_)
            | QueryOp::GuardInhabited(_)
            | QueryOp::GuardPlan(_) => shared_body(&branch, signature, mode),
        };
        body.push(RamInstruction::Scope(branch));
    }
    nest(&first[..shared], body, None, signature, mode)
}

fn proved_body(
    routine: &QueryPlan,
    plan: ProofPlan,
    variables: &BTreeMap<String, usize>,
    signature: &Signature,
    mode: ModelMode,
) -> RamBlock {
    let owner_prefix = plan.owner_prefix.is_some();
    let mut body = vec![RamInstruction::BeginProof(plan)];
    if !owner_prefix {
        for owner in routine.flat_rule.scope.owners() {
            if let Some(&variable) = variables.get(owner.name.as_ref()) {
                body.push(RamInstruction::RestrictProof {
                    variable,
                    value: ElVar {
                        name: owner.name.clone(),
                    },
                    access: ProofAccess::Consume,
                });
            }
        }
    }
    body.extend(guard(
        RamCondition::Uncovered,
        nest(&routine.stmts, Vec::new(), Some(variables), signature, mode),
    ));
    body
}

pub fn lower_function(
    name: String,
    routines: Vec<QueryPlan>,
    signature: &Signature,
    mode: ModelMode,
) -> RamFunction {
    let plans = RulePlans { name, routines };
    let module = &plans;
    let owners = module.routines.first().map_or_else(Vec::new, |routine| {
        routine
            .flat_rule
            .scope
            .owners()
            .iter()
            .map(|owner| owner.typ)
            .collect()
    });
    let matching_proofs = match mode {
        ModelMode::Native => !owners.is_empty(),
        ModelMode::Desugared => false,
    };
    let mut interface = FunctionInterface {
        inputs: module.input_indices(),
        outputs: BTreeSet::new(),
        canonical_types: BTreeSet::new(),
        owners,
        matching_proofs,
        proof_owner_prefix: proof_owner_prefix(module),
    };
    for stmt in module.routines.iter().flat_map(|routine| &routine.stmts) {
        match stmt {
            QueryOp::Iter(iteration) => {
                if iteration_plan(iteration, signature, mode)
                    .1
                    .canonical_type
                    .is_some()
                {
                    let set = &iteration.sets[0];
                    let column = set.name.index.order[set.name.restricted];
                    interface
                        .canonical_types
                        .insert(set.name.rel.arity(signature)[column]);
                }
            }
            QueryOp::Insert(stmt) => {
                interface.outputs.insert(stmt.rel);
            }
            QueryOp::DefineSet(_) | QueryOp::GuardInhabited(_) | QueryOp::GuardPlan(_) => {}
        }
    }
    let procedures: Vec<_> = shared_routine_groups(module)
        .into_iter()
        .map(|routines| {
            let stmts: Vec<_> = routines
                .iter()
                .map(|routine| routine.stmts.as_slice())
                .collect();
            let mut body = shared_body(&stmts, signature, mode);
            let plans: Option<Vec<_>> = if matching_proofs {
                routines
                    .iter()
                    .map(|routine| proof_plan(routine, module))
                    .collect()
            } else {
                None
            };
            if let Some(plans) = plans {
                let proved = routines
                    .iter()
                    .zip(plans)
                    .map(|(routine, (plan, variables))| {
                        RamInstruction::Scope(proved_body(
                            routine, plan, &variables, signature, mode,
                        ))
                    })
                    .collect();
                body = vec![RamInstruction::If {
                    condition: RamCondition::NoProofs,
                    then_body: body,
                    else_body: proved,
                }];
            }
            RamProcedure {
                name: routines[0].name.clone(),
                owners: routines[0]
                    .flat_rule
                    .scope
                    .owners()
                    .iter()
                    .map(|owner| ElVar {
                        name: owner.name.clone(),
                    })
                    .collect(),
                rules: routines
                    .iter()
                    .map(|routine| routine.flat_rule.clone())
                    .collect(),
                body,
            }
        })
        .collect();
    let rules = plans
        .routines
        .into_iter()
        .map(|routine| {
            let inputs = routine.input_indices();
            RuleSource {
                flat_rule: routine.flat_rule,
                inputs,
            }
        })
        .collect();
    RamFunction {
        name: plans.name,
        rules,
        interface,
        body: (0..procedures.len()).map(RamInstruction::Call).collect(),
        procedures,
    }
}

#[derive(Clone, Copy)]
pub enum CompactTransportIteration {
    Components,
    Objects,
    Outgoing,
    Morphisms,
    IncomingGroups,
    EnumeratedMorphisms,
}

#[derive(Clone, Copy)]
pub enum CompactTransportBinding {
    Incoming,
    Morphisms,
    Indices,
    Next,
    Changed,
    Position,
}

#[derive(Clone, Copy)]
pub enum CompactTransportCall {
    Incoming,
    Batch,
    Morphism,
    Selected,
}

#[derive(Clone, Copy)]
pub enum CompactTransportOptional {
    Call(CompactTransportCall),
    IncomingForObject,
    Indices,
    Position,
}

#[derive(Clone)]
pub enum CompactTransportCondition {
    Active,
    CyclicComponent,
    Batch,
    DifferentTarget,
    SelfEdge,
    PrimarySource,
    Adopted,
    And(
        Box<CompactTransportCondition>,
        Box<CompactTransportCondition>,
    ),
    Or(
        Box<CompactTransportCondition>,
        Box<CompactTransportCondition>,
    ),
}

#[derive(Clone, Copy)]
pub enum CompactTransportLocal {
    Changed,
    Batch,
    Target,
    Incoming,
    Primary,
    Position,
}

#[derive(Clone, Copy)]
pub enum CompactTransportReturn {
    None,
    Changed,
    Incoming,
}

#[derive(Clone)]
pub enum CompactTransportInstruction {
    ForEach {
        iteration: CompactTransportIteration,
        labeled: bool,
        body: Vec<CompactTransportInstruction>,
    },
    If {
        condition: CompactTransportCondition,
        then_body: Vec<CompactTransportInstruction>,
        else_body: Vec<CompactTransportInstruction>,
    },
    IfSome {
        binding: CompactTransportBinding,
        source: CompactTransportOptional,
        then_body: Vec<CompactTransportInstruction>,
        else_body: Vec<CompactTransportInstruction>,
    },
    RequireSome {
        binding: CompactTransportBinding,
        source: CompactTransportOptional,
        else_body: Vec<CompactTransportInstruction>,
    },
    Initialize(CompactTransportLocal),
    AccumulateChanged,
    RejectBatch,
    RecordIncoming,
    RememberPosition,
    RotatePrimary,
    FillInserted,
    Break {
        labeled: bool,
    },
    Return(CompactTransportReturn),
}

#[derive(Default)]
pub struct CompactTransportPlan {
    pub graph: Vec<CompactTransportInstruction>,
    pub component: Vec<CompactTransportInstruction>,
    pub selected: Vec<CompactTransportInstruction>,
    pub incoming: Vec<CompactTransportInstruction>,
}

fn when(
    condition: CompactTransportCondition,
    then_body: Vec<CompactTransportInstruction>,
) -> CompactTransportInstruction {
    CompactTransportInstruction::If {
        condition,
        then_body,
        else_body: Vec::new(),
    }
}

fn for_each(
    iteration: CompactTransportIteration,
    body: Vec<CompactTransportInstruction>,
) -> CompactTransportInstruction {
    CompactTransportInstruction::ForEach {
        iteration,
        labeled: false,
        body,
    }
}

fn changed_call(
    call: CompactTransportCall,
    else_body: Vec<CompactTransportInstruction>,
) -> CompactTransportInstruction {
    CompactTransportInstruction::IfSome {
        binding: CompactTransportBinding::Next,
        source: CompactTransportOptional::Call(call),
        then_body: vec![CompactTransportInstruction::AccumulateChanged],
        else_body,
    }
}

impl CompactTransportPlan {
    pub fn new(supported: bool) -> Self {
        if !supported {
            return Self::default();
        }
        let graph = vec![CompactTransportInstruction::IfSome {
            binding: CompactTransportBinding::Incoming,
            source: CompactTransportOptional::Call(CompactTransportCall::Incoming),
            then_body: vec![
                CompactTransportInstruction::Initialize(CompactTransportLocal::Changed),
                CompactTransportInstruction::ForEach {
                    iteration: CompactTransportIteration::Components,
                    labeled: true,
                    body: vec![for_each(
                        CompactTransportIteration::Objects,
                        vec![CompactTransportInstruction::IfSome {
                            binding: CompactTransportBinding::Morphisms,
                            source: CompactTransportOptional::IncomingForObject,
                            then_body: vec![changed_call(
                                CompactTransportCall::Batch,
                                vec![CompactTransportInstruction::Break { labeled: true }],
                            )],
                            else_body: Vec::new(),
                        }],
                    )],
                },
                when(
                    CompactTransportCondition::Active,
                    vec![CompactTransportInstruction::Return(
                        CompactTransportReturn::Changed,
                    )],
                ),
            ],
            else_body: Vec::new(),
        }];
        let component = vec![when(
            CompactTransportCondition::Active,
            vec![
                CompactTransportInstruction::Initialize(CompactTransportLocal::Changed),
                CompactTransportInstruction::Initialize(CompactTransportLocal::Target),
                CompactTransportInstruction::Initialize(CompactTransportLocal::Batch),
                for_each(
                    CompactTransportIteration::Morphisms,
                    vec![when(
                        CompactTransportCondition::Or(
                            Box::new(CompactTransportCondition::DifferentTarget),
                            Box::new(CompactTransportCondition::SelfEdge),
                        ),
                        vec![
                            CompactTransportInstruction::RejectBatch,
                            CompactTransportInstruction::Break { labeled: false },
                        ],
                    )],
                ),
                CompactTransportInstruction::If {
                    condition: CompactTransportCondition::Batch,
                    then_body: vec![changed_call(CompactTransportCall::Batch, Vec::new())],
                    else_body: vec![for_each(
                        CompactTransportIteration::Morphisms,
                        vec![changed_call(
                            CompactTransportCall::Morphism,
                            vec![CompactTransportInstruction::Break { labeled: false }],
                        )],
                    )],
                },
                when(
                    CompactTransportCondition::Active,
                    vec![CompactTransportInstruction::Return(
                        CompactTransportReturn::Changed,
                    )],
                ),
            ],
        )];
        let selected = vec![CompactTransportInstruction::IfSome {
            binding: CompactTransportBinding::Changed,
            source: CompactTransportOptional::Call(CompactTransportCall::Selected),
            then_body: vec![
                CompactTransportInstruction::FillInserted,
                CompactTransportInstruction::Return(CompactTransportReturn::Changed),
            ],
            else_body: Vec::new(),
        }];
        let incoming = vec![
            CompactTransportInstruction::RequireSome {
                binding: CompactTransportBinding::Indices,
                source: CompactTransportOptional::Indices,
                else_body: vec![CompactTransportInstruction::Return(
                    CompactTransportReturn::None,
                )],
            },
            for_each(
                CompactTransportIteration::Components,
                vec![when(
                    CompactTransportCondition::CyclicComponent,
                    vec![CompactTransportInstruction::Return(
                        CompactTransportReturn::None,
                    )],
                )],
            ),
            CompactTransportInstruction::Initialize(CompactTransportLocal::Incoming),
            for_each(
                CompactTransportIteration::Components,
                vec![for_each(
                    CompactTransportIteration::Outgoing,
                    vec![CompactTransportInstruction::RecordIncoming],
                )],
            ),
            for_each(
                CompactTransportIteration::IncomingGroups,
                vec![
                    CompactTransportInstruction::Initialize(CompactTransportLocal::Primary),
                    CompactTransportInstruction::Initialize(CompactTransportLocal::Position),
                    // Keeping the adopted source first preserves public image identities
                    // while another incoming edge extends the inherited relation.
                    for_each(
                        CompactTransportIteration::EnumeratedMorphisms,
                        vec![when(
                            CompactTransportCondition::And(
                                Box::new(CompactTransportCondition::PrimarySource),
                                Box::new(CompactTransportCondition::Adopted),
                            ),
                            vec![
                                CompactTransportInstruction::RememberPosition,
                                CompactTransportInstruction::Break { labeled: false },
                            ],
                        )],
                    ),
                    CompactTransportInstruction::IfSome {
                        binding: CompactTransportBinding::Position,
                        source: CompactTransportOptional::Position,
                        then_body: vec![CompactTransportInstruction::RotatePrimary],
                        else_body: Vec::new(),
                    },
                ],
            ),
            CompactTransportInstruction::Return(CompactTransportReturn::Incoming),
        ];
        Self {
            graph,
            component,
            selected,
            incoming,
        }
    }
}

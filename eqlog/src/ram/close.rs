pub enum CloseOperation {
    CanonicalizeRelations,
    TakeDelta,
    ClearAllocated,
    ApplyDeferredFunctions,
    SaveDelta,
    Canonicalize,
    MarkClosed,
    ReturnFalse,
    ReturnCondition,
    CheckConditionBeforeDelta,
    CheckCondition,
    InitializeChanges(usize),
    MarkChanged(usize),
    BreakUnlessChanged(usize),
}

pub fn close_completion() -> [CloseOperation; 4] {
    [
        CloseOperation::SaveDelta,
        CloseOperation::Canonicalize,
        CloseOperation::MarkClosed,
        CloseOperation::ReturnFalse,
    ]
}

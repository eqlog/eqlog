use super::ast::*;

#[derive(Copy, Clone, PartialEq, Eq, Hash, Debug)]
pub enum SymbolType {
    Sort,
    Pred,
    Func,
}

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub enum SortCheckError {
    WrongSymbolType { expected: SymbolType, got: SymbolType },
    UndefinedSymbol,
    RedefinedSymbol,
    WrongArgumentNumber { expected: usize, got: usize },
    ConflictingSort(Term, String, String),
    UnspecifiedSort(Term),
    BothSidesUndefined(Term, Term),
    SubtermUndefined(Term),
    VariableNotInPremise(Term),
    VariableOrWildcardInConclusionDefineAtom(Term),
    SubtermOfDefineConclusionUndefined(Term),
    DefineInComplexConclusion(Term),
    FreeVariableInConclusion(Term),
}

pub type SortCheckResult<T> = std::result::Result<T, SortCheckError>;

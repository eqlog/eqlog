use crate::ast::*;

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub enum SemanticsError {
    FunctionArgumentNumber {
        function: String,
        expected: usize,
        got: usize,
        location: Option<Location>,
    },
    PredicateArgumentNumber {
        predicate: String,
        expected: usize,
        got: usize,
        location: Option<Location>,
    },
    UndeclaredSymbol {
        name: String,
        location: Option<Location>,
    },
    NoSort {
        location: Option<Location>,
    },
    ConflictingSorts {
        sorts: Vec<String>,
        location: Option<Location>,
    },
    VariableNotInPremise {
        var: String,
        location: Option<Location>,
    },
    WildcardInConclusion {
        location: Option<Location>,
    },
    ConclusionEqualityOfNewTerms {
        location: Option<Location>,
    },
    ConclusionEqualityArgNew {
        location: Option<Location>,
    },
    ConclusionPredicateArgNew {
        location: Option<Location>,
    },
}

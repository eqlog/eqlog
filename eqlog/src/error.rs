use crate::ast::*;
use lalrpop_util::{lexer::Token, ParseError};
use std::error::Error;
use std::fmt::{self, Display};

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub enum CompileError {
    InvalidToken {
        location: usize,
    },
    UnrecognizedEOF {
        location: usize,
        expected: Vec<String>,
    },
    UnrecognizedToken {
        location: Location,
        expected: Vec<String>,
    },
    ExtraToken {
        location: Location,
    },
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

impl<'a> From<ParseError<usize, Token<'a>, CompileError>> for CompileError {
    fn from(parse_error: ParseError<usize, Token<'_>, CompileError>) -> CompileError {
        match parse_error {
            ParseError::InvalidToken { location } => CompileError::InvalidToken { location },
            ParseError::UnrecognizedEOF { location, expected } => {
                CompileError::UnrecognizedEOF { location, expected }
            }
            ParseError::UnrecognizedToken { token, expected } => CompileError::UnrecognizedToken {
                location: Location(token.0, token.2),
                expected,
            },
            ParseError::ExtraToken { token } => CompileError::ExtraToken {
                location: Location(token.0, token.2),
            },
            ParseError::User { error } => error,
        }
    }
}

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub struct CompileErrorWithSource {
    pub error: CompileError,
    pub source: String,
}

impl Display for CompileErrorWithSource {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        use CompileError::*;
        match &self.error {
            InvalidToken { location: _ } => {
                write!(f, "invalid token")?;
            }
            UnrecognizedEOF {
                location: _,
                expected: _,
            } => {
                write!(f, "unexpected end of file")?;
            }
            UnrecognizedToken {
                location: _,
                expected: _,
            } => {
                write!(f, "unrecognized token")?;
            }
            ExtraToken { location: _ } => {
                write!(f, "extra token")?;
            }
            FunctionArgumentNumber {
                function: _,
                expected,
                got,
                location: _,
            } => {
                write!(
                    f,
                    "function takes {expected} arguments but {got} were supplied"
                )?;
            }
            PredicateArgumentNumber {
                predicate: _,
                expected,
                got,
                location: _,
            } => {
                write!(
                    f,
                    "predicate takes {expected} arguments but {got} were supplied"
                )?;
            }
            UndeclaredSymbol {
                name: _,
                location: _,
            } => {
                write!(f, "undeclared symbol")?;
            }
            NoSort { location: _ } => {
                write!(f, "sort of term undetermined")?;
            }
            ConflictingSorts {
                sorts: _,
                location: _,
            } => {
                write!(f, "term has conflicting sorts")?;
            }
            VariableNotInPremise {
                var: _,
                location: _,
            } => {
                write!(f, "variable in conclusion not used in premise")?;
            }
            WildcardInConclusion { location: _ } => {
                write!(f, "wildcard in conclusion")?;
            }
            ConclusionEqualityOfNewTerms { location: _ } => {
                write!(
                    f,
                    "both sides of equality in conclusion are not used earlier"
                )?;
            }
            ConclusionEqualityArgNew { location: _ } => {
                write!(
                    f,
                    "argument of undefined term in equality in conclusion is not used earlier"
                )?;
            }
            ConclusionPredicateArgNew { location: _ } => {
                write!(f, "argument of predicate in conclusion is not used earlier")?;
            }
        }
        Ok(())
    }
}

impl Error for CompileErrorWithSource {}

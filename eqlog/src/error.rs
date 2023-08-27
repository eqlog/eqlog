use crate::source_display::*;
use lalrpop_util::{lexer::Token, ParseError};
use std::error::Error;
use std::fmt::{self, Display};
use std::path::PathBuf;

#[derive(Copy, Clone, PartialEq, Eq, Debug, Hash)]
pub enum SymbolKind {
    Type,
    Pred,
    Func,
}

impl Display for SymbolKind {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        use SymbolKind::*;
        f.write_str(match self {
            Type => "type",
            Pred => "pred",
            Func => "func",
        })
    }
}

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub enum CompileError {
    InvalidToken {
        location: Location,
    },
    UnrecognizedEOF {
        location: Location,
        expected: Vec<String>,
    },
    UnrecognizedToken {
        location: Location,
        expected: Vec<String>,
    },
    ExtraToken {
        location: Location,
    },
    SymbolNotCamelCase {
        name: String,
        location: Option<Location>,
        symbol_kind: SymbolKind,
    },
    SymbolNotSnakeCase {
        name: String,
        location: Option<Location>,
        symbol_kind: SymbolKind,
    },
    VariableNotSnakeCase {
        name: String,
        location: Location,
    },
    VariableOccursOnlyOnce {
        name: String,
        location: Option<Location>,
    },
    QueryVariableOnlyInOutput {
        name: String,
        location: Option<Location>,
    },
    FunctionArgumentNumber {
        function: String,
        expected: usize,
        got: usize,
        location: Location,
    },
    PredicateArgumentNumber {
        predicate: String,
        expected: usize,
        got: usize,
        location: Option<Location>,
    },
    UndeclaredSymbol {
        name: String,
        used_at: Location,
    },
    BadSymbolKind {
        name: String,
        expected: SymbolKind,
        found: SymbolKind,
        used_at: Location,
        declared_at: Location,
    },
    SymbolDeclaredTwice {
        name: String,
        first_declaration: Location,
        second_declaration: Location,
    },
    ReductionFromVariableOrWildcard {
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
            ParseError::InvalidToken { location } => CompileError::InvalidToken {
                location: Location(location, location + 1),
            },
            ParseError::UnrecognizedEof { location, expected } => CompileError::UnrecognizedEOF {
                location: Location(location, location + 1),
                expected,
            },
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
pub struct CompileErrorWithContext {
    pub error: CompileError,
    pub source_path: PathBuf,
    pub source: String,
}

impl Display for CompileErrorWithContext {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        use CompileError::*;
        let CompileErrorWithContext {
            error,
            source_path,
            source,
        } = self;
        let write_loc = |f: &mut fmt::Formatter, loc: Option<Location>| -> fmt::Result {
            if let Some(loc) = loc {
                let src_displ = SourceDisplay {
                    source_path: Some(source_path),
                    underlined: true,
                    ..SourceDisplay::new(source, loc)
                };
                write!(f, "{}", src_displ)?;
            } else {
                write!(f, "{}", source_path_pointer(source_path))?;
            }
            Ok(())
        };
        write!(f, "Error: ")?;
        match error {
            InvalidToken { location } => {
                write!(f, "invalid token\n")?;
                write_loc(f, Some(*location))?;
            }
            UnrecognizedEOF {
                location,
                expected: _,
            } => {
                write!(f, "unexpected end of file\n")?;
                write_loc(f, Some(*location))?;
            }
            UnrecognizedToken {
                location,
                expected: _,
            } => {
                write!(f, "unrecognized token\n")?;
                write_loc(f, Some(*location))?;
            }
            ExtraToken { location } => {
                write!(f, "unexpected token\n")?;
                write_loc(f, Some(*location))?;
            }
            SymbolNotCamelCase {
                name,
                location,
                symbol_kind,
            } => {
                write!(f, "{symbol_kind} {name} is not UpperCamelCase\n")?;
                write_loc(f, *location)?;
            }
            SymbolNotSnakeCase {
                name,
                location,
                symbol_kind,
            } => {
                write!(f, "{symbol_kind} {name} is not lower_snake_case\n")?;
                write_loc(f, *location)?;
            }
            VariableNotSnakeCase { name, location } => {
                write!(f, "variable {name} is not lower_snake_case\n")?;
                write_loc(f, Some(*location))?;
            }
            VariableOccursOnlyOnce { name, location } => {
                write!(f, "variable {name} occurs only once\n")?;
                write_loc(f, *location)?;
            }
            QueryVariableOnlyInOutput { name, location } => {
                write!(f, "variable {name} occurs only as output\n")?;
                write_loc(f, *location)?;
            }
            FunctionArgumentNumber {
                function: _,
                expected,
                got,
                location,
            } => {
                write!(
                    f,
                    "function takes {expected} arguments but {got} were supplied\n"
                )?;
                write_loc(f, Some(*location))?;
            }
            PredicateArgumentNumber {
                predicate: _,
                expected,
                got,
                location,
            } => {
                write!(
                    f,
                    "predicate takes {expected} arguments but {got} were supplied\n"
                )?;
                write_loc(f, *location)?;
            }
            UndeclaredSymbol { name, used_at } => {
                write!(f, "undeclared symbol \"{name}\"\n")?;
                write_loc(f, Some(*used_at))?;
            }
            BadSymbolKind {
                name,
                expected,
                found,
                used_at,
                declared_at,
            } => {
                write!(f, "expected {expected}, found {found} {name}\n")?;
                write_loc(f, Some(*used_at))?;
                write!(f, "{name} declared as {found} here:\n")?;
                write_loc(f, Some(*declared_at))?;
            }
            SymbolDeclaredTwice {
                name: _,
                first_declaration,
                second_declaration,
            } => {
                write!(f, "symbol declared multiple times\n")?;
                write_loc(f, Some(*second_declaration))?;
                write!(f, "Previously declared here:\n")?;
                write_loc(f, Some(*first_declaration))?;
            }
            ReductionFromVariableOrWildcard { location } => {
                write!(f, "term before ~> cannot be variable or wildcard\n")?;
                write_loc(f, *location)?;
            }
            NoSort { location } => {
                write!(f, "sort of term undetermined\n")?;
                write_loc(f, *location)?;
            }
            ConflictingSorts { sorts: _, location } => {
                write!(f, "term has conflicting sorts\n")?;
                write_loc(f, *location)?;
            }
            VariableNotInPremise { var: _, location } => {
                write!(f, "variable in conclusion not used in premise\n")?;
                write_loc(f, *location)?;
            }
            WildcardInConclusion { location } => {
                write!(f, "wildcard in conclusion\n")?;
                write_loc(f, *location)?;
            }
            ConclusionEqualityOfNewTerms { location } => {
                write!(
                    f,
                    "both sides of equality in conclusion are not used earlier\n"
                )?;
                write_loc(f, *location)?;
            }
            ConclusionEqualityArgNew { location } => {
                write!(
                    f,
                    "argument of undefined term in equality in conclusion is not used earlier\n"
                )?;
                write_loc(f, *location)?;
            }
            ConclusionPredicateArgNew { location } => {
                write!(f, "argument of predicate in conclusion is not used earlier")?;
                write_loc(f, *location)?;
            }
        }
        Ok(())
    }
}

impl Error for CompileErrorWithContext {}

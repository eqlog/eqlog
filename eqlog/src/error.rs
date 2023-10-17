use crate::grammar_util::*;
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
    Rule,
}

impl Display for SymbolKind {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        use SymbolKind::*;
        f.write_str(match self {
            Type => "type",
            Pred => "predicate",
            Func => "function",
            Rule => "rule",
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
        location: Location,
        symbol_kind: SymbolKind,
    },
    SymbolNotSnakeCase {
        name: String,
        location: Location,
        symbol_kind: SymbolKind,
    },
    VariableNotSnakeCase {
        name: String,
        location: Location,
    },
    VariableOccursOnlyOnce {
        name: String,
        location: Location,
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
        location: Location,
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
    IfAfterThen {
        location: Location,
    },
    UndeterminedTermType {
        location: Location,
    },
    ConflictingTermType {
        types: Vec<String>,
        location: Location,
    },
    VariableIntroducedInThenStmt {
        location: Location,
    },
    WildcardInThenStmt {
        location: Location,
    },
    SurjectivityViolation {
        location: Location,
    },
    ThenDefinedNotVar {
        location: Location,
    },
    ThenDefinedVarNotNew {
        location: Location,
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

impl<'a> From<ParseError<usize, Token<'a>, NeverType>> for CompileError {
    fn from(parse_error: ParseError<usize, Token<'_>, NeverType>) -> CompileError {
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
            ParseError::User { error } => match error {},
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
        let write_loc = |f: &mut fmt::Formatter, loc: Location| -> fmt::Result {
            let src_displ = SourceDisplay {
                source_path: Some(source_path),
                underlined: true,
                ..SourceDisplay::new(source, loc)
            };
            write!(f, "{}", src_displ)?;
            Ok(())
        };
        write!(f, "Error: ")?;
        match error {
            InvalidToken { location } => {
                write!(f, "invalid token\n")?;
                write_loc(f, *location)?;
            }
            UnrecognizedEOF {
                location,
                expected: _,
            } => {
                write!(f, "unexpected end of file\n")?;
                write_loc(f, *location)?;
            }
            UnrecognizedToken {
                location,
                expected: _,
            } => {
                write!(f, "unrecognized token\n")?;
                write_loc(f, *location)?;
            }
            ExtraToken { location } => {
                write!(f, "unexpected token\n")?;
                write_loc(f, *location)?;
            }
            SymbolNotCamelCase {
                name,
                location,
                symbol_kind,
            } => {
                write!(f, "{symbol_kind} \"{name}\" is not UpperCamelCase\n")?;
                write_loc(f, *location)?;
            }
            SymbolNotSnakeCase {
                name,
                location,
                symbol_kind,
            } => {
                write!(f, "{symbol_kind} \"{name}\" is not lower_snake_case\n")?;
                write_loc(f, *location)?;
            }
            VariableNotSnakeCase { name, location } => {
                write!(f, "variable \"{name}\" is not lower_snake_case\n")?;
                write_loc(f, *location)?;
            }
            VariableOccursOnlyOnce { name, location } => {
                write!(f, "variable \"{name}\" occurs only once\n")?;
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
                write_loc(f, *location)?;
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
                write_loc(f, *used_at)?;
            }
            BadSymbolKind {
                name,
                expected,
                found,
                used_at,
                declared_at,
            } => {
                write!(f, "expected {expected}, found {found} \"{name}\"\n")?;
                write_loc(f, *used_at)?;
                write!(f, "\"{name}\" declared as {found} here:\n")?;
                write_loc(f, *declared_at)?;
            }
            SymbolDeclaredTwice {
                name: _,
                first_declaration,
                second_declaration,
            } => {
                write!(f, "symbol declared multiple times\n")?;
                write_loc(f, *second_declaration)?;
                write!(f, "Previously declared here:\n")?;
                write_loc(f, *first_declaration)?;
            }
            IfAfterThen { location } => {
                write!(f, "if statement after then statement not supported yet\n")?;
                write_loc(f, *location)?;
            }
            UndeterminedTermType { location } => {
                write!(f, "sort of term undetermined\n")?;
                write_loc(f, *location)?;
            }
            ConflictingTermType { types: _, location } => {
                write!(f, "term has conflicting types\n")?;
                write_loc(f, *location)?;
            }
            VariableIntroducedInThenStmt { location } => {
                write!(f, "variable introduced in then statement\n")?;
                write_loc(f, *location)?;
            }
            WildcardInThenStmt { location } => {
                write!(f, "wildcards must not appear in then statements\n")?;
                write_loc(f, *location)?;
            }
            SurjectivityViolation { location } => {
                write!(f, "term does not appear earlier in this rule\n")?;
                write_loc(f, *location)?;
            }
            ThenDefinedNotVar { location } => {
                write!(f, "expected a variable\n")?;
                write_loc(f, *location)?;
            }
            ThenDefinedVarNotNew { location } => {
                write!(f, "variable has already been introduced earlier\n")?;
                write_loc(f, *location)?;
            }
        }
        Ok(())
    }
}

impl Error for CompileErrorWithContext {}

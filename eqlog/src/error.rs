use crate::grammar_util::*;
use crate::source_display::*;
use eqlog_eqlog::*;
use lalrpop_util::{lexer::Token, ParseError};
use std::cmp::Ordering;
use std::error::Error;
use std::fmt::{self, Display};
use std::path::PathBuf;

fn display_symbol_kind(symbol_kind: SymbolKindCase) -> &'static str {
    match symbol_kind {
        SymbolKindCase::TypeSymbol() => "type",
        SymbolKindCase::PredSymbol() => "predicate",
        SymbolKindCase::FuncSymbol() => "function",
        SymbolKindCase::RuleSymbol() => "rule",
        SymbolKindCase::EnumSymbol() => "enum",
        SymbolKindCase::CtorSymbol() => "constructor",
        SymbolKindCase::ModelSymbol() => "model",
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
        symbol_kind: SymbolKindCase,
    },
    SymbolNotSnakeCase {
        name: String,
        location: Location,
        symbol_kind: SymbolKindCase,
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
        expected: usize,
        got: usize,
        location: Location,
    },
    PredicateArgumentNumber {
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
        expected: SymbolKindCase,
        found: SymbolKindCase,
        used_at: Location,
        declared_at: Location,
    },
    SymbolDeclaredTwice {
        name: String,
        first_declaration: Location,
        second_declaration: Location,
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
    EnumCtorsNotSurjective {
        term_location: Location,
        enum_name: String,
        enum_location: Location,
    },
    MatchPatternIsVariable {
        location: Location,
    },
    MatchPatternIsWildcard {
        location: Location,
    },
    MatchPatternCtorArgIsApp {
        location: Location,
    },
    MatchPatternArgVarIsNotFresh {
        location: Location,
    },
    MatchConflictingEnum {
        match_stmt_location: Location,
        first_ctor_decl_location: Location,
        second_ctor_decl_location: Location,
    },
    MatchNotExhaustive {
        match_location: Location,
        missing_ctor_decl_location: Location,
    },
    IllegalMemberTypeExprInArgDecl {
        location: Location,
    },
}

impl CompileError {
    pub fn primary_location(&self) -> Location {
        match self {
            CompileError::InvalidToken { location } => *location,
            CompileError::UnrecognizedEOF { location, .. } => *location,
            CompileError::UnrecognizedToken { location, .. } => *location,
            CompileError::ExtraToken { location } => *location,
            CompileError::SymbolNotCamelCase { location, .. } => *location,
            CompileError::SymbolNotSnakeCase { location, .. } => *location,
            CompileError::VariableNotSnakeCase { location, .. } => *location,
            CompileError::VariableOccursOnlyOnce { location, .. } => *location,
            CompileError::FunctionArgumentNumber { location, .. } => *location,
            CompileError::PredicateArgumentNumber { location, .. } => *location,
            CompileError::UndeclaredSymbol { used_at, .. } => *used_at,
            CompileError::BadSymbolKind { used_at, .. } => *used_at,
            CompileError::SymbolDeclaredTwice {
                second_declaration, ..
            } => *second_declaration,
            CompileError::UndeterminedTermType { location } => *location,
            CompileError::ConflictingTermType { location, .. } => *location,
            CompileError::VariableIntroducedInThenStmt { location } => *location,
            CompileError::WildcardInThenStmt { location } => *location,
            CompileError::SurjectivityViolation { location } => *location,
            CompileError::ThenDefinedNotVar { location } => *location,
            CompileError::ThenDefinedVarNotNew { location } => *location,
            CompileError::EnumCtorsNotSurjective {
                term_location,
                enum_name: _,
                enum_location: _,
            } => *term_location,
            CompileError::MatchPatternIsVariable { location } => *location,
            CompileError::MatchConflictingEnum {
                match_stmt_location,
                ..
            } => *match_stmt_location,
            CompileError::MatchPatternIsWildcard { location } => *location,
            CompileError::MatchPatternCtorArgIsApp { location } => *location,
            CompileError::MatchPatternArgVarIsNotFresh { location } => *location,
            CompileError::MatchNotExhaustive { match_location, .. } => *match_location,
            CompileError::IllegalMemberTypeExprInArgDecl { location } => *location,
        }
    }
}

/// [CompileError] is sorted according to *reverse* priority with respect to reporting:
/// A smaller [CompileError] should be reported preferably over a larger one.
///
/// TODO: This is confusing, should revert the order. It is currently this way to be compatible
/// with location ordering, where lower locations take precedence over greater ones.
impl Ord for CompileError {
    fn cmp(&self, other: &Self) -> Ordering {
        use CompileError::*;
        if self == other {
            return Ordering::Equal;
        }

        // An earlier (lower) location has higher priority.
        let loc_cmp = self.primary_location().1.cmp(&other.primary_location().1);

        // TODO: Far from complete. We probably want to group errors into e.g. parse errors, symbol
        // lookup errors, inference errors etc and define orders separately and then implement the
        // ordering hierarchically: First within a group, then among groups.
        match (self, other) {
            (UndeclaredSymbol { .. }, UndeclaredSymbol { .. }) => loc_cmp,
            (UndeclaredSymbol { .. }, _) => Ordering::Less,
            (SymbolDeclaredTwice { .. }, SymbolDeclaredTwice { .. }) => loc_cmp,
            (SymbolDeclaredTwice { .. }, _) => Ordering::Less,
            (BadSymbolKind { .. }, BadSymbolKind { .. }) => loc_cmp,
            (BadSymbolKind { .. }, _) => Ordering::Less,
            (UndeterminedTermType { .. }, UndeterminedTermType { .. }) => loc_cmp,
            // TODO: Is that what we want necessarily? This is here because when there are
            // conflicting enum constructors in a match statement, then we necessarily infer
            // different types for the discriminee (it must be equal to both enums). The root cause
            // is the conflicting enum constructors though, so it's better to report that one. But
            // if the ConflictingTermType is not the discriminee but something unrelated, then it'd
            // be better to compare by location.
            (ConflictingTermType { .. }, MatchConflictingEnum { .. }) => Ordering::Greater,
            (_, _) => loc_cmp,
        }
    }
}

impl PartialOrd for CompileError {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
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
                let symbol_kind = display_symbol_kind(*symbol_kind);
                write!(f, "{symbol_kind} \"{name}\" is not UpperCamelCase\n")?;
                write_loc(f, *location)?;
            }
            SymbolNotSnakeCase {
                name,
                location,
                symbol_kind,
            } => {
                let symbol_kind = display_symbol_kind(*symbol_kind);
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
                let expected = display_symbol_kind(*expected);
                let found = display_symbol_kind(*found);
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
            EnumCtorsNotSurjective {
                term_location,
                enum_name,
                enum_location,
            } => {
                write!(
                    f,
                    "term of enum type \"{enum_name}\" is not introduced with constructor \n"
                )?;
                write_loc(f, *term_location)?;
                write!(f, "Enum \"{enum_name}\" declared here:\n")?;
                write_loc(f, *enum_location)?;
            }
            MatchPatternIsVariable { location } => {
                write!(f, "Pattern is a variable\n")?;
                write_loc(f, *location)?;
                write!(
                    f,
                    "Patterns must be given by constructors of an enum type\n"
                )?;
            }
            MatchPatternIsWildcard { location } => {
                write!(f, "Pattern is a wildcard\n")?;
                write_loc(f, *location)?;
                write!(
                    f,
                    "Patterns must be given by constructors of an enum type\n"
                )?;
            }
            MatchPatternCtorArgIsApp { location } => {
                write!(f, "Nested patterns are not supported yet\n")?;
                write_loc(f, *location)?;
                write!(f, "Only variables may occur as arguments\n")?;
            }
            MatchPatternArgVarIsNotFresh { location } => {
                write!(f, "Variable in pattern has been used before\n")?;
                write_loc(f, *location)?;
                write!(f, "Variables in patterns must be fresh\n")?;
            }
            MatchConflictingEnum {
                match_stmt_location,
                first_ctor_decl_location,
                second_ctor_decl_location,
            } => {
                write!(f, "Conflicting pattern types\n")?;
                write_loc(f, *match_stmt_location)?;
                write!(f, "Constructors belong to different enums:\n")?;
                write_loc(f, *first_ctor_decl_location)?;
                write_loc(f, *second_ctor_decl_location)?;
            }
            MatchNotExhaustive {
                match_location,
                missing_ctor_decl_location,
            } => {
                write!(f, "Missing match case:\n")?;
                write_loc(f, *match_location)?;
                write!(f, "This constructor is not covered:\n")?;
                write_loc(f, *missing_ctor_decl_location)?;
            }
            IllegalMemberTypeExprInArgDecl { location } => {
                write!(
                    f,
                    "Member type expressions not allowed in function/predicate arguments\n"
                )?;
                write_loc(f, *location)?;
            }
        }
        Ok(())
    }
}

impl Error for CompileErrorWithContext {}

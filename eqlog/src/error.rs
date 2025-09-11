use crate::grammar_util::*;
use crate::source_display::*;
use eqlog_eqlog::*;
use lalrpop_util::{lexer::Token, ParseError};
use std::cmp::Ordering;
use std::collections::HashSet;
use std::error::Error;
use std::fmt::{self, Display};
use std::path::PathBuf;
use std::sync::LazyLock;
use strum::IntoEnumIterator as _;
use strum_macros::EnumIter;

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
    MatchPatternIsMemberFunc {
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
            CompileError::MatchPatternIsMemberFunc { location } => *location,
        }
    }
}

#[derive(Copy, Clone, PartialEq, Eq, Hash, Debug, EnumIter)]
pub enum CompileErrorKind {
    InvalidToken,
    UnrecognizedEOF,
    UnrecognizedToken,
    ExtraToken,
    SymbolNotCamelCase,
    SymbolNotSnakeCase,
    VariableNotSnakeCase,
    VariableOccursOnlyOnce,
    FunctionArgumentNumber,
    PredicateArgumentNumber,
    UndeclaredSymbol,
    BadSymbolKind,
    SymbolDeclaredTwice,
    UndeterminedTermType,
    ConflictingTermType,
    VariableIntroducedInThenStmt,
    WildcardInThenStmt,
    SurjectivityViolation,
    ThenDefinedNotVar,
    ThenDefinedVarNotNew,
    EnumCtorsNotSurjective,
    MatchPatternIsVariable,
    MatchPatternIsWildcard,
    MatchPatternCtorArgIsApp,
    MatchPatternArgVarIsNotFresh,
    MatchConflictingEnum,
    MatchNotExhaustive,
    IllegalMemberTypeExprInArgDecl,
    MatchPatternIsMemberFunc,
}

impl From<&CompileError> for CompileErrorKind {
    fn from(value: &CompileError) -> Self {
        use CompileError::*;
        match value {
            InvalidToken { .. } => CompileErrorKind::InvalidToken,
            UnrecognizedEOF { .. } => CompileErrorKind::UnrecognizedEOF,
            UnrecognizedToken { .. } => CompileErrorKind::UnrecognizedToken,
            ExtraToken { .. } => CompileErrorKind::ExtraToken,
            SymbolNotCamelCase { .. } => CompileErrorKind::SymbolNotCamelCase,
            SymbolNotSnakeCase { .. } => CompileErrorKind::SymbolNotSnakeCase,
            VariableNotSnakeCase { .. } => CompileErrorKind::VariableNotSnakeCase,
            VariableOccursOnlyOnce { .. } => CompileErrorKind::VariableOccursOnlyOnce,
            FunctionArgumentNumber { .. } => CompileErrorKind::FunctionArgumentNumber,
            PredicateArgumentNumber { .. } => CompileErrorKind::PredicateArgumentNumber,
            UndeclaredSymbol { .. } => CompileErrorKind::UndeclaredSymbol,
            BadSymbolKind { .. } => CompileErrorKind::BadSymbolKind,
            SymbolDeclaredTwice { .. } => CompileErrorKind::SymbolDeclaredTwice,
            UndeterminedTermType { .. } => CompileErrorKind::UndeterminedTermType,
            ConflictingTermType { .. } => CompileErrorKind::ConflictingTermType,
            VariableIntroducedInThenStmt { .. } => CompileErrorKind::VariableIntroducedInThenStmt,
            WildcardInThenStmt { .. } => CompileErrorKind::WildcardInThenStmt,
            SurjectivityViolation { .. } => CompileErrorKind::SurjectivityViolation,
            ThenDefinedNotVar { .. } => CompileErrorKind::ThenDefinedNotVar,
            ThenDefinedVarNotNew { .. } => CompileErrorKind::ThenDefinedVarNotNew,
            EnumCtorsNotSurjective { .. } => CompileErrorKind::EnumCtorsNotSurjective,
            MatchPatternIsVariable { .. } => CompileErrorKind::MatchPatternIsVariable,
            MatchPatternIsWildcard { .. } => CompileErrorKind::MatchPatternIsWildcard,
            MatchPatternCtorArgIsApp { .. } => CompileErrorKind::MatchPatternCtorArgIsApp,
            MatchPatternArgVarIsNotFresh { .. } => CompileErrorKind::MatchPatternArgVarIsNotFresh,
            MatchConflictingEnum { .. } => CompileErrorKind::MatchConflictingEnum,
            MatchNotExhaustive { .. } => CompileErrorKind::MatchNotExhaustive,
            IllegalMemberTypeExprInArgDecl { .. } => {
                CompileErrorKind::IllegalMemberTypeExprInArgDecl
            }
            MatchPatternIsMemberFunc { .. } => CompileErrorKind::MatchPatternIsMemberFunc,
        }
    }
}

fn transitive_closure(relation: &mut HashSet<[CompileErrorKind; 2]>) {
    loop {
        let mut new_tuples: Vec<[CompileErrorKind; 2]> = Vec::new();
        for [a, b] in relation.iter().copied() {
            for [c, d] in relation.iter().copied() {
                if b != c {
                    continue;
                }

                if !relation.contains(&[a, d]) {
                    new_tuples.push([a, d]);
                }
            }
        }

        if new_tuples.is_empty() {
            break;
        }

        for [a, d] in new_tuples {
            assert!(
                a == d || !relation.contains(&[d, a]),
                "Cycle in < relation for compile error kind"
            );
            relation.insert([a, d]);
        }
    }
}

// This is the transitive closure over a generator set of tuples and not necessarily total.
static COMPILE_ERROR_KIND_ORDER: LazyLock<HashSet<[CompileErrorKind; 2]>> = LazyLock::new(|| {
    use CompileErrorKind::*;

    let mut relation: HashSet<[CompileErrorKind; 2]> =
        CompileErrorKind::iter().map(|k| [k, k]).collect();

    // UndeclaredSymbol takes precedence over everything.
    relation.extend(CompileErrorKind::iter().map(|k| [UndeclaredSymbol, k]));
    transitive_closure(&mut relation);

    // SymbolDeclaredTwice is next.
    for k in CompileErrorKind::iter() {
        if !relation.contains(&[k, SymbolDeclaredTwice]) {
            relation.insert([SymbolDeclaredTwice, k]);
        }
    }
    transitive_closure(&mut relation);

    // SymbolDeclaredTwice is next.
    for k in CompileErrorKind::iter() {
        if !relation.contains(&[k, BadSymbolKind]) {
            relation.insert([BadSymbolKind, k]);
        }
    }
    transitive_closure(&mut relation);

    for k in CompileErrorKind::iter() {
        if !relation.contains(&[k, UndeterminedTermType]) {
            relation.insert([UndeterminedTermType, k]);
        }
    }
    transitive_closure(&mut relation);

    relation.insert([MatchConflictingEnum, ConflictingTermType]);
    transitive_closure(&mut relation);

    relation
});

impl PartialOrd for CompileErrorKind {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        if self == other {
            return Some(Ordering::Equal);
        }

        let compile_error_kind_order = LazyLock::force(&COMPILE_ERROR_KIND_ORDER);
        if compile_error_kind_order.contains(&[*self, *other]) {
            return Some(Ordering::Less);
        }

        if compile_error_kind_order.contains(&[*other, *self]) {
            return Some(Ordering::Greater);
        }

        None
    }
}

/// [CompileError] is sorted according to *reverse* priority with respect to reporting:
/// A smaller [CompileError] should be reported preferably over a larger one.
///
/// TODO: This is confusing, should revert the order. It is currently this way to be compatible
/// with location ordering, where lower locations take precedence over greater ones.
impl Ord for CompileError {
    fn cmp(&self, other: &Self) -> Ordering {
        if self == other {
            return Ordering::Equal;
        }

        let self_kind = CompileErrorKind::from(self);
        let other_kind = CompileErrorKind::from(other);

        if let Some(ordering) = self_kind.partial_cmp(&other_kind) {
            return ordering;
        }

        // If the error kinds are not comparable, compare by location.
        self.primary_location().1.cmp(&other.primary_location().1)
    }
}

impl PartialOrd for CompileError {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
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
            MatchPatternIsMemberFunc { location } => {
                write!(
                    f,
                    "Member function expressions not allowed in match patterns\n"
                )?;
                write_loc(f, *location)?;
                write!(
                    f,
                    "Only constructors (ambient functions) may be used in patterns\n"
                )?;
            }
        }
        Ok(())
    }
}

impl Error for CompileErrorWithContext {}

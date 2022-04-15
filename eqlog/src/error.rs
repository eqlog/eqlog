use crate::ast::*;
use lalrpop_util::{lexer::Token, ParseError};
use std::error::Error;
use std::fmt::{self, Display};
use std::path::{Path, PathBuf};

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
    },
    VariableNotSnakeCase {
        name: String,
        location: Option<Location>,
    },
    VariableOccursOnlyOnce {
        name: String,
        location: Option<Location>,
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
    BadSymbolKind {
        name: String,
        expected: SymbolKind,
        found: SymbolKind,
        used_location: Option<Location>,
        declared_location: Option<Location>,
    },
    SymbolDeclaredTwice {
        name: String,
        first_declaration: Option<Location>,
        second_declaration: Option<Location>,
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
            ParseError::UnrecognizedEOF { location, expected } => CompileError::UnrecognizedEOF {
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

#[derive(Copy, Clone, PartialEq, Eq, Hash, Debug)]
struct DisplayLocation<'a> {
    source_path: &'a Path,
    source: &'a str,
    location: Option<Location>,
}

impl<'a> Display for DisplayLocation<'a> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let DisplayLocation {
            source_path,
            source,
            location,
        } = *self;
        let (begin, end) = match location {
            Some(Location(begin, end)) => (begin, end),
            None => (0, 0),
        };

        let line_ranges = source.lines().scan(0, |len, line| {
            let b = *len;
            // TODO: Or line.chars().count()?
            *len += line.len();
            let e = *len;
            // TODO: Doesn't work with \n\r newlines.
            *len += 1;
            Some((b, e))
        });

        // An iterator over (line_number: usize, (line_begin: usize , line_end: usize)) over all
        // lines that intersect location.
        let intersecting_line_ranges = line_ranges
            .enumerate()
            .skip_while(|(_, (_, e))| *e <= begin)
            .take_while(|(_, (b, _))| *b < end)
            .map(|(i, r)| (i + 1, r));

        // Digits of the largest line number we need to display.
        let max_line_num_digits: usize =
            match itertools::max(intersecting_line_ranges.clone().map(|(i, _)| i)) {
                Some(max) => max.to_string().len(),
                None => 0,
            };

        let write_padding = |f: &mut fmt::Formatter, n: usize| -> fmt::Result {
            for _ in 0..n {
                write!(f, " ")?;
            }
            Ok(())
        };

        write_padding(f, max_line_num_digits)?;
        write!(f, "--> {}", source_path.display())?;
        if let Some(first_line) = intersecting_line_ranges.clone().next().map(|(i, _)| i) {
            write!(f, ":{first_line}")?;
        }
        write!(f, "\n")?;

        write_padding(f, max_line_num_digits)?;
        write!(f, " | \n")?;

        for (i, (b, e)) in intersecting_line_ranges {
            let line_num_str = i.to_string();
            write_padding(f, max_line_num_digits - line_num_str.len())?;
            write!(f, "{line_num_str} | ")?;
            write!(f, "{}\n", &source[b..e])?;

            write_padding(f, max_line_num_digits)?;
            write!(f, " | ")?;
            for i in b..e {
                if i < begin || i >= end {
                    write!(f, " ")?;
                } else {
                    write!(f, "^")?;
                }
            }
            write!(f, "\n")?;
        }

        write_padding(f, max_line_num_digits)?;
        write!(f, " | \n")?;

        Ok(())
    }
}

fn display_location<'a>(
    source_path: &'a Path,
    source: &'a str,
    location: Option<Location>,
) -> impl 'a + Display + Copy {
    DisplayLocation {
        source_path,
        source,
        location,
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
        write!(f, "Error: ")?;
        match error {
            InvalidToken { location } => {
                write!(f, "invalid token\n")?;
                write!(
                    f,
                    "{}",
                    display_location(source_path, source, Some(*location))
                )?;
            }
            UnrecognizedEOF {
                location,
                expected: _,
            } => {
                write!(f, "unexpected end of file\n")?;
                write!(
                    f,
                    "{}",
                    display_location(source_path, source, Some(*location))
                )?;
            }
            UnrecognizedToken {
                location,
                expected: _,
            } => {
                write!(f, "unrecognized token\n")?;
                write!(
                    f,
                    "{}",
                    display_location(source_path, source, Some(*location))
                )?;
            }
            ExtraToken { location } => {
                write!(f, "unexpected token\n")?;
                write!(
                    f,
                    "{}",
                    display_location(source_path, source, Some(*location))
                )?;
            }
            SymbolNotCamelCase { name, location } => {
                write!(f, "symbol {name} is not UpperCamelCase\n")?;
                display_location(source_path, source, *location).fmt(f)?;
            }
            VariableNotSnakeCase { name, location } => {
                write!(f, "variable {name} is not lower_snake_case\n")?;
                display_location(source_path, source, *location).fmt(f)?;
            }
            VariableOccursOnlyOnce { name, location } => {
                write!(f, "variable {name} occurs only once\n")?;
                display_location(source_path, source, *location).fmt(f)?;
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
                write!(f, "{}", display_location(source_path, source, *location))?;
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
                write!(f, "{}", display_location(source_path, source, *location))?;
            }
            UndeclaredSymbol { name, location } => {
                write!(f, "undeclared symbol \"{name}\"\n")?;
                write!(f, "{}", display_location(source_path, source, *location))?;
            }
            BadSymbolKind {
                name,
                expected,
                found,
                used_location,
                declared_location,
            } => {
                write!(f, "expected {expected}, found {found} {name}\n")?;
                if used_location.is_some() {
                    display_location(source_path, source, *used_location).fmt(f)?;
                }
                if declared_location.is_some() {
                    write!(f, "{name} declared as {found} here:\n")?;
                    display_location(source_path, source, *declared_location).fmt(f)?;
                }
            }
            SymbolDeclaredTwice {
                name: _,
                first_declaration,
                second_declaration,
            } => {
                write!(f, "symbol declared multiple times\n")?;
                write!(
                    f,
                    "{}",
                    display_location(source_path, source, *second_declaration)
                )?;
                if first_declaration.is_some() {
                    write!(f, "Previously declared here:\n")?;
                    write!(
                        f,
                        "{}\n\n",
                        display_location(source_path, source, *first_declaration)
                    )?;
                }
            }
            ReductionFromVariableOrWildcard { location } => {
                write!(f, "term before ~> cannot be variable or wildcard\n")?;
                write!(f, "{}", display_location(source_path, source, *location))?;
            }
            NoSort { location } => {
                write!(f, "sort of term undetermined\n")?;
                write!(f, "{}", display_location(source_path, source, *location))?;
            }
            ConflictingSorts { sorts: _, location } => {
                write!(f, "term has conflicting sorts\n")?;
                write!(f, "{}", display_location(source_path, source, *location))?;
            }
            VariableNotInPremise { var: _, location } => {
                write!(f, "variable in conclusion not used in premise\n")?;
                write!(f, "{}", display_location(source_path, source, *location))?;
            }
            WildcardInConclusion { location } => {
                write!(f, "wildcard in conclusion\n")?;
                write!(f, "{}", display_location(source_path, source, *location))?;
            }
            ConclusionEqualityOfNewTerms { location } => {
                write!(
                    f,
                    "both sides of equality in conclusion are not used earlier\n"
                )?;
                write!(f, "{}", display_location(source_path, source, *location))?;
            }
            ConclusionEqualityArgNew { location } => {
                write!(
                    f,
                    "argument of undefined term in equality in conclusion is not used earlier\n"
                )?;
                write!(f, "{}", display_location(source_path, source, *location))?;
            }
            ConclusionPredicateArgNew { location } => {
                write!(f, "argument of predicate in conclusion is not used earlier")?;
                write!(f, "{}", display_location(source_path, source, *location))?;
            }
        }
        Ok(())
    }
}

impl Error for CompileErrorWithContext {}

use crate::ast::*;
use lalrpop_util::{lexer::Token, ParseError};
use std::error::Error;
use std::fmt::{self, Display};
use std::path::{Path, PathBuf};

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

#[derive(Copy, Clone, PartialEq, Eq, Hash, Debug)]
struct FormatLocation<'a> {
    source_path: &'a Path,
    source: &'a str,
    location: Location,
}

impl<'a> Display for FormatLocation<'a> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let FormatLocation {
            source_path,
            source,
            location,
        } = *self;
        let Location(begin, end) = location;

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
    location: Location,
) -> impl 'a + Display + Copy {
    FormatLocation {
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
        match error {
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
                location,
            } => {
                write!(
                    f,
                    "Function takes {expected} arguments but {got} were supplied\n"
                )?;
                if let Some(loc) = *location {
                    write!(f, "{}", display_location(source_path, source, loc))?;
                }
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

impl Error for CompileErrorWithContext {}

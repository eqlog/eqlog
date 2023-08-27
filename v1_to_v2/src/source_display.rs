use std::cmp::{max, min};
use std::fmt::{self, Display};
use std::path::Path;

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug, PartialOrd, Ord)]
pub struct Location(pub usize, pub usize);

impl Location {
    fn is_empty(self) -> bool {
        self.0 == self.1
    }
    fn intersect(self, other: Self) -> Option<Self> {
        let begin = max(self.0, other.0);
        let end = min(self.1, other.1);
        if !self.is_empty() && !other.is_empty() {
            // For non-empty locations, we only consider non-empty intersections.
            if begin < end {
                Some(Location(begin, end))
            } else {
                None
            }
        } else {
            debug_assert!(self.is_empty() || other.is_empty());
            // We return a valid location also in cases where an empty location points to right
            // before or right after a non-empty location.
            if begin <= end {
                Some(Location(begin, end))
            } else {
                None
            }
        }
    }
}

fn line_locations<'a>(source: &'a str) -> impl 'a + Clone + Iterator<Item = Location> {
    source.lines().scan(0, |pos, line| {
        let begin = *pos;
        // TODO: Or line.chars().count()?
        *pos += line.len();
        let end = *pos;
        // TODO: Doesn't work with \n\r newlines.
        *pos += 1;
        Some(Location(begin, end))
    })
}

// An iterator over all lines that intersect a given location. The iterator yields pairs consisting
// of the zero-based line index and the location of the full row.
fn intersecting_line_locations<'a>(
    location: Location,
    source: &'a str,
) -> impl 'a + Clone + Iterator<Item = (usize, Location)> {
    let intersects = move |line_loc: Location| -> bool { line_loc.intersect(location).is_some() };
    line_locations(source)
        .enumerate()
        .skip_while(move |(_, line_loc)| !intersects(*line_loc))
        .take_while(move |(_, line_loc)| intersects(*line_loc))
}

#[derive(Copy, Clone, PartialEq, Eq, Hash, Debug)]
pub struct SourceDisplay<'a> {
    pub source: &'a str,
    pub location: Location,
    pub source_path: Option<&'a Path>,
    pub underlined: bool,
}

impl<'a> SourceDisplay<'a> {
    pub fn new(source: &'a str, location: Location) -> Self {
        Self {
            source_path: None,
            source,
            location,
            underlined: false,
        }
    }
}

pub fn source_path_pointer(source_path: &Path) -> impl Clone + Display {
    format!("--> {}", source_path.display())
}

impl<'a> Display for SourceDisplay<'a> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let Self {
            source,
            location,
            source_path,
            underlined,
        } = *self;

        let nums_locs = intersecting_line_locations(location, source).map(|(i, loc)| (i + 1, loc));

        // Digits of the largest line number we need to display.
        let max_line_num_digits: usize = match itertools::max(nums_locs.clone().map(|(n, _)| n)) {
            Some(max) => max.to_string().len(),
            None => panic!("Location is empty or does not map to source"),
        };

        let write_padding = |f: &mut fmt::Formatter, n: usize| -> fmt::Result {
            for _ in 0..n {
                write!(f, " ")?;
            }
            Ok(())
        };

        if let Some(source_path) = source_path {
            let source_path = source_path_pointer(source_path);
            let (first_num, _) = nums_locs.clone().next().unwrap();
            write_padding(f, max_line_num_digits)?;
            write!(f, "{source_path}:{first_num}\n")?;
        }
        write_padding(f, max_line_num_digits)?;
        write!(f, " | \n")?;

        for (num, line_loc) in nums_locs {
            let line_num_str = num.to_string();
            write_padding(f, max_line_num_digits - line_num_str.len())?;
            write!(f, "{line_num_str} | ")?;
            let Location(line_begin, line_end) = line_loc;
            write!(f, "{}\n", &source[line_begin..line_end])?;

            if underlined {
                write_padding(f, max_line_num_digits)?;
                write!(f, " | ")?;
                for i in line_begin..line_end {
                    if Location(i, i + 1).intersect(location).is_some() {
                        write!(f, "^")?;
                    } else {
                        write!(f, " ")?;
                    }
                }
                write!(f, "\n")?;
            }
        }

        write_padding(f, max_line_num_digits)?;
        write!(f, " | \n")?;

        Ok(())
    }
}

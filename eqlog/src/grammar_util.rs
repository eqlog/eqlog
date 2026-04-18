use std::cmp::{max, min};

// TODO: Use rust's built-in never type ! once it is stabilized.
pub enum NeverType {}

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub struct Location(pub usize, pub usize);

impl Location {
    pub fn is_empty(self) -> bool {
        self.0 == self.1
    }
    pub fn intersect(self, other: Self) -> Option<Self> {
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

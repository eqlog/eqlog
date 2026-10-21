use std::ops::RangeInclusive;
use std::rc::Rc;

use crate::PrefixTree2;

#[derive(Clone, Debug, Eq, PartialEq)]
struct Run {
    source: u32,
    target: u32,
    last: u32,
}

/// An injective, increasing partial map, compressed into contiguous offset runs.
#[derive(Clone, Debug)]
pub struct MonotoneMap {
    runs: Rc<[Run]>,
    // Composed offsets use bounded run contents without retaining origin chains.
    relation: PrefixTree2,
}

impl MonotoneMap {
    /// Prepares arithmetic image blocks without allocating their individual rows.
    /// Each pair gives an inclusive source range and the image of its first key.
    /// Source and image ranges must be nonempty, disjoint, and increasing.
    pub fn from_offsets(
        offsets: impl IntoIterator<Item = (RangeInclusive<u32>, u32)>,
    ) -> Option<Self> {
        let mut runs: Vec<Run> = Vec::new();
        for (source, target) in offsets {
            if source.is_empty() {
                return None;
            }
            let first = *source.start();
            let last = *source.end();
            let length = last.checked_sub(first)?;
            target.checked_add(length)?;
            if let Some(previous) = runs.last_mut() {
                let last_target = previous.target + (previous.last - previous.source);
                if first <= previous.last || target <= last_target {
                    return None;
                }
                if previous.last.checked_add(1) == Some(first)
                    && last_target.checked_add(1) == Some(target)
                {
                    previous.last = last;
                    continue;
                }
            }
            runs.push(Run {
                source: first,
                target,
                last,
            });
        }
        Some(Self {
            runs: runs.into(),
            relation: PrefixTree2::new(),
        })
    }

    pub fn new(relation: &PrefixTree2) -> Option<Self> {
        let mut runs: Vec<Run> = Vec::new();
        for [source, target] in relation.iter() {
            if let Some(previous) = runs.last_mut() {
                let last_target = previous.target + (previous.last - previous.source);
                if source <= previous.last || target <= last_target {
                    return None;
                }
                if previous.last.checked_add(1) == Some(source)
                    && last_target.checked_add(1) == Some(target)
                {
                    previous.last = source;
                    continue;
                }
            }
            runs.push(Run {
                source,
                target,
                last: source,
            });
        }
        Some(Self {
            runs: runs.into(),
            relation: relation.clone(),
        })
    }

    pub fn apply(&self, key: u32) -> Option<u32> {
        let index = self.runs.partition_point(|run| run.last < key);
        let run = self.runs.get(index)?;
        (run.source <= key).then(|| run.target + (key - run.source))
    }

    pub(super) fn map_range(&self, first: u32, last: u32, mut visit: impl FnMut(u32, u32)) {
        let start = self.runs.partition_point(|run| run.last < first);
        for run in &self.runs[start..] {
            if run.source > last {
                break;
            }
            visit(
                run.target + (first.max(run.source) - run.source),
                run.target + (last.min(run.last) - run.source),
            );
        }
    }

    pub fn preimage(&self, key: u32) -> Option<u32> {
        let index = self
            .runs
            .partition_point(|run| run.target + (run.last - run.source) < key);
        let run = self.runs.get(index)?;
        (run.target <= key).then(|| run.source + (key - run.target))
    }

    pub(super) fn source_at_or_after(&self, key: u32) -> Option<u32> {
        let index = self.runs.partition_point(|run| run.last < key);
        self.runs.get(index).map(|run| run.source.max(key))
    }

    pub(super) fn preimage_at_or_after(&self, key: u32) -> Option<u32> {
        let index = self
            .runs
            .partition_point(|run| run.target + (run.last - run.source) < key);
        let run = self.runs.get(index)?;
        Some(run.source + (key.max(run.target) - run.target))
    }

    fn preimage_at_or_before(&self, key: u32) -> Option<u32> {
        let index = self.runs.partition_point(|run| run.target <= key);
        let run = self.runs.get(index.checked_sub(1)?)?;
        Some(run.source + (key - run.target).min(run.last - run.source))
    }

    pub(super) fn preimage_bounds(&self, first: u32, last: u32) -> Option<(u32, u32)> {
        let start = self.runs.first()?;
        let end = self.runs.last()?;
        let first = if first <= start.target {
            Some(start.source)
        } else {
            self.preimage_at_or_after(first)
        };
        let last = if last >= end.target + (end.last - end.source) {
            Some(end.last)
        } else {
            self.preimage_at_or_before(last)
        };
        first.zip(last).filter(|(first, last)| first <= last)
    }

    pub fn run_count(&self) -> usize {
        self.runs.len()
    }

    pub(super) fn bound_domain_len(&self, limit: usize) -> usize {
        if self.relation.map.root_identity() != 0 {
            return limit.min(self.relation.map.len_upper_bound());
        }
        // Composed offsets retain at most one run instead of their source relation.
        // Count in u64 because the full u32 domain contains 2^32 keys.
        let count = self.runs.iter().fold(0u64, |count, run| {
            count + u64::from(run.last - run.source) + 1
        });
        limit.min(usize::try_from(count).unwrap_or(usize::MAX))
    }

    pub(super) fn single_offset(&self) -> Option<u32> {
        if self.runs.len() != 1 {
            return None;
        }
        let run = &self.runs[0];
        Some(run.target.wrapping_sub(run.source))
    }

    pub(super) fn same_snapshot(&self, other: &Self) -> bool {
        if Rc::ptr_eq(&self.runs, &other.runs) {
            return true;
        }
        if self.relation.map.root_identity() == 0 {
            return other.relation.map.root_identity() == 0 && self.runs == other.runs;
        }
        self.relation.map.shares_root(&other.relation.map)
    }

    pub(super) fn compose_offset(&self, inner: &Self) -> Option<Self> {
        if self.runs.len() != 1 || inner.runs.len() != 1 {
            return None;
        }
        let outer = &self.runs[0];
        let inner = &inner.runs[0];
        let first = outer.source.max(inner.target);
        let last = outer.last.min(inner.target + (inner.last - inner.source));
        let runs: Rc<[Run]> = if first <= last {
            Rc::from([Run {
                source: inner.source + (first - inner.target),
                target: outer.target + (first - outer.source),
                last: inner.source + (last - inner.target),
            }])
        } else {
            Rc::from([])
        };
        Some(Self {
            runs,
            relation: PrefixTree2::new(),
        })
    }
}

#[cfg(test)]
mod tests {
    use super::{MonotoneMap, Run};
    use crate::PrefixTree2;
    use std::rc::Rc;

    #[test]
    fn full_domain_cardinality_is_capped_without_overflow() {
        let mapping = MonotoneMap {
            runs: Rc::from([Run {
                source: 0,
                target: 0,
                last: u32::MAX,
            }]),
            relation: PrefixTree2::new(),
        };
        for limit in [0, 1, 1024, usize::MAX] {
            let expected = (limit as u128).min(u128::from(u32::MAX) + 1);
            assert_eq!(mapping.bound_domain_len(limit) as u128, expected);
        }
    }
}

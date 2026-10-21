use std::rc::Rc;

use crate::PrefixTree2;

#[derive(Clone, Debug)]
struct Run {
    source: u32,
    target: u32,
    last: u32,
}

/// An injective, increasing partial map, compressed into contiguous offset runs.
#[derive(Clone, Debug)]
pub struct MonotoneMap {
    runs: Rc<[Run]>,
    relation: PrefixTree2,
}

impl MonotoneMap {
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

    pub(super) fn single_offset(&self) -> Option<u32> {
        if self.runs.len() != 1 {
            return None;
        }
        let run = &self.runs[0];
        Some(run.target.wrapping_sub(run.source))
    }

    pub(super) fn same_snapshot(&self, other: &Self) -> bool {
        self.relation.map.shares_root(&other.relation.map)
    }
}

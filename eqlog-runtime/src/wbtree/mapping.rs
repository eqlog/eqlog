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

    pub fn preimage(&self, key: u32) -> Option<u32> {
        let index = self
            .runs
            .partition_point(|run| run.target + (run.last - run.source) < key);
        let run = self.runs.get(index)?;
        (run.target <= key).then(|| run.source + (key - run.target))
    }

    pub fn run_count(&self) -> usize {
        self.runs.len()
    }

    pub(super) fn same_snapshot(&self, other: &Self) -> bool {
        self.relation.map.shares_root(&other.relation.map)
    }
}

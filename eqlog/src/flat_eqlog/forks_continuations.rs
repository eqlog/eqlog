use std::collections::BTreeMap;

use crate::flat_eqlog::*;
use by_address::ByAddress;

pub struct ForkSuffix<'a> {
    pub fork_stmt: &'a FlatForkStmt,
    pub suffix: &'a [FlatStmt],
}

fn forks_continuations_rec<'a>(
    stmts: &'a [FlatStmt],
    forks: &mut Vec<ForkSuffix<'a>>,
    continuations: &mut BTreeMap<ByAddress<&'a [FlatStmt]>, usize>,
) {
    for (stmt_index, stmt) in stmts.iter().enumerate() {
        let fork_stmt = match stmt {
            FlatStmt::Fork(fork_stmt) => fork_stmt,
            FlatStmt::If(_) | FlatStmt::SurjThen(_) | FlatStmt::NonSurjThen(_) => {
                continue;
            }
        };

        let suffix = &stmts[(stmt_index + 1)..];
        let continuation = forks.len();
        forks.push(ForkSuffix { fork_stmt, suffix });

        for block in fork_stmt.blocks.iter() {
            let empty_block_suffix = &block[block.len()..];
            continuations.insert(ByAddress(empty_block_suffix), continuation);
            forks_continuations_rec(block.as_slice(), forks, continuations);
        }
    }
}

pub fn forks_continuations<'a>(
    rule: &'a FlatRule,
) -> (
    Vec<ForkSuffix<'a>>,
    BTreeMap<ByAddress<&'a [FlatStmt]>, usize>,
) {
    let mut fork_suffixes = Vec::new();
    let mut fork_continuations = BTreeMap::new();
    forks_continuations_rec(
        rule.stmts.as_slice(),
        &mut fork_suffixes,
        &mut fork_continuations,
    );
    (fork_suffixes, fork_continuations)
}

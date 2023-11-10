use std::collections::BTreeMap;

use crate::flat_eqlog::*;
use by_address::ByAddress;

pub struct ForkSuffix<'a> {
    pub fork_stmt: &'a FlatForkStmt,
    pub suffix: &'a [FlatStmt],
}

pub struct ForkContinuations<'a> {
    pub fork_suffixes: Vec<ForkSuffix<'a>>,
    /// A map from the address of an empty suffix of a statement list to an index into
    /// `fork_suffixes`. The indexed [ForkSuffix] is where execution should continue. If
    /// `continuations` does not have an entry for an empty suffix, then execution should halt.
    pub continuations: BTreeMap<ByAddress<&'a [FlatStmt]>, usize>,
}

fn collect_fork_suffixes<'a>(
    stmts: &'a [FlatStmt],
    fork_continuations: &mut ForkContinuations<'a>,
    continuation: Option<usize>,
) {
    for (stmt_index, stmt) in stmts.iter().enumerate() {
        let fork_stmt = match stmt {
            FlatStmt::Fork(fork_stmt) => fork_stmt,
            FlatStmt::If(_) | FlatStmt::SurjThen(_) | FlatStmt::NonSurjThen(_) => {
                continue;
            }
        };

        let suffix = &stmts[(stmt_index + 1)..];
        fork_continuations
            .fork_suffixes
            .push(ForkSuffix { fork_stmt, suffix });
        if let Some(continuation) = continuation {
            fork_continuations
                .continuations
                .insert(ByAddress(&suffix[suffix.len()..]), continuation);
        }

        let continuation = fork_continuations.fork_suffixes.len() - 1;

        for block in fork_stmt.blocks.iter() {
            collect_fork_suffixes(block.as_slice(), fork_continuations, Some(continuation));
        }
    }
}

pub fn fork_continuations_pass<'a>(rule: &'a FlatRule) -> ForkContinuations<'a> {
    let mut fork_continuations = ForkContinuations {
        fork_suffixes: Vec::new(),
        continuations: BTreeMap::new(),
    };
    collect_fork_suffixes(rule.stmts.as_slice(), &mut fork_continuations, None);
    fork_continuations
}

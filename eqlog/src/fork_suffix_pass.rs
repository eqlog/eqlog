use crate::flat_eqlog::*;

pub struct ForkSuffix<'a> {
    pub fork_stmt: &'a FlatForkStmt,
    pub suffix: &'a [FlatStmt],
}

pub type ForkSuffixes<'a> = Vec<ForkSuffix<'a>>;

fn collect_fork_suffixes<'a>(stmts: &'a [FlatStmt], suffixes: &mut Vec<ForkSuffix<'a>>) {
    for (i, stmt) in stmts.iter().enumerate() {
        let fork_stmt = match stmt {
            FlatStmt::Fork(fork_stmt) => {
                for block in fork_stmt.blocks.iter() {
                    collect_fork_suffixes(block.as_slice(), suffixes);
                }
                fork_stmt
            }
            FlatStmt::If(_) | FlatStmt::SurjThen(_) | FlatStmt::NonSurjThen(_) => {
                continue;
            }
        };

        let suffix = &stmts[(i + 1)..];
        suffixes.push(ForkSuffix { fork_stmt, suffix });
    }
}

pub fn fork_postfix_pass<'a>(rule: &'a FlatRule) -> Vec<ForkSuffix<'a>> {
    let mut suffixes = Vec::new();
    collect_fork_suffixes(rule.stmts.as_slice(), &mut suffixes);
    suffixes
}

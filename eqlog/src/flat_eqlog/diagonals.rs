use super::ast::*;

fn transform_stmt(stmt: &FlatIfStmt) -> FlatIfStmt {
    let rel = match &stmt.rel {
        FlatInRel::EqlogRel(rel) => *rel,
        FlatInRel::TypeSet(_) | FlatInRel::EqlogRelWithDiagonals { .. } => {
            return stmt.clone();
        }
        FlatInRel::Equality(_) => {
            let [lhs, rhs]: &[FlatVar; 2] = stmt.args.as_slice().try_into().unwrap();
            // Could also transform a diagonal equality into a typeset here, but we're not
            // generating Equality diagonals at the moment, so it shouldn't ever happen anyway.
            assert!(lhs != rhs);
            return stmt.clone();
        }
    };

    let equalities: Vec<usize> = stmt
        .args
        .iter()
        .map(|arg| stmt.args.iter().position(|arg0| arg == arg0).unwrap())
        .collect();

    let args: Vec<FlatVar> = stmt
        .args
        .iter()
        .zip(equalities.iter())
        .enumerate()
        .filter_map(
            |(i, (arg, j))| {
                if i == *j {
                    Some(arg.clone())
                } else {
                    None
                }
            },
        )
        .collect();

    if args.len() == stmt.args.len() {
        // Only trivial equalities.
        return stmt.clone();
    }

    let rel = FlatInRel::EqlogRelWithDiagonals {
        rel,
        equalities: equalities.into(),
    };
    FlatIfStmt {
        rel,
        args: args,
        age: stmt.age,
    }
}

pub fn use_rels_with_diagonals(flat_rule: &mut FlatRule) {
    for stmt in flat_rule.premise.iter_mut() {
        *stmt = transform_stmt(stmt);
    }
}

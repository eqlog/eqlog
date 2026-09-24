use crate::diagonal_canonicalization::*;

#[test]
fn canonicalizing_off_diagonal_predicate_preserves_matching_tuple() {
    for close_before_merge in [false, true] {
        let mut model = DiagonalCanonicalization::new();
        let x = model.new_t();
        let y = model.new_t();
        let a = model.new_t();
        let b = model.new_t();
        model.insert_pair(x, x, y, y);
        model.insert_pair(x, a, y, y);
        // Prefer b as the representative so only the off-diagonal tuple changes.
        model.insert_pair(b, b, b, b);
        if close_before_merge {
            model.close();
        }

        model.equate_t(b, a);
        assert_eq!(model.root_t(a), b);
        model.canonicalize();
        model.canonicalize();
        model.insert_gate();
        model.close();

        assert!(model.pair(x, x, y, y));
        assert!(model.pair(x, b, y, y));
        assert!(model.matched_pair(x, y));
    }
}

#[test]
fn canonicalizing_off_diagonal_function_preserves_matching_tuple() {
    for close_before_merge in [false, true] {
        let mut model = DiagonalCanonicalization::new();
        let x = model.new_t();
        let y = model.new_t();
        let a = model.new_t();
        let b = model.new_t();
        model.insert_value(x, x, y, y);
        model.insert_value(x, a, y, y);
        // Prefer b as the representative so only the off-diagonal tuple changes.
        model.insert_value(b, b, b, b);
        if close_before_merge {
            model.close();
        }

        model.equate_t(b, a);
        assert_eq!(model.root_t(a), b);
        model.canonicalize();
        model.canonicalize();
        model.insert_gate();
        model.close();

        assert_eq!(model.value(x, x, y), Some(y));
        assert_eq!(model.value(x, b, y), Some(y));
        assert!(model.matched_value(x, y));
    }
}

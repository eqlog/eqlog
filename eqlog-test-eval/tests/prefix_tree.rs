use eqlog_runtime::{
    PrefixTree1, PrefixTree2, PrefixTree3, PrefixTree4, PrefixTree5, PrefixTree6, PrefixTree7,
    PrefixTree8, PrefixTree9,
};

macro_rules! restriction_tests {
    ($name:ident, $tree:ident, $restriction:ident, $arity:expr) => {
        #[test]
        fn $name() {
            let mut tree = $tree::new();
            tree.insert_restriction(0, $restriction::new());
            assert!(tree.is_empty());
            assert!(tree.get(0).is_none());
            assert_eq!(tree.iter_restrictions().count(), 0);

            let mut restriction = $restriction::new();
            restriction.insert([1; $arity - 1]);
            tree.insert_restriction(0, restriction.clone());
            assert_eq!(tree.iter().count(), 1);
            tree.remove_restriction(0, &restriction);
            assert!(tree.is_empty());
            assert!(tree.get(0).is_none());
            assert_eq!(tree.iter_restrictions().count(), 0);
        }
    };
}

restriction_tests!(binary_restrictions, PrefixTree2, PrefixTree1, 2);
restriction_tests!(ternary_restrictions, PrefixTree3, PrefixTree2, 3);
restriction_tests!(arity_4_restrictions, PrefixTree4, PrefixTree3, 4);
restriction_tests!(arity_5_restrictions, PrefixTree5, PrefixTree4, 5);
restriction_tests!(arity_6_restrictions, PrefixTree6, PrefixTree5, 6);
restriction_tests!(arity_7_restrictions, PrefixTree7, PrefixTree6, 7);
restriction_tests!(arity_8_restrictions, PrefixTree8, PrefixTree7, 8);
restriction_tests!(arity_9_restrictions, PrefixTree9, PrefixTree8, 9);

#[test]
fn filtering_a_later_column_does_not_leave_empty_prefixes() {
    let mut tree = PrefixTree3::new();
    tree.insert([1, 2, 3]);
    let mapped = tree.mapped(None, None, Some(PrefixTree2::new()));
    assert!(mapped.is_empty());
    assert!(mapped.get(1).is_none());
    assert_eq!(mapped.iter_restrictions().count(), 0);
}

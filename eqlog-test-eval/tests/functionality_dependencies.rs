macro_rules! functionality_dependencies_tests {
    ($variant:ident, $direct:ident, $cascade:ident) => {
        mod $variant {
            mod direct {
                include!(concat!(
                    env!("OUT_DIR"),
                    "/functionality_dependencies/",
                    stringify!($variant),
                    "/direct_",
                    stringify!($variant),
                    ".eql.rs"
                ));
            }

            mod cascade {
                include!(concat!(
                    env!("OUT_DIR"),
                    "/functionality_dependencies/",
                    stringify!($variant),
                    "/cascade_",
                    stringify!($variant),
                    ".eql.rs"
                ));
            }

            #[test]
            fn a_derived_function_conflict_enables_a_predicate_join() {
                for close_before_conflict in [false, true] {
                    let mut model = direct::$direct::new();
                    let a = model.new_el();
                    let b = model.new_el();
                    let c = model.new_el();
                    model.insert_f(a, b);
                    model.insert_p(b);
                    model.insert_q(c);
                    if close_before_conflict {
                        model.close();
                        assert!(!model.hit());
                    }
                    assert!(!model.are_equal_el(b, c));

                    model.insert_seed(a, c);
                    model.close();
                    assert!(model.are_equal_el(b, c));
                    assert!(model.hit());
                }
            }

            #[test]
            fn a_function_conflict_preserves_pending_joins_after_interruption() {
                let mut model = direct::$direct::new();
                let a = model.new_el();
                let b = model.new_el();
                let c = model.new_el();
                model.insert_f(a, b);
                model.insert_p(b);
                model.insert_q(c);
                model.close();
                assert!(!model.hit());

                model.insert_seed(a, c);
                assert!(model.close_until(|model| model.are_equal_el(b, c)));
                model.close();
                assert!(model.hit());
            }

            #[test]
            fn derived_equality_enables_joins_after_cascading_function_conflicts() {
                for close_before_merge in [false, true] {
                    let mut model = cascade::$cascade::new();
                    let a = model.new_source();
                    let b = model.new_source();
                    let c = model.new_middle();
                    let d = model.new_middle();
                    let e = model.new_target();
                    let f = model.new_target();
                    model.insert_to_middle(a, c);
                    model.insert_to_middle(b, d);
                    model.insert_to_target(c, e);
                    model.insert_to_target(d, f);
                    model.insert_left(e);
                    model.insert_right(f);
                    if close_before_merge {
                        model.close();
                        assert!(!model.hit());
                    }
                    assert!(!model.are_equal_source(a, b));
                    assert!(!model.are_equal_middle(c, d));
                    assert!(!model.are_equal_target(e, f));

                    model.insert_merge(a, b);
                    model.close();
                    assert!(model.are_equal_source(a, b));
                    assert!(model.are_equal_middle(c, d));
                    assert!(model.are_equal_target(e, f));
                    assert!(model.hit());
                }
            }
        }
    };
}

functionality_dependencies_tests!(native_naive, DirectNativeNaive, CascadeNativeNaive);
functionality_dependencies_tests!(
    native_seminaive,
    DirectNativeSeminaive,
    CascadeNativeSeminaive
);
functionality_dependencies_tests!(desugared_naive, DirectDesugaredNaive, CascadeDesugaredNaive);
functionality_dependencies_tests!(
    desugared_seminaive,
    DirectDesugaredSeminaive,
    CascadeDesugaredSeminaive
);

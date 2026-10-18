use eqlog_test_eval as _;

include!(concat!(
    env!("EQLOG_OUT_DIR"),
    "/eqlog-test-eval/src/functionality_star.eql.rs"
));

// Desugared tables equate a second function result on insertion instead of
// running functionality rules.
#[cfg(not(feature = "desugared"))]
#[test]
fn functionality_emits_a_linear_number_of_equalities_per_domain() {
    let mut rows = PrefixTree3::new();
    for result in 0..128 {
        rows.insert([10, 11, result]);
    }
    for result in 200..208 {
        rows.insert([10, 12, result]);
    }
    let mut output = Vec::new();
    functionality_choose(FunctionalityChooseEnv {
        phantom: std::marker::PhantomData,
        __canonical_el: &[true; 208],
        choose_new_order_0_1_2: &rows,
        choose_old_order_0_1_2: PrefixTree3::empty(),
        new_el_equalities: &mut output,
    });
    assert_eq!(output.len(), 127 + 7);
    for [left, right] in output {
        assert!(left < 128 && right < 128 || left >= 200 && right >= 200);
    }
}

#[cfg(not(feature = "desugared"))]
#[test]
fn functionality_skips_obsolete_anchors_before_choosing_a_result() {
    for old_results in [vec![0, 1], vec![0]] {
        let mut old = PrefixTree3::new();
        for &result in &old_results {
            old.insert([10, 11, result]);
        }
        let mut new = PrefixTree3::new();
        new.insert([10, 11, 2]);
        let expected = if old_results.len() == 2 {
            vec![[2, 1]]
        } else {
            new.insert([10, 11, 3]);
            vec![[3, 2]]
        };
        let mut canonical = [true; 12];
        canonical[0] = false;
        let mut output = Vec::new();
        functionality_choose(FunctionalityChooseEnv {
            phantom: std::marker::PhantomData,
            __canonical_el: &canonical,
            choose_new_order_0_1_2: &new,
            choose_old_order_0_1_2: &old,
            new_el_equalities: &mut output,
        });
        assert_eq!(output, expected);
    }
}

#[test]
fn an_old_result_connects_later_results_and_merged_domains() {
    let mut model = FunctionalityStar::new();
    let new = model.new_el();
    let old = model.new_el();
    let x = model.new_el();
    let y = model.new_el();
    let other = model.new_el();
    model.insert_choose(x, x, old);
    model.insert_choose(y, x, other);
    model.close();
    assert!(!model.are_equal_el(new, old));
    assert!(!model.are_equal_el(other, old));

    model.insert_choose(x, x, new);
    assert!(model.close_until(|model| model.are_equal_el(new, old)));
    model.close();
    assert!(model.are_equal_el(new, old));
    assert!(!model.are_equal_el(other, old));

    model.equate_el(x, y);
    model.close();
    assert!(model.are_equal_el(other, old));
}

#[test]
fn inherited_results_join_owned_results_in_the_same_model() {
    let mut model = FunctionalityStar::new();
    let source = model.new_container();
    let target = model.new_container();
    let x = model.new_member(source);
    let y = model.new_member(source);
    let image_x = model.new_member(target);
    let image_y = model.new_member(target);
    let own_result = model.new_member(target);
    model.insert_chosen(source, x, y);
    model.insert_chosen(target, image_x, own_result);
    model.close();
    assert!(!model.are_equal_member(image_y, own_result));

    let morphism = model.new_container_mor();
    model.insert_container_mor_dom(morphism, source);
    model.insert_container_mor_cod(morphism, target);
    model.insert_member_mor_app(morphism, x, image_x);
    model.insert_member_mor_app(morphism, y, image_y);
    model.close();
    assert!(model.are_equal_member(image_y, own_result));
}

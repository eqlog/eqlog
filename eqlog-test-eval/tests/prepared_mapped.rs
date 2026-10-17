use eqlog_test_eval as _;

include!(concat!(
    env!("EQLOG_OUT_DIR"),
    "/eqlog-test-eval/src/prepared_mapped.eql.rs"
));

#[test]
fn global_secondary_indices_follow_late_nested_images_and_equalities() {
    let mut model = PreparedMapped::new();
    let source = model.new_bundle();
    let target = model.new_bundle();
    let f = model.new_fiber(source);
    let g = model.new_fiber(target);
    let h = model.new_fiber(target);
    let x0 = model.new_el(source, f);
    let x1 = model.new_el(source, f);
    let y0 = model.new_el(target, g);
    let y1 = model.new_el(target, g);
    let z0 = model.new_el(target, h);
    let z1 = model.new_el(target, h);
    let outer = model.new_bundle_mor();
    model.insert_bundle_mor_dom(outer, source);
    model.insert_bundle_mor_cod(outer, target);
    model.insert_fiber_mor_app(outer, f, g);
    model.insert_bundle_el_mor_app(outer, x0, y0);
    let inner = model.new_fiber_mor(target);
    model.insert_fiber_mor_dom(target, inner, g);
    model.insert_fiber_mor_cod(target, inner, h);
    model.insert_el_mor_app(target, inner, y0, z0);
    model.insert_el_mor_app(target, inner, y1, z1);
    model.insert_pair(source, f, x0, x1);
    model.insert_fixed_pair(source, f, x0, x1);
    model.insert_reached(target, h, z1);
    model.insert_fixed_reached(target, h, z1);
    model.close();
    assert!(!model.reached(target, h, z0));
    assert!(!model.fixed_reached(target, h, z0));

    model.insert_bundle_el_mor_app(outer, x1, y1);
    assert!(model.close_until(|model| model.reached(target, h, z0)));
    model.close();
    assert!(model.fixed_reached(target, h, z0));
    assert!(model.pair(target, h, z1, z0));
    assert!(!model.pair(source, f, x1, x0));

    let z2 = model.new_el(target, h);
    let z3 = model.new_el(target, h);
    model.insert_pair(target, h, z3, z2);
    model.insert_fixed_pair(target, h, z3, z2);
    model.close();
    assert!(!model.reached(target, h, z3));
    assert!(!model.fixed_reached(target, h, z3));
    model.equate_el(target, h, z0, z2);
    model.close();
    assert!(model.reached(target, h, z3));
    assert!(model.fixed_reached(target, h, z3));
}

#[test]
fn separate_relation_updates_and_late_images_follow_the_whole_chain() {
    let mut model = PreparedMapped::new();
    let bundle = model.new_bundle();
    let fibers = [
        model.new_fiber(bundle),
        model.new_fiber(bundle),
        model.new_fiber(bundle),
    ];
    let elements = fibers.map(|fiber| {
        [
            model.new_el(bundle, fiber),
            model.new_el(bundle, fiber),
            model.new_el(bundle, fiber),
        ]
    });
    let morphisms = [model.new_fiber_mor(bundle), model.new_fiber_mor(bundle)];
    for (i, &morphism) in morphisms.iter().enumerate() {
        model.insert_fiber_mor_dom(bundle, morphism, fibers[i]);
        model.insert_fiber_mor_cod(bundle, morphism, fibers[i + 1]);
        for j in 0..2 {
            model.insert_el_mor_app(bundle, morphism, elements[i][j], elements[i + 1][j]);
        }
    }
    model.insert_pair(bundle, fibers[0], elements[0][0], elements[0][1]);
    model.close();
    assert!(model.pair(bundle, fibers[2], elements[2][0], elements[2][1]));
    assert!(!model.fixed_pair(bundle, fibers[2], elements[2][1], elements[2][0]));

    model.insert_fixed_pair(bundle, fibers[0], elements[0][1], elements[0][0]);
    model.close();
    assert!(model.fixed_pair(bundle, fibers[2], elements[2][1], elements[2][0]));

    model.insert_pair(bundle, fibers[0], elements[0][2], elements[0][0]);
    model.close();
    assert!(!model.pair(bundle, fibers[2], elements[2][2], elements[2][0]));
    model.insert_el_mor_app(bundle, morphisms[0], elements[0][2], elements[1][2]);
    model.close();
    assert!(model.pair(bundle, fibers[1], elements[1][2], elements[1][0]));
    assert!(!model.pair(bundle, fibers[2], elements[2][2], elements[2][0]));
    model.insert_el_mor_app(bundle, morphisms[1], elements[1][2], elements[2][2]);
    model.close();
    assert!(model.pair(bundle, fibers[2], elements[2][2], elements[2][0]));

    let last = model.new_fiber(bundle);
    let last_elements = [
        model.new_el(bundle, last),
        model.new_el(bundle, last),
        model.new_el(bundle, last),
    ];
    let tail = model.new_fiber_mor(bundle);
    model.insert_fiber_mor_dom(bundle, tail, fibers[2]);
    model.insert_fiber_mor_cod(bundle, tail, last);
    for j in 0..3 {
        model.insert_el_mor_app(bundle, tail, elements[2][j], last_elements[j]);
    }
    model.close();
    assert!(model.pair(bundle, last, last_elements[2], last_elements[0]));
    assert!(model.fixed_pair(bundle, last, last_elements[1], last_elements[0]));

    model.insert_fixed_pair(bundle, fibers[0], elements[0][0], elements[0][2]);
    model.close();
    assert!(model.fixed_pair(bundle, last, last_elements[0], last_elements[2]));
}

#[test]
fn scoped_reverse_lookup_reads_prepared_nested_primary_slices() {
    let mut model = PreparedMapped::new();
    let source = model.new_bundle();
    let target = model.new_bundle();
    let f = model.new_fiber(source);
    let g = model.new_fiber(target);
    let h = model.new_fiber(target);
    let x = [
        model.new_el(source, f),
        model.new_el(source, f),
        model.new_el(source, f),
    ];
    let y = [
        model.new_el(target, g),
        model.new_el(target, g),
        model.new_el(target, g),
    ];
    let z = [
        model.new_el(target, h),
        model.new_el(target, h),
        model.new_el(target, h),
    ];
    let outer = model.new_bundle_mor();
    model.insert_bundle_mor_dom(outer, source);
    model.insert_bundle_mor_cod(outer, target);
    model.insert_fiber_mor_app(outer, f, g);
    for i in [0, 2] {
        model.insert_bundle_el_mor_app(outer, x[i], y[i]);
    }
    let inner = model.new_fiber_mor(target);
    model.insert_fiber_mor_dom(target, inner, g);
    model.insert_fiber_mor_cod(target, inner, h);
    for i in 0..3 {
        model.insert_el_mor_app(target, inner, y[i], z[i]);
    }
    model.insert_pair(source, f, x[0], x[1]);
    model.insert_pair(source, f, x[1], x[2]);
    model.insert_local_reached(target, h, z[2]);
    model.close();
    assert!(!model.local_reached(target, h, z[0]));
    assert!(!model.local_reached(target, h, z[1]));

    model.insert_bundle_el_mor_app(outer, x[1], y[1]);
    assert!(model.close_until(|model| model.local_reached(target, h, z[0])));
    model.close();
    assert!(model.local_reached(target, h, z[1]));
    for i in 0..3 {
        assert!(!model.local_reached(source, f, x[i]));
        assert!(!model.local_reached(target, g, y[i]));
    }

    let fresh = model.new_el(target, h);
    let alias = model.new_el(target, h);
    model.insert_pair(target, h, fresh, alias);
    model.close();
    assert!(!model.local_reached(target, h, fresh));
    model.equate_el(target, h, alias, z[0]);
    model.close();
    assert!(model.local_reached(target, h, fresh));

    let tail = model.new_fiber(target);
    let image = model.new_el(target, tail);
    model.insert_local_reached(target, tail, image);
    model.close();
    let backward = model.new_fiber_mor(target);
    model.insert_fiber_mor_dom(target, backward, tail);
    model.insert_fiber_mor_cod(target, backward, g);
    model.insert_el_mor_app(target, backward, image, y[2]);
    model.close();
    for i in 0..3 {
        assert!(model.local_reached(target, g, y[i]));
        assert!(!model.local_reached(source, f, x[i]));
    }
}

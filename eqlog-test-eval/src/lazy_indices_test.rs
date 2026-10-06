use crate::lazy_indices::LazyIndices;
use eqlog_runtime::CompiledModel;

#[test]
fn later_readers_see_accumulated_rows_and_equality_replacements() {
    let mut model = LazyIndices::new();
    let a = model.new_el();
    let b = model.new_el();
    let c = model.new_el();
    let d = model.new_el();
    model.insert_edge(a, b);
    model.insert_edge(c, d);
    model.close();
    model.insert_end(b);
    model.close();
    assert!(model.backward(a));

    model.insert_edge(b, c);
    model.canonicalize();
    model.equate_el(c, d);
    model.canonicalize();
    model.equate_el(b, a);
    model.canonicalize();
    model.insert_start(a);
    model.insert_start(c);
    model.insert_end(d);
    model.close();
    assert!(model.forward(a));
    assert!(model.forward(c));
    assert!(model.backward(b));
    assert!(model.backward(c));
    assert!(model.diagonal(a));
    assert!(model.diagonal(c));
    assert_eq!(model.iter_edge().count(), 3);

    let mut imported = LazyIndices::from_dynamic(&model.to_dynamic()).unwrap();
    let e = imported.new_el();
    imported.insert_edge(e, c);
    imported.close();
    assert!(imported.backward(e));
    assert_eq!(imported.iter_edge().count(), 4);
}

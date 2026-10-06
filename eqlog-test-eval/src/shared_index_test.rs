use crate::shared_index::SharedIndex;

#[test]
fn readers_on_either_side_of_an_unrelated_stratum_share_incremental_work() {
    let mut model = SharedIndex::new();
    let x = model.new_el();
    let y = model.new_el();
    let z = model.new_el();
    model.insert_edge(x, y);
    model.insert_edge(z, x);
    model.insert_start(y);
    model.close();
    assert!(model.result(z));
    assert!(!model.result(x));

    let w = model.new_el();
    model.insert_edge(w, z);
    model.insert_start(x);
    model.close();
    assert!(model.result(w));

    let alias = model.new_el();
    let v = model.new_el();
    model.insert_edge(v, alias);
    model.close();
    assert!(!model.result(v));
    model.equate_el(alias, z);
    model.close();
    assert!(model.result(v));
    model.close();
    assert_eq!(model.iter_result().count(), 3);
}

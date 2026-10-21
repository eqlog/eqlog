use crate::prefix_diagonal_cache::PrefixDiagonalCache;

#[test]
fn cached_full_inputs_restore_their_source_before_late_secondary_preparation() {
    let mut model = PrefixDiagonalCache::new();
    let diagonal = model.new_el();
    let other = model.new_el();
    let last = model.new_el();
    model.insert_source(diagonal, diagonal);
    model.insert_source(other, diagonal);
    model.insert_source(other, other);
    model.insert_source(last, other);
    model.close();
    assert_eq!(model.iter_joined().count(), 0);

    model.insert_kick(diagonal);
    model.close();
    assert!(model.joined(diagonal, diagonal));
    assert!(model.joined(other, diagonal));
    assert!(model.joined(other, other));
    assert!(model.joined(last, other));
}

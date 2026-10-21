use std::collections::BTreeSet;

use crate::prefix_diagonals::{El, PrefixDiagonals};

fn check(model: &PrefixDiagonals, rows: &[(El, El, El)]) {
    let expected: BTreeSet<_> = rows
        .iter()
        .map(|&(x, y, value)| (model.root_el(x), model.root_el(y), model.root_el(value)))
        .collect();
    assert_eq!(model.iter_copied().collect::<BTreeSet<_>>(), expected);
    let diagonal: BTreeSet<_> = expected
        .iter()
        .filter_map(|&(x, y, value)| (x == y).then_some((x, value)))
        .collect();
    assert_eq!(model.iter_diagonal().collect::<BTreeSet<_>>(), diagonal);
}

#[test]
fn diagonal_consumers_preserve_full_consumers_and_new_equality_matches() {
    let mut model = PrefixDiagonals::new();
    let elements: Vec<_> = (0..12).map(|_| model.new_el()).collect();
    let mut rows = Vec::new();
    for (i, &x) in elements.iter().enumerate() {
        for (j, &y) in elements.iter().enumerate() {
            let value = elements[(i + j) % elements.len()];
            rows.push((x, y, value));
            model.insert_source(x, y, value);
        }
    }
    model.close();
    check(&model, &rows);

    let late = model.new_el();
    for (x, y) in [(elements[3], elements[3]), (elements[1], elements[2])] {
        rows.push((x, y, late));
        model.insert_source(x, y, late);
    }
    model.close();
    check(&model, &rows);
    assert!(!model.diagonal(elements[1], late));
    model.equate_el(elements[1], elements[2]);
    model.close();
    check(&model, &rows);
    assert!(model.diagonal(elements[1], late));
    model.close();
    check(&model, &rows);
}

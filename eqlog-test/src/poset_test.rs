use crate::poset::*;

fn adjoin_chain(p: &mut Poset, length: usize) -> (P, P) {
    assert_ne!(length, 0);

    let first = p.new_p();
    let mut prev = first;
    for _ in 0..(length - 1) {
        let next = p.new_p();
        p.insert_le(prev, next);
        prev = next;
    }
    let last = prev;
    (first, last)
}

#[test]
fn test_collapse() {
    let mut p = Poset::new();

    let (first0, last0) = adjoin_chain(&mut p, 1);
    adjoin_chain(&mut p, 7);
    let (first2, last2) = adjoin_chain(&mut p, 20);

    // Link chains 0 and 2, forming a single loop.
    p.insert_le(last0, first2);
    p.insert_le(last2, first0);

    p.close();
    assert_eq!(p.iter_p().count(), 8);
    assert_eq!(p.iter_le().count(), 1 + (7 * 8 / 2));
}

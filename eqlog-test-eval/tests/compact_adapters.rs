use eqlog_runtime::__private::{CanonicalMask, ElementWeights, MemberSpaces};

#[test]
fn adoption_keeps_old_handles_as_aliases_of_monotone_namespaces() {
    let mut spaces = MemberSpaces::with_handle_bound(4);
    spaces.create_owner(0);
    spaces.create_owner(1);
    let first = spaces.adopt(0, 0);
    let second = spaces.adopt(1, 1);
    let third = spaces.adopt(0, 2);
    let fourth = spaces.adopt(1, 3);
    assert_eq!(spaces.stats().owned_origins, 4);
    for (old, new) in [(0, first), (1, second), (2, third), (3, fourth)] {
        assert!(new >= 4);
        assert_eq!(spaces.root(old), Some(new));
        assert_eq!(spaces.owner(old), spaces.owner(new));
    }
    let before = spaces.snapshot(1);
    spaces.inherit_total_members(0, 1);
    let image = spaces.image(0, 1).unwrap();
    assert_eq!(spaces.image(first, 1), Some(image));
    assert!(image < second);
    assert!(second < spaces.image(2, 1).unwrap());
    assert!(spaces.image(2, 1).unwrap() < fourth);
    assert_eq!(spaces.iter(1).count(), 4);
    assert_eq!(before.iter().count(), 2);
    assert!(!before.contains(image));
    spaces.equate(1, 1, image);
    assert_eq!(spaces.root(second), spaces.root(image));
    assert_eq!(before.root(1), Some(second));
    let late = spaces.allocate(0);
    spaces.refresh(1);
    assert!(spaces.image(late, 1).is_some());
    assert_eq!(spaces.stats().owned_origins, 5);
}

#[test]
fn canonical_masks_do_not_expand_reserved_members() {
    let dense = CanonicalMask::Dense(&[true, false, true]);
    assert!(dense.contains(0));
    assert!(!dense.contains(1));
    let mut spaces = MemberSpaces::with_handle_bound(1000);
    spaces.create_owner(0);
    let member = spaces.adopt(0, 999);
    let mask = CanonicalMask::Members(&spaces);
    assert!(mask.contains(member));
    assert!(!mask.contains(999));
    assert!(!mask.contains(member - 1));
    assert!(!mask.contains(u32::MAX));
    assert_eq!(spaces.stats().owned_origins, 1);
    assert_eq!(spaces.stats().handle_blocks, 2);
}

#[test]
fn virtual_weights_allocate_only_modified_entries() {
    let mut weights = ElementWeights::new();
    weights.push(3);
    weights.push(5);
    assert_eq!(weights.len(), 2);
    weights.increase_size_to(1_000_000_001);
    assert_eq!(weights[1_000_000_000], 0);
    assert_eq!(weights.stored_len(), 2);
    weights[1_000_000_000] += 7;
    assert_eq!(weights.len(), 1_000_000_001);
    assert_eq!(weights.stored_len(), 3);
    assert_eq!(weights[0], 3);
    assert_eq!(weights[1], 5);
    assert_eq!(weights[1_000_000_000], 7);
    weights.increase_size_to(2_000_000_000);
    assert_eq!(weights.len(), 2_000_000_000);
    assert_eq!(weights.stored_len(), 3);

    let mut small = ElementWeights::from(vec![2, 4]);
    small.increase_size_to(6);
    small[5] = 8;
    small.increase_size_to(8);
    let exported: Vec<usize> = small.into();
    assert_eq!(exported, vec![2, 4, 0, 0, 0, 8, 0, 0]);
    let imported = ElementWeights::from(exported);
    assert_eq!(imported.len(), 8);
    assert_eq!(imported[5], 8);
}

#[test]
#[should_panic(expected = "weight index is outside the reserved address space")]
fn weights_reject_unreserved_handles() {
    let weights = ElementWeights::from(vec![1]);
    let _ = weights[1];
}

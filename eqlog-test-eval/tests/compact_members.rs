use std::collections::BTreeSet;

use eqlog_runtime::__private::{CanonicalMask, MemberSpaces};

#[test]
fn replay_events_normalize_local_rows_after_parent_equality() {
    let mut spaces = MemberSpaces::new();
    spaces.create_owner(0);
    spaces.create_owner(1);
    let a = spaces.allocate(0);
    let b = spaces.allocate(0);
    let c = spaces.allocate(0);
    let local = spaces.allocate(1);
    let initial = spaces.inherit_total_members_with_merges(0, 1).unwrap();
    assert!(initial.merges.is_empty());
    assert_eq!(initial.source.owner(), 0);
    let image_a = spaces.image(a, 1).unwrap();
    let image_b = spaces.image(b, 1).unwrap();
    let image_c = spaces.image(c, 1).unwrap();
    let original = spaces.snapshot(1);
    let local_origin = original.origin(local).unwrap();
    let a_origin = original.origin(image_a).unwrap();
    let c_origin = original.origin(image_c).unwrap();
    let merged = spaces.equate_with_merge(1, local, image_a).unwrap();
    assert_eq!(merged.loser, a_origin);
    assert_eq!(merged.winner, local_origin);
    spaces.equate(1, image_c, image_b);
    spaces.equate(0, a, b);
    let refresh = spaces.refresh_with_merges(1).unwrap();
    assert_eq!(refresh.merges.len(), 2);
    assert_eq!(spaces.local_merges(1), refresh.merges.as_slice());
    assert_eq!(refresh.source.root_origin(local_origin), None);
    let current = spaces.snapshot(1);
    for origin in [local_origin, a_origin, c_origin] {
        let mut canonical = refresh.source.root_origin(origin).unwrap_or(origin);
        for merge in &refresh.merges {
            if canonical == merge.loser {
                canonical = merge.winner;
            }
        }
        assert_eq!(current.root_origin(origin), Some(canonical));
    }
    assert!(CanonicalMask::Origins(&current).contains(a_origin));
    assert!(!CanonicalMask::Origins(&current).contains(local_origin));
    assert_eq!(
        current.canonical_domain().iter().collect::<Vec<_>>(),
        vec![a_origin]
    );
    assert_eq!(original.canonical_domain().len(), 4);
    assert_eq!(spaces.source(1), Some(0));
    assert_eq!(spaces.owners().collect::<Vec<_>>(), vec![0, 1]);
    assert!(spaces.refresh_with_merges(1).is_none());
    assert_eq!(spaces.local_merges(1), refresh.merges.as_slice());
}

#[test]
fn inherited_members_share_storage_and_keep_owner_local_equality() {
    let mut spaces = MemberSpaces::new();
    for owner in [10, 20, 30, 40] {
        spaces.create_owner(owner);
    }
    let a = spaces.allocate(10);
    let b = spaces.allocate(10);
    let c = spaces.allocate(10);
    spaces.equate(10, a, b);
    spaces.inherit_total_members(10, 20);
    spaces.inherit_total_members(10, 30);
    spaces.inherit_total_members(20, 40);
    let source = spaces.snapshot(10);
    let child = spaces.snapshot(20);
    assert!(source.shares_domain_with(&child));
    assert!(source.shares_partition_with(&child));
    let child_a = spaces.image(a, 20).unwrap();
    let child_c = spaces.image(c, 20).unwrap();
    let sibling_a = spaces.image(a, 30).unwrap();
    let sibling_c = spaces.image(c, 30).unwrap();
    assert_ne!(a, child_a);
    assert_ne!(child_a, sibling_a);
    assert!(spaces.contains(20, child_a));
    assert!(!spaces.contains(10, child_a));
    assert_eq!(spaces.owner(child_a), Some(20));
    assert_eq!(spaces.image(child_a, 30), None);
    assert!(spaces.equate(20, child_a, child_c));
    assert_eq!(spaces.root(child_a), spaces.root(child_c));
    assert_ne!(spaces.root(a), spaces.root(c));
    assert_ne!(spaces.root(sibling_a), spaces.root(sibling_c));
    assert_ne!(child.root(child_a), child.root(child_c));
    assert_eq!(spaces.refresh_descendants(20), 1);
    assert_eq!(spaces.iter(40).count(), 1);
    assert_eq!(spaces.iter(10).count(), 2);
    assert_eq!(spaces.iter(30).count(), 2);
    assert_eq!(spaces.refresh_descendants(10), 0);
}

#[test]
fn late_source_roots_and_local_members_preserve_old_snapshots() {
    let mut spaces = MemberSpaces::new();
    spaces.create_owner(0);
    spaces.create_owner(1);
    let source = spaces.allocate(0);
    let local = spaces.allocate(1);
    spaces.inherit_total_members(0, 1);
    let image = spaces.image(source, 1).unwrap();
    let before = spaces.snapshot(1);
    spaces.equate(1, local, image);
    let local_equation = spaces.snapshot(1);

    let a = spaces.allocate(0);
    let b = spaces.allocate(0);
    let c = spaces.allocate(0);
    let d = spaces.allocate(0);
    spaces.equate(0, a, b);
    spaces.equate(0, c, d);
    spaces.equate(0, a, c);
    spaces.equate(0, source, a);
    assert_ne!(spaces.root(source), Some(source));
    assert_eq!(spaces.image(a, 1), None);
    assert!(spaces.refresh(1));
    let late = spaces.image(a, 1).unwrap();
    assert_eq!(spaces.root(local), Some(late));
    assert_eq!(spaces.root(image), Some(late));
    assert_eq!(spaces.image(source, 1), Some(late));
    assert!(spaces.contains(1, local));
    assert_eq!(before.root(image), Some(image));
    assert_ne!(before.root(local), before.root(image));
    assert_eq!(local_equation.root(local), local_equation.root(image));
    assert!(!before.contains(late));
    assert!(!local_equation.contains(late));
    assert_eq!(spaces.stats().replayed_equations, 1);
    assert!(!spaces.refresh(1));
    assert_eq!(spaces.stats().replayed_equations, 1);
}

#[test]
fn reserved_holes_are_not_members() {
    let mut spaces = MemberSpaces::new();
    for owner in [0, 1, 2] {
        spaces.create_owner(owner);
    }
    let unrelated = spaces.allocate(2);
    let source = spaces.allocate(0);
    spaces.inherit_total_members(0, 1);
    let child = spaces.snapshot(1);
    let block = child.blocks().next().unwrap();
    let hole = block.first_handle;
    assert_eq!(block.first_origin, 0);
    assert_eq!(block.len, 2);
    assert!(!spaces.contains(1, hole));
    assert_eq!(spaces.owner(hole), None);
    assert_eq!(spaces.root(hole), None);
    assert_eq!(child.handle(0), None);
    assert_eq!(child.origin(hole), None);
    assert_eq!(spaces.image(unrelated, 1), None);
    let image = spaces.image(source, 1).unwrap();
    assert_eq!(child.members().collect::<Vec<_>>(), vec![image]);
    assert_eq!(spaces.iter(1).collect::<Vec<_>>(), vec![image]);
    assert_eq!(spaces.owner(u32::MAX), None);
}

#[test]
fn installing_inheritance_retains_existing_target_equations() {
    let mut spaces = MemberSpaces::new();
    spaces.create_owner(7);
    spaces.create_owner(9);
    let left = spaces.allocate(9);
    let right = spaces.allocate(9);
    spaces.equate(9, left, right);
    let source = spaces.allocate(7);
    let before = spaces.snapshot(9);
    spaces.inherit_total_members(7, 9);
    assert_eq!(spaces.root(left), spaces.root(right));
    assert_eq!(spaces.root(left), before.root(left));
    let image = spaces.image(source, 9).unwrap();
    assert_ne!(spaces.root(left), Some(image));
    assert_eq!(spaces.iter(9).count(), 2);
    assert!(!spaces.inherit_total_members(7, 9));
}

#[test]
fn fragmented_domains_remain_shared_across_late_growth() {
    let mut spaces = MemberSpaces::new();
    for owner in 0..3 {
        spaces.create_owner(owner);
    }
    let mut source = Vec::new();
    for _ in 0..128 {
        spaces.allocate(2);
        source.push(spaces.allocate(0));
    }
    spaces.inherit_total_members(0, 1);
    let before = spaces.snapshot(1);
    assert!(before.shares_domain_with(&spaces.snapshot(0)));
    let local = spaces.allocate(1);
    let late = spaces.allocate(0);
    spaces.refresh(1);
    let current = spaces.snapshot(1);
    assert!(current.contains(local));
    assert!(!before.contains(local));
    assert_eq!(before.members().count(), 128);
    assert_eq!(current.members().count(), 130);
    for member in source {
        let origin = spaces.snapshot(0).origin(member).unwrap();
        assert_eq!(before.handle(origin), current.handle(origin));
    }
    assert!(!before.contains(spaces.image(late, 1).unwrap()));
}

#[test]
fn chains_store_only_owned_origins_and_local_equations() {
    for waves in [1, 8] {
        for equality in [false, true] {
            let mut spaces = MemberSpaces::new();
            let owners = 256;
            let mut local = Vec::new();
            for owner in 0..owners {
                spaces.create_owner(owner);
                if owner > 0 {
                    spaces.inherit_total_members(owner - 1, owner);
                }
                let members: Vec<_> = (0..waves).map(|_| spaces.allocate(owner)).collect();
                local.push(members);
            }
            for wave in 0..waves {
                for owner in 1..owners {
                    spaces.refresh(owner);
                    if equality {
                        let inherited = spaces
                            .image(local[owner as usize - 1][wave], owner)
                            .unwrap();
                        spaces.equate(owner, inherited, local[owner as usize][wave]);
                    }
                }
            }
            let stats = spaces.stats();
            assert_eq!(stats.owned_origins, u64::from(owners) * waves as u64);
            assert!(stats.handle_blocks <= owners as usize * (waves + 1));
            assert!(stats.reserved_handles > stats.owned_origins * 100);
            let equations = if equality {
                (owners as usize - 1) * waves
            } else {
                0
            };
            assert_eq!(stats.local_equations, equations);
            assert!(stats.replayed_equations <= (owners as u64) * (waves * waves) as u64);
            for owner in 0..owners {
                let expected = if equality {
                    waves
                } else {
                    (owner as usize + 1) * waves
                };
                let roots: BTreeSet<_> = spaces.iter(owner).collect();
                assert_eq!(roots.len(), expected);
                for &member in &local[owner as usize] {
                    assert!(roots.contains(&spaces.root(member).unwrap()));
                }
            }
            assert_eq!(spaces.refresh_descendants(0), 0);
        }
    }
}

#[test]
#[should_panic(expected = "cyclic member inheritance")]
fn inheritance_rejects_cycles() {
    let mut spaces = MemberSpaces::new();
    for owner in 0..3 {
        spaces.create_owner(owner);
    }
    spaces.inherit_total_members(0, 1);
    spaces.inherit_total_members(1, 2);
    spaces.inherit_total_members(2, 0);
}

#[test]
#[should_panic(expected = "owner already has another source")]
fn inheritance_rejects_multiple_sources() {
    let mut spaces = MemberSpaces::new();
    for owner in 0..3 {
        spaces.create_owner(owner);
    }
    spaces.inherit_total_members(0, 2);
    spaces.inherit_total_members(1, 2);
}

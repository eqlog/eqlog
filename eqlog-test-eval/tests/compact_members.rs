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
    assert_eq!(spaces.source_revision(0), None);
    for owner in 0..3 {
        spaces.create_owner(owner);
    }
    assert_eq!(spaces.source_revision(0), None);
    let mut source = Vec::new();
    for _ in 0..128 {
        spaces.allocate(2);
        source.push(spaces.allocate(0));
    }
    spaces.inherit_total_members(0, 1);
    let before = spaces.snapshot(1);
    let inherited_revision = spaces.snapshot(0).revision();
    assert_eq!(spaces.source_revision(1), Some(inherited_revision));
    assert!(before.shares_domain_with(&spaces.snapshot(0)));
    let local = spaces.allocate(1);
    let late = spaces.allocate(0);
    assert_eq!(spaces.source_revision(1), Some(inherited_revision));
    assert_ne!(inherited_revision, spaces.snapshot(0).revision());
    spaces.refresh(1);
    assert_eq!(
        spaces.source_revision(1),
        Some(spaces.snapshot(0).revision())
    );
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
#[should_panic(expected = "cyclic member inheritance")]
fn a_leaf_rejects_its_own_incoming_edge() {
    let mut spaces = MemberSpaces::new();
    spaces.create_owner(0);
    spaces.register_edge(0, 0);
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

#[test]
fn shared_diamonds_identify_only_witnessed_ancestor_images() {
    let mut spaces = MemberSpaces::new();
    for owner in 0..4 {
        spaces.create_owner(owner);
    }
    let common = spaces.allocate(0);
    let common_origin = spaces.snapshot(0).origin(common).unwrap();
    spaces.witness(0, common_origin);
    spaces.inherit_total_members(0, 1);
    spaces.inherit_total_members(0, 2);
    let left = spaces.allocate(1);
    let right = spaces.allocate(2);
    let local = spaces.allocate(3);
    spaces.inherit_total_members(1, 3);
    let before = spaces.snapshot(3);
    assert!(spaces.can_share_inheritance(2, 3));
    assert!(spaces.inherit_shared_members(2, 3));
    assert!(spaces.has_multiple_sources());
    let left_common = spaces.image(common, 1).unwrap();
    let right_common = spaces.image(common, 2).unwrap();
    let common_image = spaces.image(left_common, 3).unwrap();
    assert_eq!(spaces.image(right_common, 3), Some(common_image));
    assert_eq!(spaces.image(common, 3), None);
    assert_ne!(left_common, right_common);
    let left_image = spaces.image(left, 3).unwrap();
    let right_image = spaces.image(right, 3).unwrap();
    assert_eq!(
        spaces.iter(3).collect::<BTreeSet<_>>(),
        BTreeSet::from([common_image, left_image, right_image, local])
    );
    assert!(before.contains(common_image));
    assert!(before.contains(left_image));
    assert!(before.contains(local));
    assert!(!before.contains(right_image));
    assert_eq!(spaces.iter(0).count(), 1);
    assert_eq!(spaces.iter(1).count(), 2);
    assert_eq!(spaces.iter(2).count(), 2);
    assert!(spaces.refresh_with_merges(3).is_none());

    let late_right = spaces.allocate(2);
    let refresh = spaces.refresh_with_merges(3).unwrap();
    let late_origin = spaces.snapshot(2).origin(late_right).unwrap();
    assert_eq!(refresh.source.owner(), 1);
    assert!(!refresh.source.domain().contains(&late_origin));
    assert!(refresh.merges.is_empty());
    assert!(spaces.image(late_right, 3).is_some());
    assert_eq!(spaces.iter(3).count(), 5);
}

#[test]
fn equal_origin_numbers_do_not_prove_shared_images() {
    let mut spaces = MemberSpaces::new();
    for owner in 0..4 {
        spaces.create_owner(owner);
    }
    let common = spaces.allocate(0);
    let origin = spaces.snapshot(0).origin(common).unwrap();
    spaces.inherit_total_members(0, 1);
    spaces.inherit_total_members(0, 2);
    spaces.inherit_total_members(1, 3);
    assert!(!spaces.can_share_inheritance(2, 3));
    spaces.witness(1, origin);
    spaces.witness(2, origin);
    assert!(!spaces.can_share_inheritance(2, 3));
    assert_eq!(spaces.iter(3).count(), 1);
    assert_eq!(spaces.image(spaces.image(common, 2).unwrap(), 3), None);
}

#[test]
fn refreshed_witnesses_keep_late_local_and_source_proofs() {
    let mut spaces = MemberSpaces::new();
    for owner in 0..5 {
        spaces.create_owner(owner);
    }
    let first = spaces.allocate(0);
    spaces.inherit_total_members(0, 1);
    let local = spaces.allocate(1);
    let local_origin = spaces.snapshot(1).origin(local).unwrap();
    spaces.witness(1, local_origin);
    let late = spaces.allocate(0);
    assert!(spaces.refresh(1));
    for member in [first, late] {
        let origin = spaces.snapshot(0).origin(member).unwrap();
        spaces.witness(0, origin);
    }
    assert!(spaces.refresh(1));
    spaces.inherit_total_members(1, 2);
    spaces.inherit_total_members(1, 3);
    spaces.inherit_total_members(2, 4);
    assert!(spaces.can_share_inheritance(3, 4));
    spaces.inherit_shared_members(3, 4);
    for member in [
        spaces.image(first, 1).unwrap(),
        spaces.image(late, 1).unwrap(),
        local,
    ] {
        let left = spaces.image(member, 2).unwrap();
        let right = spaces.image(member, 3).unwrap();
        assert_eq!(spaces.image(left, 4), spaces.image(right, 4));
        assert!(spaces.image(left, 4).is_some());
    }
}

#[test]
fn a_late_source_proof_supersedes_an_independent_local_proof() {
    let mut spaces = MemberSpaces::new();
    for owner in 0..4 {
        spaces.create_owner(owner);
    }
    let first = spaces.allocate(0);
    let origin = spaces.snapshot(0).origin(first).unwrap();
    spaces.inherit_total_members(0, 1);
    spaces.witness(1, origin);
    let late = spaces.allocate(0);
    assert!(spaces.refresh(1));
    spaces.witness(0, origin);
    let late_origin = spaces.snapshot(0).origin(late).unwrap();
    spaces.witness(0, late_origin);
    assert!(spaces.refresh(1));
    spaces.inherit_total_members(0, 2);
    spaces.inherit_total_members(1, 3);
    assert!(spaces.can_share_inheritance(2, 3));
    spaces.inherit_shared_members(2, 3);
    for member in [first, late] {
        let left = spaces.image(member, 1).unwrap();
        let right = spaces.image(member, 2).unwrap();
        assert_eq!(spaces.image(left, 3), spaces.image(right, 3));
    }
}

#[test]
fn shared_refresh_rechecks_late_origins_and_changed_partitions() {
    let mut spaces = MemberSpaces::new();
    for owner in 0..4 {
        spaces.create_owner(owner);
    }
    let common = spaces.allocate(0);
    spaces.inherit_total_members(0, 1);
    spaces.inherit_total_members(0, 2);
    spaces.inherit_total_members(1, 3);
    assert!(!spaces.can_share_inheritance(2, 3));
    let origin = spaces.snapshot(0).origin(common).unwrap();
    spaces.witness(0, origin);
    spaces.refresh(1);
    spaces.refresh(2);
    assert!(spaces.can_share_inheritance(2, 3));
    spaces.inherit_shared_members(2, 3);
    let before = spaces.snapshot(3);

    let late = spaces.allocate(0);
    spaces.refresh(1);
    spaces.refresh(2);
    assert!(!spaces.can_refresh(3));
    assert_eq!(spaces.snapshot(3).revision(), before.revision());
    let late_origin = spaces.snapshot(0).origin(late).unwrap();
    spaces.witness(0, late_origin);
    spaces.refresh(1);
    spaces.refresh(2);
    assert!(spaces.can_refresh(3));
    assert!(spaces.refresh(3));
    let left_late = spaces.image(late, 1).unwrap();
    let right_late = spaces.image(late, 2).unwrap();
    let late_image = spaces.image(left_late, 3).unwrap();
    assert_eq!(spaces.image(right_late, 3), Some(late_image));
    assert!(!before.contains(late_image));
    let left_common = spaces.image(common, 1).unwrap();
    spaces.equate(1, left_common, left_late);
    assert!(!spaces.can_refresh(3));
    assert_eq!(spaces.iter(3).count(), 2);
}

#[test]
fn shared_refresh_rechecks_equations_in_each_participating_owner() {
    for equated_owner in [1, 2, 3] {
        let mut spaces = MemberSpaces::new();
        for owner in 0..4 {
            spaces.create_owner(owner);
        }
        let a = spaces.allocate(0);
        let b = spaces.allocate(0);
        for member in [a, b] {
            let origin = spaces.snapshot(0).origin(member).unwrap();
            spaces.witness(0, origin);
        }
        spaces.inherit_total_members(0, 1);
        spaces.inherit_total_members(0, 2);
        spaces.inherit_total_members(1, 3);
        spaces.inherit_shared_members(2, 3);
        assert!(spaces.can_refresh(3));
        assert!(!spaces.refresh(3));

        let members = spaces.iter(equated_owner).collect::<Vec<_>>();
        assert_eq!(members.len(), 2);
        assert!(spaces.equate(equated_owner, members[0], members[1]));
        assert!(!spaces.can_refresh(3));
        assert_ne!(spaces.root(a), spaces.root(b));
    }
}

#[test]
fn descendant_refresh_visits_skewed_diamonds_in_topological_order() {
    let mut spaces = MemberSpaces::new();
    for owner in 0..5 {
        spaces.create_owner(owner);
    }
    let common = spaces.allocate(0);
    let origin = spaces.snapshot(0).origin(common).unwrap();
    spaces.witness(0, origin);
    for (source, target) in [(0, 1), (0, 2), (2, 3), (1, 4)] {
        spaces.inherit_total_members(source, target);
    }
    spaces.inherit_shared_members(3, 4);
    let before = spaces.snapshot(4);
    let late = spaces.allocate(0);
    let late_origin = spaces.snapshot(0).origin(late).unwrap();
    spaces.witness(0, late_origin);
    assert_eq!(spaces.refresh_descendants(0), 4);
    for owner in 1..5 {
        assert!(spaces.snapshot(owner).domain().contains(&late_origin));
    }
    assert_eq!(spaces.iter(4).count(), 2);
    assert_eq!(before.members().count(), 1);
    assert_eq!(spaces.refresh_descendants(0), 0);
}

#[test]
#[should_panic(expected = "cyclic member inheritance")]
fn pending_edges_reject_cycles_before_installing_images() {
    let mut spaces = MemberSpaces::new();
    for owner in 0..3 {
        spaces.create_owner(owner);
    }
    spaces.register_edge(0, 1);
    spaces.register_edge(1, 2);
    spaces.register_edge(0, 2);
    spaces.register_edge(0, 2);
    spaces.register_edge(2, 0);
}

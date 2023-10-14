#[cfg(test)]
mod test {
    use crate::pointed::*;
    use maplit::btreeset;
    use std::collections::BTreeSet;

    #[test]
    fn test_make_point() {
        let mut ptd = Pointed::new();

        let els: BTreeSet<P> = ptd.iter_p().collect();
        assert_eq!(els, btreeset! {});
        let pts: BTreeSet<P> = ptd.iter_pt().collect();
        assert_eq!(pts, btreeset! {});

        ptd.close();

        let els: BTreeSet<P> = ptd.iter_p().collect();
        assert_eq!(els.len(), 1);
        let pts: BTreeSet<P> = ptd.iter_pt().collect();
        assert_eq!(pts, btreeset! {els.iter().copied().next().unwrap()});
    }

    #[test]
    fn test_collapse_point() {
        let mut ptd = Pointed::new();

        let el0 = ptd.new_p();
        ptd.insert_pt(el0);
        let el1 = ptd.new_p();
        ptd.insert_pt(el1);

        ptd.close();

        assert_eq!(ptd.iter_p().count(), 1);
        assert_eq!(ptd.iter_pt().count(), 1);
        assert!(ptd.are_equal_p(el0, el1));
        assert!(ptd
            .iter_pt()
            .all(|lhs_el| ptd.iter_pt().all(|rhs_el| ptd.are_equal_p(lhs_el, rhs_el))));
    }

    #[test]
    fn test_ignore_non_point() {
        let mut ptd = Pointed::new();

        ptd.new_p();
        ptd.close();

        assert_eq!(ptd.iter_p().count(), 2);
        let (el0, el1) = {
            let mut it = ptd.iter_p();
            let el0 = it.next().unwrap();
            let el1 = it.next().unwrap();
            (el0, el1)
        };
        assert!(!ptd.are_equal_p(el0, el1));
        assert_eq!(ptd.iter_pt().count(), 1);
    }
}

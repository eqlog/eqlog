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
        let pts: BTreeSet<Pt> = ptd.iter_pt().collect();
        assert_eq!(pts, btreeset! {});

        ptd.close();

        let els: BTreeSet<P> = ptd.iter_p().collect();
        assert_eq!(els.len(), 1);
        let pts: BTreeSet<Pt> = ptd.iter_pt().collect();
        assert_eq!(pts, btreeset! {Pt(els.iter().copied().next().unwrap())});
    }
}

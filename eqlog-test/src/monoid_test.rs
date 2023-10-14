#[cfg(test)]
mod test {
    use maplit::btreeset;
    use std::collections::BTreeSet;
    use std::iter::once;

    #[test]
    fn cyclic_two_elements() {
        use crate::monoid::*;

        let mut mon = Monoid::new();

        // Neutral element.
        let a0 = mon.new_m();
        mon.insert_e(a0);

        // Generator.
        let a1 = mon.new_m();

        // a1 * a1 = a0
        mon.insert_mul(a1, a1, a0);

        mon.close();

        let a0 = mon.root_m(a0);
        let a1 = mon.root_m(a1);
        let els: BTreeSet<M> = mon.iter_m().collect();
        assert_eq!(els, btreeset! {a0, a1});

        let e: BTreeSet<M> = mon.iter_e().collect();
        assert_eq!(e, btreeset! {a0});

        let mul: BTreeSet<(M, M, M)> = mon.iter_mul().collect();
        assert_eq!(
            mul,
            btreeset! {
                (a0, a0, a0),
                (a0, a1, a1),
                (a1, a0, a1),
                (a1, a1, a0),
            }
        );
    }

    #[test]
    fn cyclic_five_elements() {
        use crate::monoid::*;

        let mut mon = Monoid::new();

        // Neutral element.
        let a0 = mon.new_m();
        mon.insert_e(a0);

        // Generator.
        let a1 = mon.new_m();

        // a1 * a1 = a2
        let a2 = mon.new_m();
        mon.insert_mul(a1, a1, a2);

        // a2 * a2 = a4
        let a4 = mon.new_m();
        mon.insert_mul(a2, a2, a4);

        // a4 * a1 = a0
        mon.insert_mul(a4, a1, a0);

        mon.close();

        assert_eq!(mon.iter_m().count(), 5);
        assert_eq!(mon.iter_e().count(), 1);
        assert_eq!(mon.iter_mul().count(), 5 * 5);
    }

    #[test]
    fn cyclic_many_elements() {
        use crate::monoid::*;
        // Cyclic group of order 2^n.
        let n = 4;
        let mut mon = Monoid::new();

        // Neutral element.
        let e = mon.new_m();
        mon.insert_e(e);
        let mut els = Vec::new();
        for _ in 0..n {
            els.push(mon.new_m());
        }
        for (a, b) in els
            .iter()
            .copied()
            .zip(els.iter().copied().skip(1).chain(once(e)))
        {
            mon.insert_mul(a, a, b);
        }

        mon.close();
        assert_eq!(mon.iter_m().count(), 1 << n);
        assert_eq!(mon.iter_e().count(), 1);
        assert_eq!(mon.iter_mul().count(), 1 << (2 * n));
    }

    #[test]
    fn trivial_idempotent() {
        use crate::trivial_idempotent::*;

        let mut m = TrivialIdempotent::new();

        let el0 = m.new_m();
        m.insert_e(el0);
        let el1 = m.new_m();
        m.insert_mul(el1, el1, el1);

        m.close();

        assert!(m.are_equal_m(el0, el1));
        assert_eq!(m.iter_m().count(), 1);
    }
}

#[cfg(test)]
mod test {
    use maplit::btreeset;
    use std::collections::BTreeSet;

    #[test]
    fn test_equational_cyclic_no_neutral() {
        use crate::equational_monoid::*;

        // Cyclic monoid with 5 non-trivial elements, with neutral element not defined.
        let mut mon = EquationalMonoid::new();
        let a1 = mon.new_m();
        let a2 = mon.new_m();
        let a3 = mon.new_m();
        let a4 = mon.new_m();
        let a5 = mon.new_m();

        mon.insert_mul(Mul(a1, a1, a2));
        mon.insert_mul(Mul(a2, a1, a3));
        mon.insert_mul(Mul(a3, a1, a4));
        mon.insert_mul(Mul(a4, a1, a5));
        mon.insert_mul(Mul(a5, a2, a1));

        let mut m: Vec<M> = mon.iter_m().collect();
        m.sort();
        assert_eq!(m, vec![a1, a2, a3, a4, a5]);

        let mut e: Vec<E> = mon.iter_e().collect();
        e.sort();
        assert_eq!(e, vec![]);

        let mut mul: Vec<Mul> = mon.iter_mul().collect();
        mul.sort();
        assert_eq!(
            mul,
            vec![
                Mul(a1, a1, a2),
                Mul(a2, a1, a3),
                Mul(a3, a1, a4),
                Mul(a4, a1, a5),
                Mul(a5, a2, a1),
            ]
        );

        mon.close();

        let mut m: Vec<M> = mon.iter_m().collect();
        m.sort();
        assert_eq!(m, vec![a1, a2, a3, a4, a5]);

        let mut e: Vec<E> = mon.iter_e().collect();
        e.sort();
        assert_eq!(e, vec![]);

        let mut mul: Vec<Mul> = mon.iter_mul().collect();
        mul.sort();
        assert_eq!(
            mul,
            vec![
                Mul(a1, a1, a2),
                Mul(a1, a2, a3),
                Mul(a1, a3, a4),
                Mul(a1, a4, a5),
                // Mul(a1, a4, E())
                Mul(a2, a1, a3),
                Mul(a2, a2, a4),
                Mul(a2, a3, a5),
                // Mul(a2, a4, E()),
                Mul(a2, a5, a1),
                Mul(a3, a1, a4),
                Mul(a3, a2, a5),
                //Mul(a3, a3, E()),
                Mul(a3, a4, a1),
                Mul(a3, a5, a2),
                Mul(a4, a1, a5),
                //Mul(a4, a2, E()),
                Mul(a4, a3, a1),
                Mul(a4, a4, a2),
                Mul(a4, a5, a3),
                //Mul(a5, a1, E()),
                Mul(a5, a2, a1),
                Mul(a5, a3, a2),
                Mul(a5, a4, a3),
                Mul(a5, a5, a4),
            ]
        );
    }

    #[test]
    fn cyclic_two_elements() {
        use crate::monoid::*;

        let mut mon = Monoid::new();

        // Neutral element.
        let a0 = mon.new_m();
        mon.insert_e(E(a0));

        // Generator.
        let a1 = mon.new_m();

        // a1 * a1 = a0
        mon.insert_mul(Mul(a1, a1, a0));

        mon.close();

        let a0 = mon.m_root(a0);
        let a1 = mon.m_root(a1);
        let els: BTreeSet<M> = mon.iter_m().collect();
        assert_eq!(els, btreeset! {a0, a1});

        let e: BTreeSet<E> = mon.iter_e().collect();
        assert_eq!(e, btreeset! {E(a0)});

        let mul: BTreeSet<Mul> = mon.iter_mul().collect();
        assert_eq!(
            mul,
            btreeset! {
                Mul(a0, a0, a0),
                Mul(a0, a1, a1),
                Mul(a1, a0, a1),
                Mul(a1, a1, a0),
            }
        );
    }

    #[test]
    fn cyclic_five_elements() {
        use crate::monoid::*;

        let mut mon = Monoid::new();

        // Neutral element.
        let a0 = mon.new_m();
        mon.insert_e(E(a0));

        // Generator.
        let a1 = mon.new_m();

        // a1 * a1 = a2
        let a2 = mon.new_m();
        mon.insert_mul(Mul(a1, a1, a2));

        // a2 * a2 = a4
        let a4 = mon.new_m();
        mon.insert_mul(Mul(a2, a2, a4));

        // a4 * a1 = a0
        mon.insert_mul(Mul(a4, a1, a0));

        mon.close();

        assert_eq!(mon.iter_m().count(), 5);
        assert_eq!(mon.iter_e().count(), 1);
        assert_eq!(mon.iter_mul().count(), 5 * 5);
    }
}

use eqlog_runtime::eqlog_mod;
eqlog_mod!(equational_monoid);
pub use crate::equational_monoid::*;

#[test]
fn test_equational_cyclic_no_neutral() {
    // Cyclic monoid with 5 non-trivial elements, with neutral element not defined.
    let mut mon = EquationalMonoid::new();
    let a1 = mon.new_m();
    let a2 = mon.new_m();
    let a3 = mon.new_m();
    let a4 = mon.new_m();
    let a5 = mon.new_m();

    mon.insert_mul(a1, a1, a2);
    mon.insert_mul(a2, a1, a3);
    mon.insert_mul(a3, a1, a4);
    mon.insert_mul(a4, a1, a5);
    mon.insert_mul(a5, a2, a1);

    mon.close();

    let mut m: Vec<M> = mon.iter_m().collect();
    m.sort();
    assert_eq!(m, vec![a1, a2, a3, a4, a5]);

    let mut e: Vec<M> = mon.iter_e().collect();
    e.sort();
    assert_eq!(e, vec![]);

    let mut mul: Vec<(M, M, M)> = mon.iter_mul().collect();
    mul.sort();
    assert_eq!(
        mul,
        vec![
            (a1, a1, a2),
            (a1, a2, a3),
            (a1, a3, a4),
            (a1, a4, a5),
            // Mul(a1, a4, E())
            (a2, a1, a3),
            (a2, a2, a4),
            (a2, a3, a5),
            // Mul(a2, a4, E()),
            (a2, a5, a1),
            (a3, a1, a4),
            (a3, a2, a5),
            //Mul(a3, a3, E()),
            (a3, a4, a1),
            (a3, a5, a2),
            (a4, a1, a5),
            //Mul(a4, a2, E()),
            (a4, a3, a1),
            (a4, a4, a2),
            (a4, a5, a3),
            //Mul(a5, a1, E()),
            (a5, a2, a1),
            (a5, a3, a2),
            (a5, a4, a3),
            (a5, a5, a4),
        ]
    );
}

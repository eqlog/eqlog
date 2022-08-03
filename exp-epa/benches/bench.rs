use criterion::{criterion_group, criterion_main, Criterion};
use exp_epa::check;
use indoc::indoc;

fn check_bool_and_commutative() {
    let src = indoc! {"
            def and (x : Bool) (y : Bool) : Bool :=
              elim_bool x into (x1 : Bool) : Bool
                | false => false
                | true => y
              .

            def first_false (y: Bool) : and(false, y) = false := refl false.
            def second_false (x: Bool) : and(x, false) = false :=
              elim_bool x into (x0 : Bool) : and(x0, false) = false
                | false => (refl false : and(false, false) = false)
                | true => (refl false : and(true, false) = false)
              .

            def first_true (y: Bool) : and(true, y) = y := refl y.
            def second_true (x: Bool) : and(x, true) = x :=
              elim_bool x into (x0 : Bool) : and(x0, true) = x0
                | false => (refl false : and(false, true) = false)
                | true => (refl true : and(true, true) = true)
              .

            def and_commutative (x : Bool) (y : Bool) : and(x, y) = and(y, x) :=
              elim_bool x into (x0 : Bool) : and(x0, y) = and(y, x0)
                | false =>
                    let
                      def left_is_false : and(false, y) = false := first_false(y).
                      def right_is_false : and(y, false) = false := second_false(y).
                    in
                      refl false
                | true =>
                    let
                      def left_is_y : and(true, y) = y := first_true(y).
                      def right_is_y : and(y, true) = y := second_true(y).
                    in
                      refl y
              .
        "};
    check(&src);
}

fn criterion_benchmark(c: &mut Criterion) {
    c.bench_function("check_bool_and_commutative", |b| {
        b.iter(|| check_bool_and_commutative())
    });
}

criterion_group!(benches, criterion_benchmark);
criterion_main!(benches);

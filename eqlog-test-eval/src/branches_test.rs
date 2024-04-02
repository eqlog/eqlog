use crate::branches::*;

#[test]
fn branching_predicates_nothing() {
    let mut branches = Branches::new();

    branches.close();

    assert!(!branches.a());
    assert!(!branches.b());
    assert!(!branches.b_0());
    assert!(!branches.c());
    assert!(!branches.c_0());
    assert!(!branches.d());
    assert!(!branches.d_0());
}

#[test]
fn branching_predicates_a() {
    let mut branches = Branches::new();
    branches.insert_a();

    branches.close();

    assert!(branches.a());
    assert!(!branches.b());
    assert!(!branches.b_0());
    assert!(!branches.c());
    assert!(!branches.c_0());
    assert!(!branches.d());
    assert!(!branches.d_0());
}

#[test]
fn branching_predicates_b() {
    let mut branches = Branches::new();
    branches.insert_b();

    branches.close();

    assert!(!branches.a());
    assert!(branches.b());
    assert!(!branches.b_0());
    assert!(!branches.c());
    assert!(!branches.c_0());
    assert!(!branches.d());
    assert!(!branches.d_0());
}

#[test]
fn branching_predicates_c() {
    let mut branches = Branches::new();
    branches.insert_c();

    branches.close();

    assert!(!branches.a());
    assert!(!branches.b());
    assert!(!branches.b_0());
    assert!(branches.c());
    assert!(!branches.c_0());
    assert!(!branches.d());
    assert!(!branches.d_0());
}

#[test]
fn branching_predicates_ab() {
    let mut branches = Branches::new();
    branches.insert_a();
    branches.insert_b();

    branches.close();

    assert!(branches.a());
    assert!(branches.b());
    assert!(branches.b_0());
    assert!(!branches.c());
    assert!(!branches.c_0());
    assert!(!branches.d());
    assert!(!branches.d_0());
}

#[test]
fn branching_predicates_ac() {
    let mut branches = Branches::new();
    branches.insert_a();
    branches.insert_c();

    branches.close();

    assert!(branches.a());
    assert!(!branches.b());
    assert!(!branches.b_0());
    assert!(branches.c());
    assert!(branches.c_0());
    assert!(!branches.d());
    assert!(!branches.d_0());
}

#[test]
fn branching_predicates_acd() {
    let mut branches = Branches::new();
    branches.insert_a();
    branches.insert_c();
    branches.insert_d();

    branches.close();

    assert!(branches.a());
    assert!(!branches.b());
    assert!(!branches.b_0());
    assert!(branches.c());
    assert!(branches.c_0());
    assert!(branches.d());
    assert!(branches.d_0());
}

#[test]
fn branching_same_variable_after_unaffected() {
    let mut branches = Branches::new();

    let a = branches.new_foo();
    let b = branches.new_foo();
    branches.insert_bar(a);

    branches.close();

    assert!(branches.baz(b));
}

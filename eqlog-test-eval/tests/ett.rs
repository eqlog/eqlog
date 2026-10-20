use eqlog_ett::check;
use eqlog_ett::kernel::Kernel;
use indoc::{formatdoc, indoc};

const NAT: &str = indoc! {"
    inductive Nat where
    | zero
    | succ (n : Nat)

    def add (m n : Nat) : Nat :=
      rec n motive (k : Nat) => Nat with
      | zero => m
      | succ k ih => Nat.succ ih
      end
"};

#[test]
fn arithmetic_and_vectors() {
    check(&format!(
        "{}\n{}",
        include_str!("../../eqlog-ett/nat.ett"),
        include_str!("../../eqlog-ett/vec.ett")
    ))
    .unwrap();
}

const VEC: &str = indoc! {"
    inductive Vec (A : Type) : (n : Nat) -> Type where
    | nil : Vec A Nat.zero
    | cons (k : Nat) (x : A) (xs : Vec A k) : Vec A (Nat.succ k)
"};

#[test]
fn indexed_constructor_instantiations_are_checked() {
    let prefix = format!("{NAT}\n{VEC}\ninductive Bit where | off");
    check(&format!("{prefix}\ndef singleton (A : Type) (x : A) : Vec A (Nat.succ Nat.zero) := Vec.cons A Nat.zero x (Vec.nil A)")).unwrap();
    for declaration in [
        "def bad : Vec Nat Nat.zero := Vec.cons Nat Nat.zero Nat.zero (Vec.nil Nat)",
        "def bad : Vec Nat (Nat.succ Nat.zero) := Vec.nil Nat",
        "def bad : Vec Nat (Nat.succ Nat.zero) := Vec.cons Nat Nat.zero Bit.off (Vec.nil Nat)",
        "def bad : Vec Nat (Nat.succ Nat.zero) := Vec.cons Nat Bit.off Nat.zero (Vec.nil Nat)",
        "def bad : Vec Nat (Nat.succ Nat.zero) := Vec.cons Nat Nat.zero Nat.zero (Vec.nil Bit)",
        "def bad : Type := Vec Nat Bit.off",
        "def bad : Type := Vec Type Nat.zero",
    ] {
        assert!(
            check(&format!("{prefix}\n{declaration}")).is_err(),
            "{declaration}"
        );
    }
}

#[test]
fn type_parameters_and_inductive_schemas_are_checked() {
    for declaration in [
        "def bad : Type := Type",
        "def bad : Type := Nat",
        "def bad (A : Type) : Type := A",
        "inductive Bad : (A : Type) -> Type where",
        "def bad (x : Nat.zero) : Nat := Nat.zero",
        "def bad (A : Type) (B : Type) (x : A) : B := x",
        "inductive Bad where | mk (A : Type)",
        "inductive Bad (A : Type) where | mk (x : Bad Nat)",
        "inductive Bad (A : Type) where | mk : Bad Nat",
        "inductive Bad where | mk (x : Vec Bad Nat.zero)",
        "inductive Bad : (n : Nat) -> Type where | mk : Bad Type",
        "inductive Bad (Bad : Type) where | mk",
        "inductive Type where",
    ] {
        assert!(
            check(&format!("{NAT}\n{VEC}\n{declaration}")).is_err(),
            "{declaration}"
        );
    }
    let shadow = indoc! {"
        inductive Empty where
        inductive Void where
        def bad (Empty : Type) (x : Empty) : Void :=
          rec x motive (y : Empty) => Void with end
        def contradiction : Void := bad Nat Nat.zero
    "};
    assert!(check(&format!("{NAT}\n{shadow}")).is_err());
}

#[test]
fn types_are_not_terms_in_equality() {
    let prefix = formatdoc! {"
        {NAT}
        inductive I : (n : Nat) -> Type where
        | mk (n : Nat) : I n
        def out (n : Nat) (x : I n) : Nat :=
          rec n, x motive (k : Nat) (y : I k) => Nat with
          | mk j => j
          end
        theorem compute (n : Nat) : out n (I.mk n) = n := rfl
    "};
    check(&prefix).unwrap();
    assert!(check(&format!("{prefix}\ntheorem bad (h : I Nat.zero = I (Nat.succ Nat.zero)) : out (Nat.succ Nat.zero) (I.mk Nat.zero) = Nat.zero := rfl")).is_err());
    let parameters = formatdoc! {"
        {NAT}
        inductive Bit where | off
        inductive P (A : Type) where | mk (x : A)
        def out (A : Type) (p : P A) : A :=
          rec p motive (y : P A) => A with
          | mk x => x
          end
        theorem good (A : Type) (x : A) : out A (P.mk A x) = x := rfl
    "};
    check(&parameters).unwrap();
    assert!(check(&format!("{parameters}\ntheorem bad (h : P Nat = P Bit) : out Nat (P.mk Bit Bit.off) = Bit.off := rfl")).is_err());
}

#[test]
fn equality_can_validate_a_previously_untyped_application() {
    check(&formatdoc! {"
        {NAT}
        {VEC}
        def id (A : Type) (x : A) : A := x
        theorem same (A : Type) (x : A) : x = x := rfl
        theorem before (n : Nat) (xs : Vec Nat (add Nat.zero n)) :
          id (Vec Nat n) xs = xs :=
          let p : add Nat.zero n = n :=
            rec n motive (k : Nat) => add Nat.zero k = k with
            | zero => rfl
            | succ k ih => rfl
            end;
          same (Vec Nat n) (id (Vec Nat n) xs)
    "})
    .unwrap();
}

#[test]
fn other_sums_and_dependent_elimination() {
    check(indoc! {"
        inductive Bit where
        | off
        | on

        def flip (b : Bit) : Bit :=
          rec b motive (x : Bit) => Bit with
          | off => Bit.on
          | on => Bit.off
          end

        theorem involution (b : Bit) : flip (flip b) = b :=
          rec b motive (x : Bit) => flip (flip x) = x with
          | off => rfl
          | on => rfl
          end
    "})
    .unwrap();
}

#[test]
fn reflection_does_not_escape_its_context() {
    let valid =
        format!("{NAT}\ntheorem congr (a b : Nat) (h : a = b) : Nat.succ a = Nat.succ b := rfl");
    check(&valid).unwrap();
    let invalid = format!("{valid}\ntheorem false (a b : Nat) : a = b := rfl");
    assert!(check(&invalid)
        .err()
        .unwrap()
        .to_string()
        .contains("false:"));
}

#[test]
fn signatures_and_induction_hypotheses_do_not_prove_themselves() {
    for declaration in [
        "theorem false : Nat.zero = Nat.succ Nat.zero := rfl",
        "def false : Nat := rfl",
        "def false : Nat := missing",
        "def false : Nat := add Nat.zero",
        "def false : Nat := false",
        "theorem false (n : Nat) : n = Nat.zero := rec n motive (k : Nat) => k = Nat.zero with | zero => rfl | succ k ih => rfl end",
        "def false (n : Nat) : Nat := rec n motive (k : Nat) => Nat with | zero => Nat.zero end",
        "def false (n : Nat) : Nat := rec n motive (k : Nat) => Nat with | zero => Nat.zero | zero => Nat.zero | succ k ih => ih end",
        "def false : Nat := let bogus : Nat.zero = Nat.succ Nat.zero := rfl; Nat.zero",
    ] {
        assert!(check(&format!("{NAT}\n{declaration}")).is_err(), "{declaration}");
    }
    assert!(check(&format!(
        "{NAT}\ninductive Bit where | off\ndef false : Nat := add Bit.off Nat.zero"
    ))
    .is_err());
}

#[test]
fn instantiated_signatures_keep_their_lexical_bindings() {
    let prefix = format!(
        "{NAT}\ndef one : Nat := Nat.succ Nat.zero\ntheorem known : one = Nat.succ Nat.zero := rfl"
    );
    assert!(check(&format!(
        "{prefix}\ntheorem bad (one : Nat) : one = Nat.succ Nat.zero := known"
    ))
    .is_err());
    check(&format!("{NAT}\ntheorem same (n : Nat) (h : n = n) : n = n := h\ntheorem test (x : Nat) : x = x := same x rfl")).unwrap();
    check(&formatdoc! {"
        {NAT}
        def keep (k n : Nat) : Nat :=
          rec n motive (k : Nat) => Nat with
          | zero => k
          | succ j ih => k
          end
        theorem keeps (k : Nat) : keep k (Nat.succ Nat.zero) = k := rfl
    "})
    .unwrap();
}

#[test]
fn beta_allocations_stop_after_three_constructor_cases() {
    check(&format!("{NAT}\ntheorem two : add Nat.zero (Nat.succ (Nat.succ Nat.zero)) = Nat.succ (Nat.succ Nat.zero) := rfl")).unwrap();
    assert!(check(&format!("{NAT}\ntheorem three : add Nat.zero (Nat.succ (Nat.succ (Nat.succ Nat.zero))) = Nat.succ (Nat.succ (Nat.succ Nat.zero)) := rfl")).is_err());
    check(&format!("{NAT}\ntheorem cycle (n : Nat) (h : n = Nat.succ n) : add Nat.zero n = add Nat.zero n := rfl")).unwrap();
    let collapse = formatdoc! {"
        {NAT}
        def collapse (n : Nat) : Nat :=
          rec n motive (k : Nat) => Nat with
          | zero => Nat.zero
          | succ k ih => ih
          end
    "};
    check(&format!(
        "{collapse}\ntheorem two : collapse (Nat.succ (Nat.succ Nat.zero)) = Nat.zero := rfl"
    ))
    .unwrap();
    assert!(check(&format!("{collapse}\ntheorem three : collapse (Nat.succ (Nat.succ (Nat.succ Nat.zero))) = Nat.zero := rfl")).is_err());
}

#[test]
fn fresh_contexts_and_partial_images() {
    let mut m = Kernel::new();
    let root = m.define_empty();
    let data = m.new_data();
    let zero = m.new_constructor();
    let succ = m.new_constructor();
    let end = m.define_no_data_constructors();
    let cs = m.define_more_data_constructors(succ, end);
    let cs = m.define_more_data_constructors(zero, cs);
    m.insert_data_constructors(data, cs);
    let root_args = m.define_nil_args(root);
    let ty = m.define_data_type(root, data, root_args);
    m.insert_family_schema(root, ty);
    let x = m.new_context();
    let y = m.new_context();
    let px = m.new_context_mor();
    let py = m.new_context_mor();
    m.insert_extension(x, root, ty, px);
    m.insert_extension(y, root, ty, py);
    let x_args = m.define_nil_args(x);
    let x_ty = m.define_data_type(x, data, x_args);
    let x_zero = m.define_construct(x, zero, x_args);
    let hidden_args = m.define_cons_args(x, x_zero, x_args);
    let hidden = m.define_construct(x, succ, hidden_args);
    let body_args = m.define_cons_args(x, hidden, x_args);
    let body = m.define_construct(x, succ, body_args);
    m.insert_constructor_schema(x, x_zero, x_ty);
    m.insert_constructor_schema(x, hidden, x_ty);
    m.insert_constructor_schema(x, body, x_ty);
    let target = m.new_context();
    let f = m.new_context_mor();
    m.insert_advance(x, target, f);
    let image = m.new_tm(target);
    let target_args = m.define_nil_args(target);
    let image_ty = m.define_data_type(target, data, target_args);
    m.insert_type_image(f, x, x_ty, target, image_ty);
    m.insert_term_image(f, x, body, target, image);
    let variable = m.define_variable(x);
    let equality = m.define_equality(x, variable, x_zero);
    let assumption = m.new_context();
    let p = m.new_context_mor();
    m.insert_extension(assumption, x, equality, p);
    let local_variable = m.new_tm(assumption);
    let local_args = m.define_nil_args(assumption);
    let local_zero = m.define_construct(assumption, zero, local_args);
    m.define_data_type(assumption, data, local_args);
    m.insert_term_image(p, x, variable, assumption, local_variable);
    m.insert_term_image(p, x, x_zero, assumption, local_zero);
    m.close();
    assert!(m.valid(x) && m.valid(y));
    assert!(!m.are_equal_context(x, y));
    assert!(!m.are_equal_tm(variable, x_zero));
    assert!(m.are_equal_tm(local_variable, local_zero));
    assert_eq!(m.context_mor_dom(f), Some(x));
    assert_eq!(m.context_mor_cod(f), Some(target));
    assert!(m.has_type(target, image, image_ty));
    assert!(m.tm_mor_app(f, hidden).is_none());
    assert!(m.tm_mor_app(f, x_zero).is_none());
    assert_eq!(
        m.iter_context_member_tm()
            .filter(|(g, _)| *g == target)
            .count(),
        1
    );

    let target_zero = m.define_construct(target, zero, target_args);
    let target_hidden_args = m.define_cons_args(target, target_zero, target_args);
    let target_hidden = m.define_construct(target, succ, target_hidden_args);
    let target_body_args = m.define_cons_args(target, target_hidden, target_args);
    let target_body = m.define_construct(target, succ, target_body_args);
    m.close();
    assert_eq!(m.tm_mor_app(f, hidden), Some(target_hidden));
    assert!(m.are_equal_tm(image, target_body));
}

#[test]
fn fresh_type_parameters_support_polymorphic_substitution() {
    check(&formatdoc! {"
        {NAT}
        {VEC}
        def id (A : Type) (x : A) : A := x
        def keep (A B : Type) (x : A) (y : B) : A := id A x
        theorem keeps (A B : Type) (x : A) (y : B) :
          keep A B x y = x := rfl
        def proof_parameter (A : Type) (x : A) : x = x := id (x = x) rfl
        inductive At (A : Type) (a : A) where
        | mk
        def out (B : Type) (b : B) (x : At B b) : B :=
          rec x motive (y : At B b) => B with
          | mk => b
          end
        theorem out_mk (B : Type) (b : B) : out B b (At.mk B b) = b := rfl
        inductive Holds (n : Nat) (h : add Nat.zero n = n) where
        | mk
        def witness : Holds Nat.zero rfl := Holds.mk Nat.zero rfl
    "})
    .unwrap();
    let prefix = formatdoc! {"
        {NAT}
        inductive Bit where | off
        def id (A : Type) (x : A) : A := x
    "};
    for declaration in [
        "def bad : Nat := id Nat.zero Nat.zero",
        "def bad : Nat := id Type Nat.zero",
        "def bad (A : Type) (x : A) : Nat := id Nat x",
        "def bad (A : Type) (x : A) : A := id A Nat.zero",
        "def bad (A : Type) (x : A) : A := id x x",
        "theorem bad (A B : Type) : A = B := rfl",
        "theorem bad (h : Nat.zero = Bit.off) : Nat.zero = Nat.zero := rfl",
    ] {
        assert!(
            check(&format!("{prefix}\n{declaration}")).is_err(),
            "{declaration}"
        );
    }
}

#[test]
fn reflexivity_is_a_term_constructor() {
    let mut m = Kernel::new();
    let g = m.define_empty();
    let ty = m.new_ty(g);
    m.insert_family_schema(g, ty);
    let x = m.new_tm(g);
    m.insert_constructor_schema(g, x, ty);
    let proof = m.define_refl(g, x);
    let untyped = m.new_tm(g);
    let untyped_proof = m.define_refl(g, untyped);
    let ill_formed = m.define_equality(g, x, untyped);
    let invalid = m.new_context();
    let p = m.new_context_mor();
    m.insert_extension(invalid, g, ill_formed, p);
    m.close();
    let equality = m.equality(g, x, x).unwrap();
    assert!(m.is_type(g, equality));
    assert!(m.has_type(g, proof, equality));
    assert!(m.type_of(g, untyped_proof).is_none());
    assert!(!m.is_type(g, ill_formed));
    assert!(!m.valid(invalid));
    assert!(!m.substitution(p));

    let second_proof = m.new_tm(g);
    m.insert_constructor_schema(g, second_proof, equality);
    m.close();
    assert!(m.are_equal_tm(proof, second_proof));
}

#[test]
fn type_extension_is_fresh_and_type_pairing_waits_for_formation() {
    let mut m = Kernel::new();
    let root = m.define_empty();
    let e = m.new_context();
    let other = m.new_context();
    let p = m.new_context_mor();
    let other_p = m.new_context_mor();
    m.insert_type_extension(e, root, p);
    m.insert_type_extension(other, root, other_p);
    let a = m.define_type_variable(e);
    let other_a = m.define_type_variable(other);
    let base = m.define_context_mor_id(root);
    let ty = m.new_ty(root);
    let pair = m.define_pair_type(e, root, base, ty);
    let image = m.new_ty(root);
    m.insert_type_image(pair, e, a, root, image);
    m.close();
    assert!(m.valid(e) && m.valid(other));
    assert!(m.is_type(e, a) && m.is_type(other, other_a));
    assert!(!m.are_equal_context(e, other));
    assert!(!m.are_equal_ty(a, other_a));
    assert!(!m.substitution(pair));
    assert!(m.context_mor_dom(pair).is_none());
    assert!(m.context_mor_cod(pair).is_none());
    assert!(!m.is_type(root, image));

    m.insert_family_schema(root, ty);
    m.close();
    assert!(m.substitution(pair));
    assert!(m.are_equal_ty(m.ty_mor_app(pair, a).unwrap(), ty));
    assert!(m.are_equal_ty(image, ty));
    assert!(m.are_equal_context_mor(m.context_mor_comp(p, pair).unwrap(), base));

    let other_ty = m.new_ty(root);
    m.insert_family_schema(root, other_ty);
    let other_pair = m.define_pair_type(e, root, base, other_ty);
    m.close();
    assert!(m.substitution(other_pair));
    assert!(!m.are_equal_ty(ty, other_ty));
    assert!(!m.are_equal_context_mor(pair, other_pair));
}

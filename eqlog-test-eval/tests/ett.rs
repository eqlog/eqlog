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
        include_str!("../../examples/ett/nat.ett"),
        include_str!("../../examples/ett/vec.ett")
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
fn universes_and_inductive_schemas_are_checked() {
    for declaration in [
        "def bad : Type := Type",
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
fn equal_fibers_do_not_identify_indices_for_beta() {
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
        def id (A : Type) (x : A) : A := x
        theorem same (A : Type) (x : A) : x = x := rfl
        def code (n : Nat) : Type :=
          rec n motive (k : Nat) => Type with
          | zero => Nat
          | succ k ih => ih
          end
        theorem code_nat (n : Nat) : code n = Nat :=
          rec n motive (k : Nat) => code k = Nat with
          | zero => rfl
          | succ k ih => rfl
          end
        theorem before (n : Nat) : id (code n) Nat.zero = Nat.zero :=
          let p : code n = Nat := code_nat n;
          same Nat (id (code n) Nat.zero)
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
    m.insert_extension(x, root, ty);
    m.insert_extension(y, root, ty);
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
    let equality = m.define_identity(x, x_ty, variable, x_zero);
    let assumption = m.new_context();
    m.insert_extension(assumption, x, equality);
    let p = m.define_projection(assumption);
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

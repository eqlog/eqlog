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
fn natural_number_module() {
    check(include_str!("../../examples/ett/nat.ett")).unwrap();
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
}

#[test]
fn fresh_contexts_and_partial_images() {
    let mut m = Kernel::new();
    let root = m.define_empty();
    let data = m.new_data();
    let zero = m.new_constructor();
    let succ = m.new_constructor();
    m.insert_nullary(zero, data);
    m.insert_recursive(succ, data);
    let end = m.define_no_data_constructors();
    let cs = m.define_more_data_constructors(succ, end);
    let cs = m.define_more_data_constructors(zero, cs);
    m.insert_data_constructors(data, cs);
    let ty = m.define_data_type(root, data);
    let x = m.new_context();
    let y = m.new_context();
    m.insert_extension(x, root, ty);
    m.insert_extension(y, root, ty);
    let x_ty = m.define_data_type(x, data);
    let x_zero = m.define_constant(x, zero);
    let hidden = m.define_construct(x, succ, x_zero);
    let body = m.define_construct(x, succ, hidden);
    let target = m.new_context();
    let f = m.new_context_mor();
    m.insert_advance(x, target, f);
    let image = m.new_tm(target);
    let image_ty = m.define_data_type(target, data);
    m.insert_type_image(f, x, x_ty, target, image_ty);
    m.insert_term_image(f, x, body, target, image);
    let variable = m.define_variable(x);
    let equality = m.define_identity(x, x_ty, variable, x_zero);
    let assumption = m.new_context();
    m.insert_extension(assumption, x, equality);
    let p = m.define_projection(assumption);
    let local_variable = m.new_tm(assumption);
    let local_zero = m.define_constant(assumption, zero);
    m.define_data_type(assumption, data);
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

    let target_zero = m.define_constant(target, zero);
    let target_hidden = m.define_construct(target, succ, target_zero);
    let target_body = m.define_construct(target, succ, target_hidden);
    m.close();
    assert_eq!(m.tm_mor_app(f, hidden), Some(target_hidden));
    assert!(m.are_equal_tm(image, target_body));
}

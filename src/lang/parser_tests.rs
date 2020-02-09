use super::parser::*;
use super::ast::*;

macro_rules! assert_parse {
    ($parse:expr, $expected:expr) => {
        match $parse {
            Ok(result) => assert_eq!(result, $expected),
            Err(err) => panic!("{}", err),
        }
    }
}

fn id(name: &str) -> Expr {
    Expr::App(name.to_string(), vec![])
}

fn discard() -> DefId {
    None
}

fn name(name: &str) -> DefId {
    Some(name.to_string())
}

#[test]
fn bool() {
    assert_parse!(
        ExprParser::new().parse("bool"),
        id("bool")
    );
}

#[test]
fn discard_() {
    assert_parse!(
        DefIdParser::new().parse("_"),
        discard());
}

#[test]
fn x() {
    assert_parse!(
        DefIdParser::new().parse("x"),
        name("x")
    );
}

#[test]
fn ctx_ext() {
    assert_parse!(
        CtxExtsParser::new().parse("(x : bool)"),
        vec![CtxExt(name("x"), id("bool"))]);
}

#[test]
fn negb() {
    let negb = "
def negb (x : bool) : bool :=
  elim x into (_ : bool) : bool
  | => false
  | => true
  end.";
  assert_parse!(
      DefParser::new().parse(negb),
      Def {
          name: name("negb"),
          ctx: vec![CtxExt(Some("x".to_string()), id("bool"))],
          ret_ty: id("bool"),
          body:
            Expr::Elim {
                val: Box::new(id("x")),
                into_ctx: vec![CtxExt(discard(), id("bool"))],
                into_ty: Box::new(id("bool")),
                cases: vec![
                    ElimCase(vec![], id("false")),
                    ElimCase(vec![], id("true")),
                ]
            }
      });
}

#[test]
fn eq_plus() {
    let eq_plus = "a + b = c + e + f";
    assert_parse!(
        ExprParser::new().parse(eq_plus),
        Expr::App(
            "eq".to_string(),
            vec![
                Expr::App(
                    "plus".to_string(),
                    vec![id("a"), id("b")]
                ),
                Expr::App(
                    "plus".to_string(),
                    vec![
                        Expr::App(
                            "plus".to_string(),
                            vec![id("c"), id("e")]
                        ),
                        id("f"),
                    ],
                ),
            ]
        )
    )
}

#[test]
fn let_eq() {
    let multi_let = "
let x : bool := true in
let y : bool := false in
x = y";
    assert_parse!(
        ExprParser::new().parse(multi_let),
        Expr::Let {
            name: Some("x".to_string()),
            ty: Box::new(id("bool")),
            val: Box::new(id("true")),
            body: Box::new(
                Expr::Let {
                    name: Some("y".to_string()),
                    ty: Box::new(id("bool")),
                    val: Box::new(id("false")),
                    body: Box::new(
                        Expr::App(
                            "eq".to_string(),
                            vec![id("x"), id("y")]
                        )
                    )
                }
            )
        }
    );
}

#[test]
fn app() {
    assert_parse!(
        ExprParser::new().parse("plus a b"),
        Expr::App("plus".to_string(), vec![id("a"), id("b")])
    );
}

#[test]
fn app2() {
    assert_parse!(
        ExprParser::new().parse("plus a (plus b c)"),
        Expr::App(
            "plus".to_string(),
            vec![
                id("a"),
                Expr::App(
                    "plus".to_string(),
                    vec![id("b"), id("c")]
                )
            ]
        )
    );
}

#[test]
fn zero() {
    assert_parse!(
        ExprParser::new().parse("0"),
        id("O")
    );
}

#[test]
fn three() {
    assert_parse!(
        ExprParser::new().parse("3"),
        Expr::App(
            "S".to_string(),
            vec![
                Expr::App(
                    "S".to_string(),
                    vec![
                        Expr::App(
                            "S".to_string(),
                            vec![id("O")]
                        )
                    ]
                )
            ]
        )
    );
}
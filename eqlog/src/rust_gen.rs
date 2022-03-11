use std::io::{self, Write};
use crate::direct_ast::*;
use crate::signature::Signature;
use crate::index_selection::*;
use std::fmt::{self, Formatter, Display};
use crate::query_action::*;
use std::iter::{once, repeat};
use std::collections::BTreeSet;

fn write_imports(out: &mut impl Write) -> io::Result<()> {
    write!(out, 
    "#[allow(non_snake_case, non_camel_case_types, unused_mut, unused_variables, unused_imports, unused_parens, clippy::all)]\n"
    )?;
    write!(out, "use std::collections::BTreeSet;\n")?;
    write!(out, "use eqlog_util::Unification;\n")?;
    Ok(())
}

// #[derive(Copy, Clone, PartialEq, Eq, Debug, Hash, PartialOrd, Ord)]
// pub struct SortName(pub u32);
fn write_sort_type(out: &mut impl Write, sort: &Sort) -> io::Result<()> {
    write!(out, "#[derive(Copy, Clone, PartialEq, Eq, Debug, Hash, PartialOrd, Ord)]\n")?;
    write!(out, "pub struct {}(pub u32);\n", sort.0)?;
    Ok(())
}

// #[derive(Copy, Clone, PartialEq, Eq, Debug, Hash, PartialOrd, Ord)]
// pub struct RelationName(pub SortOne, pub SortTwo, ..., pub SortN);
fn write_tuple_type(
    out: &mut impl Write,
    relation: &str,
    arity: &[&str],
) -> io::Result<()> {
    write!(out, "#[derive(Copy, Clone, PartialEq, Eq, Debug, Hash, PartialOrd, Ord)]\n")?;
    write!(out, "pub struct {}(", relation)?;
    if arity.is_empty() {
        write!(out, ")")?;
    } else {
        for arg_sort in arity[0 .. arity.len() - 1].iter() {
            write!(out, "pub {}, ", arg_sort)?;
        }
        write!(out, "pub {})", arity.last().unwrap())?;
    }
    write!(out, ";\n")?;
    Ok(())
}

fn write_sort_fields(
    out: &mut impl Write,
    name: &str,
) -> io::Result<()> {
    write!(out, "  {}: Unification<{}>,\n", name, name)?;
    write!(out, "  {}_dirty: {},\n", name, name)?;
    Ok(())
}

#[derive(Copy, Clone, PartialEq, Eq, Debug, Hash)]
enum TupleAge{All, Dirty}

impl Display for TupleAge {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            TupleAge::All => write!(f, "all"),
            TupleAge::Dirty => write!(f, "dirty"),
        }
    }
}

fn write_relation_field_name(
    out: &mut impl Write,
    name: &str,
    age: TupleAge,
) -> io::Result<()> {
    write!(out, "{}_{}", name, age)?;
    Ok(())
}

fn write_relation_field(
    out: &mut impl Write,
    name: &str,
    age: TupleAge,
) -> io::Result<()> {
    write!(out, "  ")?;
    write_relation_field_name(out, name, age)?;
    write!(out, ": BTreeSet<{}>,\n", name)?;
    Ok(())
}

fn write_is_dirty_impl(
    out: &mut impl Write,
    signature: &Signature,
) -> io::Result<()> {
    write!(out, "  fn is_dirty(&self) -> bool {{\n")?;
    write!(out, "    false\n")?;
    for (relation, _) in signature.relations() {
        write!(out, "      || !self.{}_dirty.is_empty()\n", relation)?;
    }
    write!(out, "  }}\n")?;
    Ok(())
}

fn write_iter_name(
    out: &mut impl Write,
    relation: &str,
    query: &QuerySpec,
    age: TupleAge,
) -> io::Result<()> {
    write!(out, "iter_{}_{}", relation, age)?;
    for p in query.projections.iter() {
        write!(out, "_{}", p)?;
    }
    for diag in query.diagonals.iter() {
        write!(out, "_diagonal")?;
        for d in diag.iter() {
            write!(out, "_{}", d)?;
        }
    }
    Ok(())
}

fn write_iter_impl(
    out: &mut impl Write,
    relation: &str,
    arity: &[&str],
    query: &QuerySpec,
    age: TupleAge,
) -> io::Result<()> {
    write!(out, "  fn ")?;
    write_iter_name(out, relation, query, age)?;
    write!(out, "(&self")?;
    for i in query.projections.iter().copied() {
        write!(out, ", arg{}: {}", i, arity[i])?;
    }
    write!(out, ") -> impl Iterator<Item=&{}> {{\n", relation)?;
    write!(out, "    self.")?;
    write_relation_field_name(out, relation, age)?;
    write!(out, ".iter().filter(move |t| {{\n")?;

    write!(out, "      let proj_matches = true")?;
    for i in query.projections.iter().copied() {
        write!(out, " && t.{} == arg{}", i, i)?;
    }
    write!(out, ";\n")?;

    for (k, diagonal) in query.diagonals.iter().enumerate() {
        write!(out, "      let diag{}_matches = true", k)?;
        for (prev, next) in diagonal.iter().zip(diagonal.iter().skip(1)) {
            write!(out, " && t.{} == t.{}", prev, next)?;
        }
        write!(out, ";\n")?;
    }

    write!(out, "      proj_matches")?;
    for k in 0 .. query.diagonals.len() {
        write!(out, " && diag{}_matches", k)?;
    }
    write!(out, "\n")?;

    write!(out, "    }})\n")?;
    write!(out, "  }}\n")?;
    Ok(())
}

fn write_query_loop_headers<'a>(
    out: &mut impl Write,
    signature: &Signature,
    query_ages: impl Iterator<Item=(&'a Query, TupleAge)>,
) -> io::Result<()> {
    let mut indent = 3;
    for (query, age) in query_ages {
        for _ in 0 .. indent {
            write!(out, "  ")?;
        }
        indent += 1;

        use Query::*;
        match query {
            Relation{relation, diagonals, projections, results} => {
                let arity_len =
                    signature.relations()
                    .find(|(rel, _)| rel == relation)
                    .unwrap().1.len();
                let query_spec = QuerySpec {
                    diagonals: diagonals.clone(),
                    projections: projections.keys().copied().collect(),
                };
                write!(out, "for {}(", relation)?;
                for i in 0 .. arity_len {
                    if let Some(tm) = results.get(&i) {
                        if let Some(diag) = diagonals.iter().find(|diag| diag.contains(&i)) {
                            if *diag.iter().next().unwrap() == i {
                                write!(out, "tm{}", tm.0)?;
                            } else {
                                write!(out, "_")?;
                            }
                        } else {
                            write!(out, "tm{}", tm.0)?;
                        }
                    } else {
                        write!(out, "_")?;
                    }
                    write!(out, ", ")?;
                }
                write!(out, ") in self.")?;
                write_iter_name(out, relation, &query_spec, age)?;
                write!(out, "(")?;
                for tm in projections.values().copied() {
                    write!(out, "tm{}, ", tm.0)?;
                }
                write!(out, ") {{\n")?;
            },
            Sort{..} => {
                panic!("Not implemented")
            },
        }
    }
    Ok(())
}

fn write_query_loop_footers(
    out: &mut impl Write,
    query_len: usize,
) -> io::Result<()> {
    let mut indent = 2 + query_len;
    while indent > 2 {
        for _ in 0 .. indent {
            write!(out, "  ")?;
        }
        indent -= 1;
        write!(out, "}}\n")?;
    }
    Ok(())
}

fn write_action(
    out: &mut impl Write,
    signature: &Signature,
    action: &Action,
    indent: usize,
) -> io::Result<()> {
    use Action::*;
    match action {
        AddTerm{function, args, result} => {
            let Function{dom, cod, ..} = signature.functions().get(function).unwrap();
            let query_spec = QuerySpec {
                projections: (0 .. dom.len()).collect(),
                diagonals: BTreeSet::new(),
            };

            for _ in 0 .. indent { write!(out, "  ")?; }
            write!(out, "let tm{} = match self.", result.0)?;
            write_iter_name(out, function, &query_spec, TupleAge::All)?;
            write!(out, "(")?;
            for arg in args {
                write!(out, "tm{}, ", arg.0)?;
            }
            write!(out, ").next() {{\n")?;

            for _ in 0 .. indent + 1 { write!(out, "  ")?; }
            write!(out, "Some(result) => result,\n")?;

            for _ in 0 .. indent + 1 { write!(out, "  ")?; }
            write!(out, "None => self.{}.new(),\n", cod)?;

            for _ in 0 .. indent { write!(out, "  ")?; }
            write!(out, "}}\n")?;

            for _ in 0 .. indent { write!(out, "  ")?; }
            write!(out, "{}_new.push({}(", function, function)?;
            for tm in args.iter().chain(once(result)) {
                write!(out, "tm{}, ", tm.0)?;
            }
            write!(out, "));\n")?;
        },
        AddTuple{relation, args} => {
            for _ in 0 .. indent {
                write!(out, "  ")?;
            }
            write!(out, "{}_new.push({}(", relation, relation)?;
            for tm in args {
                write!(out, "tm{}, ", tm.0)?;
            }
            write!(out, "));\n")?;
        },
        Equate{sort, lhs, rhs} => {
            for _ in 0 .. indent {
                write!(out, "  ")?;
            }
            write!(out, "{}_new_eqs.push((tm{}, tm{}));\n", sort, lhs.0, rhs.0)?;
        },
    }
    Ok(())
}

fn write_closure(
    out: &mut impl Write,
    signature: &Signature,
    query_actions: &[QueryAction],
) -> io::Result<()> {
    write!(out, "  pub fn close(&mut self) {{\n")?;
    for (relation, _) in signature.relations() {
        write!(out, "    let mut {}_new: Vec<{}> = Vec::new();\n", relation, relation)?;
    }
    write!(out, "\n")?;
    for (sort, _) in signature.sorts() {
        write!(out, "    let mut {}_new_eqs: Vec<({}, {})> = Vec::new();\n", sort, sort, sort)?;
    }
    write!(out, "\n")?;

    write!(out, "    while self.is_dirty() {{\n")?;
    for query_action in query_actions {
        let queries_len = query_action.queries.len();
        for new_index in 0 .. queries_len {
            let ages =
                repeat(TupleAge::All).take(new_index)
                .chain(once(TupleAge::Dirty))
                .chain(repeat(TupleAge::All).take(queries_len - new_index - 1));
            let query_ages = query_action.queries.iter().zip(ages);
            write_query_loop_headers(out, signature, query_ages)?;
            for action in query_action.actions.iter() {
                write_action(out, signature, action, queries_len + 3)?;
            }
            write_query_loop_footers(out, queries_len)?;
        }
        write!(out, "\n")?;
    }

    for (relation, _) in signature.relations() {
        write!(out, "      self.{}_dirty.clear();\n", relation)?;
        write!(out, "      for t in {}_new.drain(..) {{\n", relation)?;
        write!(out, "        if self.{}_all.insert(t) {{\n", relation)?;
        write!(out, "          self.{}_dirty.insert(t); \n", relation)?;
        write!(out, "        }}\n")?;
        write!(out, "      }}\n")?;
        write!(out, "\n")?;
    }

    for (sort, _) in signature.sorts() {
        write!(out, "      if !{}_new_eqs.is_empty() {{\n", sort)?;
        write!(out, "        panic!(\"Equalities not implemented\");\n")?;
        write!(out, "      }}\n")?;
    }

    write!(out, "    }}\n")?;

    write!(out, "  }}\n")?;
    Ok(())
}

fn write_theory_struct(
    out: &mut impl Write,
    name: &str,
    signature: &Signature,
) -> io::Result<()> {
    write!(out, "pub struct {} {{\n", name)?;
    for sort in signature.sorts().keys() {
        write_sort_fields(out, sort.as_str())?;
        write!(out, "\n")?;
    }

    for (rel, _) in signature.relations() {
        write_relation_field(out, rel, TupleAge::All)?;
        write_relation_field(out, rel, TupleAge::Dirty)?;
        write!(out, "\n")?;
    }
    write!(out, "}}\n")?;
    Ok(())
}

fn write_theory_impl(
    out: &mut impl Write,
    name: &str,
    signature: &Signature,
    query_actions: &[QueryAction],
    index_selection: &IndexSelection,
) -> io::Result<()> {
    write!(out, "impl {} {{\n", name)?;
    for (rel, arity) in signature.relations() {
        let query_index_map = index_selection.get(rel).unwrap();
        for query in query_index_map.keys() {
            write_iter_impl(out, rel, &arity, query, TupleAge::All)?;
            write_iter_impl(out, rel, &arity, query, TupleAge::Dirty)?;
        }
        write!(out, "\n")?;
    }

    write_is_dirty_impl(out, signature)?;
    write!(out, "\n")?;

    write_closure(out, signature, query_actions)?;

    write!(out, "}}\n")?;
    Ok(())
}

pub fn write_theory(
    out: &mut impl Write,
    name: &str,
    signature: &Signature,
    query_actions: &[QueryAction],
    index_selection: &IndexSelection,
) -> io::Result<()> {
    write_imports(out)?;

    write!(out, "\n")?;
    for sort in signature.sorts().values() {
        write_sort_type(out, sort)?;
    }

    write!(out, "\n")?;
    for (rel, arity) in signature.relations() {
        write_tuple_type(out, rel, &arity)?;
    }
    write!(out, "\n")?;

    write_theory_struct(out, name, signature)?;
    write_theory_impl(out, name, signature, query_actions, index_selection)?;

    Ok(())
}

#[cfg(test)]
mod tests {

use crate::flat_ast::*;
use super::*;

#[test]
fn asdf() {
    use indoc::indoc;
    use crate::grammar::TheoryParser;
    let src = indoc! {"
        Sort Obj;
        Sort Mor;

        Func Comp : Mor * Mor -> Mor;
        Pred Signature: Obj * Mor * Obj;
        Func Id : Obj -> Mor;
        
        Axiom Signature(x, f, y) & Signature(y, g, z) => Comp(g, f)! & Signature(x, Comp(g, f), z);
    "};
        //Axiom Signature(x, f, x) & Signature(y, f, y) => x = y;
        //Axiom Comp(h, Comp(g, f)) ~> Comp(Comp(h, g), f);
    let (sig, axioms) = TheoryParser::new().parse(src).unwrap();
    let query_actions: Vec<QueryAction> =
        axioms.iter()
        .map(|(seq, sorts)| QueryAction::new(&sig, &flatten_sequent(seq, sorts)))
        .collect();

    let index_selection = select_indices(&sig, &query_actions);

    let stdout = io::stdout();
    let mut handle = stdout.lock();
    write_imports(&mut handle)?;
    write_theory(&mut handle, "Cat", &sig, &query_actions, &index_selection).unwrap();
    //panic!()
}

}

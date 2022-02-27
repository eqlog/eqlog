use std::io::{self, Write};
use crate::direct_ast::*;
use crate::signature::Signature;
use crate::index_selection::*;
use std::fmt::{self, Formatter, Display};
use crate::flat_ast::*;

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
    write!(out, "  {}_clean_until: {},\n", name, name)?;
    Ok(())
}

#[derive(Copy, Clone, PartialEq, Eq, Debug, Hash)]
enum TupleAge{Old, New}
impl Display for TupleAge {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            TupleAge::Old => write!(f, "old"),
            TupleAge::New => write!(f, "new"),
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
    write!(out, ": BTreeMap<{}>,\n", name)?;
    Ok(())
}

fn write_query_name(
    out: &mut impl Write,
    relation: &str,
    query: &QuerySpec,
    age: TupleAge,
) -> io::Result<()> {
    write!(out, "{}_query_{}", relation, age)?;
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

fn write_query_impl(
    out: &mut impl Write,
    relation: &str,
    arity: &[&str],
    query: &QuerySpec,
    age: TupleAge,
) -> io::Result<()> {
    write!(out, "  fn ")?;
    write_query_name(out, relation, query, age)?;
    write!(out, "(")?;
    for i in query.projections.iter().copied() {
        write!(out, "arg{}: {}, ", i, arity[i])?;
    }
    write!(out, ") -> impl Iterator<Item=&{}> {{\n", relation)?;
    write!(out, "    ")?;
    write_relation_field_name(out, relation, age)?;
    write!(out, ".iter().filter(|t| {{\n")?;

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

fn write_theory(
    out: &mut impl Write,
    name: &str,
    signature: &Signature,
    index_selection: &IndexSelection,
) -> io::Result<()> {
    for sort in signature.sorts().values() {
        write_sort_type(out, sort)?;
    }

    write!(out, "\n")?;
    for (rel, arity) in signature.relations() {
        write_tuple_type(out, rel, &arity)?;
    }
    write!(out, "\n")?;

    write!(out, "pub struct {} {{\n", name)?;
    for sort in signature.sorts().keys() {
        write_sort_fields(out, sort.as_str())?;
        write!(out, "\n")?;
    }

    for (rel, arity) in signature.relations() {
        write_relation_field(out, rel, TupleAge::New)?;
        write_relation_field(out, rel, TupleAge::Old)?;
        let query_index_map = index_selection.get(rel).unwrap();
        for query in query_index_map.keys() {
            write_query_impl(out, rel, &arity, query, TupleAge::Old)?;
            write_query_impl(out, rel, &arity, query, TupleAge::New)?;
        }
        write!(out, "\n")?;
    }
    write!(out, "}}\n")?;

    Ok(())
}

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
        
        Axiom Signature(x, f, x) & Signature(y, f, y) => x = y;
    "};
    let (sig, axioms) = TheoryParser::new().parse(src).unwrap();
    let flat_axioms: Vec<FlatSequent> =
        axioms.iter()
        .map(|(seq, sorts)| flatten_sequent(seq, sorts))
        .collect();
    let index_selection = select_indices(&sig, &flat_axioms);

    let stdout = io::stdout();
    let mut handle = stdout.lock();
    write_theory(&mut handle, "Cat", &sig, &index_selection).unwrap();
    panic!()
}

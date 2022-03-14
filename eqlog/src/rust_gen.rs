use crate::direct_ast::*;
use crate::flat_ast::*;
use crate::index_selection::*;
use crate::query_action::*;
use crate::signature::Signature;
use convert_case::{Case, Casing};
use indoc::writedoc;
use std::collections::BTreeMap;
use std::collections::BTreeSet;
use std::fmt::{self, Display, Formatter};
use std::io::{self, Write};
use std::iter::{once, repeat};

use Case::Snake;

fn write_imports(out: &mut impl Write) -> io::Result<()> {
    write!(out, "use std::collections::BTreeSet;\n")?;
    write!(out, "use std::collections::HashSet;\n")?;
    write!(out, "use eqlog_util::Unification;\n")?;
    Ok(())
}

// #[derive(Copy, Clone, PartialEq, Eq, Debug, Hash, PartialOrd, Ord)]
// pub struct SortName(pub u32);
fn write_sort_type(out: &mut impl Write, sort: &Sort) -> io::Result<()> {
    write!(out, "#[allow(dead_code)]\n")?;
    write!(
        out,
        "#[derive(Copy, Clone, PartialEq, Eq, Debug, Hash, PartialOrd, Ord)]\n"
    )?;
    write!(out, "pub struct {}(pub u32);\n", sort.0)?;
    Ok(())
}

fn write_sort_from_u32_impl(out: &mut impl Write, sort: &Sort) -> io::Result<()> {
    write!(
        out,
        "impl Into<u32> for {} {{ fn into(self) -> u32 {{ self.0 }} }}\n",
        sort.0
    )?;
    Ok(())
}

fn write_sort_into_u32_impl(out: &mut impl Write, sort: &Sort) -> io::Result<()> {
    write!(
        out,
        "impl From<u32> for {} {{ fn from(x: u32) -> Self {{ {}(x) }} }}\n",
        sort.0, sort.0
    )?;
    Ok(())
}

// #[derive(Copy, Clone, PartialEq, Eq, Debug, Hash, PartialOrd, Ord)]
// pub struct RelationName(pub SortOne, pub SortTwo, ..., pub SortN);
fn write_tuple_type(out: &mut impl Write, relation: &str, arity: &[&str]) -> io::Result<()> {
    write!(out, "#[allow(dead_code)]\n")?;
    write!(
        out,
        "#[derive(Copy, Clone, PartialEq, Eq, Debug, Hash, PartialOrd, Ord)]\n"
    )?;
    write!(out, "pub struct {}(", relation)?;
    if arity.is_empty() {
        write!(out, ")")?;
    } else {
        for arg_sort in arity[0..arity.len() - 1].iter() {
            write!(out, "pub {}, ", arg_sort)?;
        }
        write!(out, "pub {})", arity.last().unwrap())?;
    }
    write!(out, ";\n")?;
    Ok(())
}

fn write_sort_fields(out: &mut impl Write, name: &str) -> io::Result<()> {
    write!(
        out,
        "{}_equalities: Unification<{}>,\n",
        name.to_case(Snake),
        name
    )?;
    write!(out, "{}_all: HashSet<{}>,\n", name.to_case(Snake), name)?;
    write!(out, "{}_dirty: HashSet<{}>,\n", name.to_case(Snake), name)?;
    Ok(())
}

#[derive(Copy, Clone, PartialEq, Eq, Debug, Hash)]
enum TupleAge {
    All,
    Dirty,
}

impl Display for TupleAge {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            TupleAge::All => write!(f, "all"),
            TupleAge::Dirty => write!(f, "dirty"),
        }
    }
}

fn write_relation_field_name(out: &mut impl Write, name: &str, age: TupleAge) -> io::Result<()> {
    write!(out, "{}_{}", name.to_case(Snake), age)?;
    Ok(())
}

fn write_relation_field(out: &mut impl Write, name: &str, age: TupleAge) -> io::Result<()> {
    write_relation_field_name(out, name, age)?;
    write!(out, " : BTreeSet<{}>,\n", name)?;
    Ok(())
}

fn write_is_dirty_impl(out: &mut impl Write, signature: &Signature) -> io::Result<()> {
    write!(out, "fn is_dirty(&self) -> bool {{\n")?;
    write!(out, "false")?;
    for (relation, _) in signature.relations() {
        write!(
            out,
            " || !self.{}_dirty.is_empty()",
            relation.to_case(Snake)
        )?;
    }
    for sort in signature.sorts().keys() {
        let sort_snake = sort.to_case(Snake);
        writedoc!(out, " || !self.{sort_snake}_dirty.is_empty()")?;
    }
    write!(out, "}}\n")?;
    Ok(())
}

fn write_iter_name(
    out: &mut impl Write,
    relation: &str,
    query: &QuerySpec,
    age: TupleAge,
) -> io::Result<()> {
    write!(out, "iter_{}_{}", relation.to_case(Snake), age)?;
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
    write!(out, "#[allow(dead_code)]\n")?;
    write!(out, "fn ")?;
    write_iter_name(out, relation, query, age)?;
    write!(out, "(&self")?;
    for i in query.projections.iter().copied() {
        write!(out, ", arg{}: {}", i, arity[i])?;
    }
    write!(out, ") -> impl '_ + Iterator<Item={}> {{\n", relation)?;
    write!(out, "self.")?;
    write_relation_field_name(out, relation, age)?;
    write!(out, ".iter().filter(move |_t| {{\n")?;

    write!(out, "let proj_matches = true")?;
    for i in query.projections.iter().copied() {
        write!(out, " && _t.{} == arg{}", i, i)?;
    }
    write!(out, ";\n")?;

    for (k, diagonal) in query.diagonals.iter().enumerate() {
        write!(out, "let diag{}_matches = true", k)?;
        for (prev, next) in diagonal.iter().zip(diagonal.iter().skip(1)) {
            write!(out, " && _t.{} == _t.{}", prev, next)?;
        }
        write!(out, ";\n")?;
    }

    write!(out, "proj_matches")?;
    for k in 0..query.diagonals.len() {
        write!(out, " && diag{}_matches", k)?;
    }
    write!(out, "\n")?;

    write!(out, "}}).copied()\n")?;
    write!(out, "}}\n")?;
    Ok(())
}

fn write_pub_iter(out: &mut impl Write, relation: &str) -> io::Result<()> {
    let rel_snake = relation.to_case(Snake);
    writedoc!(
        out,
        "
        #[allow(dead_code)]
        pub fn iter_{rel_snake}(&self) -> impl '_ + Iterator<Item={relation}> {{
            self.iter_{rel_snake}_all()
        }}
    "
    )?;
    Ok(())
}

fn write_pub_insert_relation(
    out: &mut impl Write,
    relation: &str,
    arity: &[&str],
) -> io::Result<()> {
    let relation_snake = relation.to_case(Snake);
    writedoc!(
        out,
        "
        #[allow(dead_code)]
        pub fn insert_{relation_snake}(&mut self, mut t : {relation}) {{
    "
    )?;
    for (i, sort) in arity.iter().enumerate() {
        let sort_snake = sort.to_case(Snake);
        writedoc!(
            out,
            "
            t.{i} = self.{sort_snake}_equalities.root(t.{i});
        "
        )?;
    }
    writedoc!(
        out,
        "
        self.{relation_snake}_all.insert(t);
        self.{relation_snake}_dirty.insert(t);
        }}
    "
    )?;
    Ok(())
}

fn write_pub_new_element(out: &mut impl Write, sort: &str) -> io::Result<()> {
    let sort_snake = sort.to_case(Snake);
    writedoc!(
        out,
        "
        #[allow(dead_code)]
        pub fn new_{sort_snake}(&mut self) -> {sort} {{
            let size = self.{sort_snake}_equalities.len();
            self.{sort_snake}_equalities.increase_size(size + 1);
            let el = {sort}::from(size as u32);
            self.{sort_snake}_dirty.insert(el);
            self.{sort_snake}_all.insert(el);
            el
        }}
    "
    )?;
    Ok(())
}

fn write_pub_iter_sort(out: &mut impl Write, sort: &str) -> io::Result<()> {
    let sort_snake = sort.to_case(Snake);
    writedoc!(
        out,
        "
        #[allow(dead_code)]
        pub fn iter_{sort_snake}(&mut self) -> impl '_ + Iterator<Item={sort}> {{
            self.{sort_snake}_all.iter().copied()
        }}
    "
    )?;
    Ok(())
}

fn write_query_loop_headers<'a>(
    out: &mut impl Write,
    signature: &Signature,
    query_ages: impl Iterator<Item = (&'a Query, TupleAge)>,
) -> io::Result<()> {
    for (query, age) in query_ages {
        use Query::*;
        match query {
            Relation {
                relation,
                diagonals,
                projections,
                results,
            } => {
                let arity_len = signature
                    .relations()
                    .find(|(rel, _)| rel == relation)
                    .unwrap()
                    .1
                    .len();
                let query_spec = QuerySpec {
                    diagonals: diagonals.clone(),
                    projections: projections.keys().copied().collect(),
                };
                write!(out, "#[allow(unused_variables)]\n")?;
                write!(out, "for {}(", relation)?;
                for i in 0..arity_len {
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
            }
            Sort { sort, result } => {
                write!(out, "#[allow(unused_variables)]\n")?;
                write!(
                    out,
                    "for tm{} in self.{}_{}.iter().copied() {{\n",
                    result.0,
                    sort.to_case(Snake),
                    age
                )?;
            }
        }
    }
    Ok(())
}

fn write_query_loop_footers(out: &mut impl Write, query_len: usize) -> io::Result<()> {
    for _ in 0..query_len {
        write!(out, "}}\n")?;
    }
    Ok(())
}

fn write_action(out: &mut impl Write, signature: &Signature, action: &Action) -> io::Result<()> {
    use Action::*;
    match action {
        AddTerm {
            function,
            args,
            result,
        } => {
            let Function { dom, cod, .. } = signature.functions().get(function).unwrap();
            let query_spec = QuerySpec {
                projections: (0..dom.len()).collect(),
                diagonals: BTreeSet::new(),
            };

            write!(out, "#[allow(unused_variables)]\n")?;
            write!(out, "let tm{} = match self.", result.0)?;
            write_iter_name(out, function, &query_spec, TupleAge::All)?;
            write!(out, "(")?;
            for arg in args {
                write!(out, "tm{}, ", arg.0)?;
            }
            write!(out, ").next() {{\n")?;

            write!(out, "Some(result) => result.{},\n", dom.len())?;

            write!(out, "None => {{\n")?;

            write!(
                out,
                "let new_el = {}((self.{}_equalities.len() + {}_new_el_num) as u32);\n",
                cod,
                cod.to_case(Snake),
                cod.to_case(Snake)
            )?;

            write!(out, "{}_new_el_num += 1;\n", cod.to_case(Snake))?;

            write!(out, "{}_new.push({}(", function.to_case(Snake), function)?;
            for tm in args.iter() {
                write!(out, "tm{}, ", tm.0)?;
            }
            write!(out, "new_el));\n")?;

            write!(out, "new_el\n")?;

            write!(out, "}},\n")?;

            write!(out, "}};\n")?;
        }
        AddTuple { relation, args } => {
            write!(out, "{}_new.push({}(", relation.to_case(Snake), relation)?;
            for tm in args {
                write!(out, "tm{}, ", tm.0)?;
            }
            write!(out, "));\n")?;
        }
        Equate { sort, lhs, rhs } => {
            write!(
                out,
                "{}_new_eqs.push((tm{}, tm{}));\n",
                sort.to_case(Snake),
                lhs.0,
                rhs.0
            )?;
        }
    }
    Ok(())
}

fn write_query_action_step(
    out: &mut impl Write,
    signature: &Signature,
    query_action: &QueryAction,
) -> io::Result<()> {
    let queries_len = query_action.queries.len();
    for new_index in 0..queries_len {
        let ages = repeat(TupleAge::All)
            .take(new_index)
            .chain(once(TupleAge::Dirty))
            .chain(repeat(TupleAge::All).take(queries_len - new_index - 1));
        let query_ages = query_action.queries.iter().zip(ages);
        write_query_loop_headers(out, signature, query_ages)?;
        for action in query_action.actions.iter() {
            write_action(out, signature, action)?;
        }
        write_query_loop_footers(out, queries_len)?;
    }
    Ok(())
}

fn write_functionality_step(
    out: &mut impl Write,
    signature: &Signature,
    function: &Function,
) -> io::Result<()> {
    let Function { name, dom, cod } = function;

    let new_result = FlatTerm(dom.len());
    let old_result = FlatTerm(dom.len() + 1);

    let dirty_query = Query::Relation {
        relation: name.clone(),
        diagonals: BTreeSet::new(),
        projections: BTreeMap::new(),
        results: (0..dom.len() + 1).map(|i| (i, FlatTerm(i))).collect(),
    };

    let old_query = Query::Relation {
        relation: name.clone(),
        diagonals: BTreeSet::new(),
        projections: (0..dom.len()).map(|i| (i, FlatTerm(i))).collect(),
        results: once((dom.len(), old_result)).collect(),
    };
    let query_ages = [(&dirty_query, TupleAge::Dirty), (&old_query, TupleAge::All)];

    let action = Action::Equate {
        sort: cod.clone(),
        lhs: new_result,
        rhs: old_result,
    };

    write_query_loop_headers(out, signature, query_ages.iter().copied())?;
    write_action(out, signature, &action)?;
    write_query_loop_footers(out, query_ages.len())?;
    Ok(())
}

fn write_add_new_elements(out: &mut impl Write, sort: &str) -> io::Result<()> {
    write!(out, "self.{}_dirty.clear();\n", sort.to_case(Snake))?;
    write!(
        out,
        "for new_id in self.{}_equalities.len() .. self.{}_equalities.len() + {}_new_el_num {{\n",
        sort.to_case(Snake),
        sort.to_case(Snake),
        sort.to_case(Snake)
    )?;
    write!(out, "let tm = {}(new_id as u32);\n", sort)?;
    write!(
        out,
        "if tm == self.{}_equalities.root(tm) {{\n",
        sort.to_case(Snake)
    )?;

    write!(out, "self.{}_dirty.insert(tm);\n", sort.to_case(Snake),)?;
    write!(out, "self.{}_all.insert(tm);\n", sort.to_case(Snake),)?;
    write!(out, "}}\n")?;
    write!(out, "}}\n")?;
    write!(out, "{}_new_el_num = 0;\n", sort.to_case(Snake))?;
    Ok(())
}

fn write_add_new_equalities(
    out: &mut impl Write,
    signature: &Signature,
    sort: &str,
) -> io::Result<()> {
    write!(
        out,
        "let {}_equalities_old_len = self.{}_equalities.len();\n",
        sort.to_case(Snake),
        sort.to_case(Snake)
    )?;
    write!(
        out,
        "self.{}_equalities.increase_size(self.{}_equalities.len() + {}_new_el_num);\n",
        sort.to_case(Snake),
        sort.to_case(Snake),
        sort.to_case(Snake)
    )?;
    write!(
        out,
        "for (lhs, rhs) in {}_new_eqs.drain(..) {{\n",
        sort.to_case(Snake)
    )?;
    write!(
        out,
        "let lhs = self.{}_equalities.root(lhs);\n",
        sort.to_case(Snake)
    )?;
    write!(
        out,
        "let rhs = self.{}_equalities.root(rhs);\n",
        sort.to_case(Snake)
    )?;
    write!(out, "if lhs == rhs {{ continue; }}\n")?;
    write!(
        out,
        "let lhs_is_old = (lhs.0 as usize) < {}_equalities_old_len;\n",
        sort.to_case(Snake)
    )?;
    write!(
        out,
        "let rhs_is_old = (rhs.0 as usize) < {}_equalities_old_len;\n",
        sort.to_case(Snake)
    )?;
    write!(
        out,
        "let old_removed_term = match (lhs_is_old, rhs_is_old) {{\n"
    )?;
    write!(
        out,
        "  (false, false) => {{ self.{}_equalities.union_into(lhs, rhs); None }}\n",
        sort.to_case(Snake)
    )?;
    write!(
        out,
        "  (true, false) => {{ self.{}_equalities.union_into(rhs, lhs); None }}\n",
        sort.to_case(Snake)
    )?;
    write!(
        out,
        "  (false, true) => {{ self.{}_equalities.union_into(lhs, rhs); None }}\n",
        sort.to_case(Snake)
    )?;
    write!(
        out,
        "  (true, true) => {{ self.{}_equalities.union_into(lhs, rhs); Some(lhs) }}\n",
        sort.to_case(Snake)
    )?;
    write!(out, "}};\n")?;
    write!(out, "if let Some(tm) = old_removed_term {{\n")?;
    for (relation, arity) in signature.relations() {
        if let None = arity.iter().find(|s| **s == sort) {
            continue;
        }
        write!(
            out,
            "let {}_contains_tm = |t : &&{}| {{ false \n",
            relation.to_case(Snake),
            relation
        )?;
        for (i, arg_sort) in arity.iter().enumerate() {
            if *arg_sort == sort {
                write!(out, " || t.{} == tm", i)?;
            }
        }
        write!(out, " }};\n")?;

        write!(out, "{}_new.extend(self.", relation.to_case(Snake))?;
        write_relation_field_name(out, relation, TupleAge::All)?;
        write!(
            out,
            ".iter().filter({}_contains_tm));\n",
            relation.to_case(Snake)
        )?;

        write!(
            out,
            "self.{}_all.retain(|t| !{}_contains_tm(&t));",
            relation.to_case(Snake),
            relation.to_case(Snake)
        )?;
        write!(out, "\n")?;
    }
    write!(out, "}}\n")?;
    write!(out, "}}\n")?;
    Ok(())
}

fn write_closure(
    out: &mut impl Write,
    signature: &Signature,
    query_actions: &[QueryAction],
) -> io::Result<()> {
    write!(out, "#[allow(dead_code)]\n")?;
    write!(out, "pub fn close(&mut self) {{\n")?;
    for (relation, _) in signature.relations() {
        write!(
            out,
            "let mut {}_new: Vec<{}> = Vec::new();\n",
            relation.to_case(Snake),
            relation
        )?;
    }
    write!(out, "\n")?;
    for (sort, _) in signature.sorts() {
        write!(
            out,
            "let mut {}_new_el_num: usize = 0;\n",
            sort.to_case(Snake),
        )?;
        write!(
            out,
            "let mut {}_new_eqs: Vec<({}, {})> = Vec::new();\n",
            sort.to_case(Snake),
            sort,
            sort
        )?;
    }
    write!(out, "\n")?;

    write!(out, "while self.is_dirty() {{\n")?;
    for query_action in query_actions {
        write_query_action_step(out, signature, query_action)?;
        write!(out, "\n")?;
    }

    for function in signature.functions().values() {
        write_functionality_step(out, signature, function)?;
        write!(out, "\n")?;
    }

    for (sort, _) in signature.sorts() {
        write_add_new_equalities(out, signature, sort)?;
        write_add_new_elements(out, sort)?;
        write!(out, "\n")?;
    }

    for (relation, arity) in signature.relations() {
        write!(out, "self.{}_dirty.clear();\n", relation.to_case(Snake))?;
        write!(
            out,
            "for t in {}_new.drain(..) {{\n",
            relation.to_case(Snake)
        )?;
        write!(out, "let u = {}(", relation)?;
        for (i, sort) in arity.iter().enumerate() {
            write!(
                out,
                "self.{}_equalities.root(t.{}), ",
                sort.to_case(Snake),
                i
            )?;
        }
        write!(out, ");\n")?;
        write!(
            out,
            "if self.{}_all.insert(u) {{\n",
            relation.to_case(Snake)
        )?;
        write!(out, "self.{}_dirty.insert(u); \n", relation.to_case(Snake))?;
        write!(out, "}}\n")?;
        write!(out, "}}\n")?;
        write!(out, "\n")?;
    }

    write!(out, "}}\n")?;

    write!(out, "}}\n")?;
    Ok(())
}

fn write_new_impl(out: &mut impl Write, signature: &Signature) -> io::Result<()> {
    write!(out, "#[allow(dead_code)]\n")?;
    write!(out, "pub fn new() -> Self {{\n")?;
    write!(out, "Self {{\n")?;
    for sort in signature.sorts().keys() {
        write!(
            out,
            "{}_equalities: Unification::new(),\n",
            sort.to_case(Snake)
        )?;
        write!(out, "{}_dirty: HashSet::new(),\n", sort.to_case(Snake))?;
        write!(out, "{}_all: HashSet::new(),\n", sort.to_case(Snake))?;
    }
    for (relation, _) in signature.relations() {
        write!(out, "{}_all: BTreeSet::new(),\n", relation.to_case(Snake))?;
        write!(out, "{}_dirty: BTreeSet::new(),\n", relation.to_case(Snake))?;
    }
    write!(out, "}}\n")?;
    write!(out, "}}\n")?;
    Ok(())
}

fn write_theory_struct(out: &mut impl Write, name: &str, signature: &Signature) -> io::Result<()> {
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
    for sort in signature.sorts().keys() {
        write_pub_new_element(out, sort)?;
        write_pub_iter_sort(out, sort)?;
        write!(out, "\n")?;
    }
    for (rel, arity) in signature.relations() {
        let query_index_map = index_selection.get(rel).unwrap();
        for query in query_index_map.keys() {
            write_iter_impl(out, rel, &arity, query, TupleAge::All)?;
            write_iter_impl(out, rel, &arity, query, TupleAge::Dirty)?;
        }
        let unrestrained_query = QuerySpec::new();
        if let None = query_index_map.get(&unrestrained_query) {
            write_iter_impl(out, rel, &arity, &unrestrained_query, TupleAge::All)?;
            write_iter_impl(out, rel, &arity, &unrestrained_query, TupleAge::Dirty)?;
        };
        write_pub_iter(out, rel)?;
        write_pub_insert_relation(out, rel, &arity)?;
        write!(out, "\n")?;
    }

    write_new_impl(out, signature)?;
    write!(out, "\n")?;

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
        write_sort_from_u32_impl(out, sort)?;
        write_sort_into_u32_impl(out, sort)?;
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

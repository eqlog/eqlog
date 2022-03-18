use crate::direct_ast::*;
use crate::index_selection::*;
use crate::query_action::*;
use crate::signature::Signature;
use convert_case::{Case, Casing};
use indoc::writedoc;
use itertools::Itertools;
use std::collections::BTreeSet;
use std::fmt::{self, Display, Formatter};
use std::io::{self, Write};

use Case::Snake;

fn write_imports(out: &mut impl Write) -> io::Result<()> {
    writedoc! { out, "
        use std::collections::BTreeSet;
        use std::collections::HashSet;
        use eqlog_util::Unification;
    "}
}

// #[derive(Copy, Clone, PartialEq, Eq, Debug, Hash, PartialOrd, Ord)]
// pub struct SortName(pub u32);
fn write_sort_type(out: &mut impl Write, sort: &str) -> io::Result<()> {
    writedoc! {out, "
        #[allow(dead_code)]
        #[derive(Copy, Clone, PartialEq, Eq, Debug, Hash, PartialOrd, Ord)]
        pub struct {sort}(pub u32);
    "}
}

fn write_sort_from_u32_impl(out: &mut impl Write, sort: &str) -> io::Result<()> {
    writedoc! {out, "
        impl Into<u32> for {sort} {{ fn into(self) -> u32 {{ self.0 }} }}
    "}
}

fn write_sort_into_u32_impl(out: &mut impl Write, sort: &str) -> io::Result<()> {
    writedoc! {out, "
        impl From<u32> for {sort} {{ fn from(x: u32) -> Self {{ {sort}(x) }} }}
    "}
}

struct IntersperseDisplay<T, I, F>(T, I, F)
where
    T: Display,
    I: IntoIterator + Clone,
    F: for<'a> Fn(&mut Formatter<'a>, I::Item) -> fmt::Result;

impl<T, I, F> Display for IntersperseDisplay<T, I, F>
where
    T: Display,
    I: IntoIterator + Clone,
    F: for<'a> Fn(&mut Formatter<'a>, I::Item) -> fmt::Result,
{
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        let sep = &self.0;
        let mut it = self.1.clone().into_iter();
        let fun = &self.2;
        if let Some(first) = it.next() {
            fun(f, first)?;
            for item in it {
                write!(f, "{sep}")?;
                fun(f, item)?;
            }
        }
        Ok(())
    }
}

// #[derive(Copy, Clone, PartialEq, Eq, Debug, Hash, PartialOrd, Ord)]
// pub struct RelationName(pub SortOne, pub SortTwo, ..., pub SortN);
fn write_tuple_type(out: &mut impl Write, relation: &str, arity: &[&str]) -> io::Result<()> {
    let args = arity
        .iter()
        .copied()
        .format_with(", ", |sort, f| f(&format_args!("pub {sort}")));
    writedoc! {out, "
        #[allow(dead_code)]
        #[derive(Copy, Clone, PartialEq, Eq, Debug, Hash, PartialOrd, Ord)]
        pub struct {relation}({args});
    "}
}

fn write_sort_fields(out: &mut impl Write, sort: &str) -> io::Result<()> {
    let sort_snake = sort.to_case(Snake);
    writedoc! {out, "
        {sort_snake}_equalities: Unification<{sort}>,
        {sort_snake}_all: HashSet<{sort}>,
        {sort_snake}_dirty: HashSet<{sort}>,
    "}
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

fn write_relation_field(out: &mut impl Write, relation: &str, age: TupleAge) -> io::Result<()> {
    let relation_snake = relation.to_case(Snake);
    writedoc! {out, "
        {relation_snake}_{age} : BTreeSet<{relation}>,
    "}
}

fn write_is_dirty_impl(out: &mut impl Write, signature: &Signature) -> io::Result<()> {
    let rels_dirty = signature
        .relations()
        .format_with(" || ", |(relation, _), f| {
            let relation_snake = relation.to_case(Snake);
            f(&format_args!("!self.{relation_snake}_dirty.is_empty()"))
        });

    let sorts_dirty = signature.sorts().keys().format_with(" || ", |sort, f| {
        let sort_snake = sort.to_case(Snake);
        f(&format_args!("!self.{sort_snake}_dirty.is_empty()"))
    });

    writedoc! {out, "
        fn is_dirty(&self) -> bool {{
            {rels_dirty} || {sorts_dirty}
        }}
    "}
}

struct IterName<'a>(&'a str, TupleAge, &'a QuerySpec);

impl<'a> Display for IterName<'a> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        let relation_snake = self.0.to_case(Snake);
        let age = self.1;
        let query_spec = self.2;
        write!(f, "iter_{relation_snake}_{age}")?;
        for p in query_spec.projections.iter() {
            write!(f, "_{p}")?;
        }
        for diag in query_spec.diagonals.iter() {
            write!(f, "_diagonal")?;
            for d in diag.iter() {
                write!(f, "_{d}")?;
            }
        }
        Ok(())
    }
}

fn write_iter_impl(
    out: &mut impl Write,
    relation: &str,
    arity: &[&str],
    query: &QuerySpec,
    age: TupleAge,
) -> io::Result<()> {
    let relation_snake = relation.to_case(Snake);
    let iter_name = IterName(relation, age, query);

    // (arg3: Mor, arg5: Obj, ...)
    let args = query.projections.iter().copied().format_with(", ", |i, f| {
        let sort = arity[i];
        f(&format_args!("arg{i}: {sort}"))
    });

    // && _t.3 == arg3 && _t.5 == arg5 ...
    let projs_match = query
        .projections
        .iter()
        .copied()
        .format_with("", |i, f| f(&format_args!(" && _t.{i} == arg{i}")));

    // let diag0_matches = _t.1 == _t.2 && _t.2 == _t.4 && ...;
    // let diag1_matches = _t.3 == _t.8;
    // ...
    let diags_match_decls = query
        .diagonals
        .iter()
        .enumerate()
        .format_with("\n", |(d, diag), f| {
            let clauses = diag
                .iter()
                .zip(diag.iter().skip(1))
                .format_with(" && ", |(prev, next), f| {
                    f(&format_args!("_t.{prev} == _t.{next}"))
                });
            f(&format_args!("let diag{d}_matches = {clauses};"))
        });

    // && diag0_matches && diag_1_matches ...
    let diags_match =
        (0..query.diagonals.len()).format_with("", |d, f| f(&format_args!(" && diag{d}_matches")));

    writedoc! {out, "
        #[allow(dead_code)]
        fn {iter_name}(&self, {args}) -> impl '_ + Iterator<Item={relation}> {{
            self.{relation_snake}_{age}.iter().filter(move |_t| {{
                let proj_matches = true {projs_match};
                {diags_match_decls}
                proj_matches {diags_match}
            }}).copied()
        }}
    "}
}

fn write_pub_iter(out: &mut impl Write, relation: &str) -> io::Result<()> {
    let rel_snake = relation.to_case(Snake);
    writedoc! {out, "
        #[allow(dead_code)]
        pub fn iter_{rel_snake}(&self) -> impl '_ + Iterator<Item={relation}> {{
            self.iter_{rel_snake}_all()
        }}
    "}
}

fn write_pub_insert_relation(
    out: &mut impl Write,
    relation: &str,
    arity: &[&str],
) -> io::Result<()> {
    let relation_snake = relation.to_case(Snake);
    let assign_roots = arity.iter().enumerate().format_with("\n", |(i, sort), f| {
        let sort_snake = sort.to_case(Snake);
        f(&format_args!(
            "  t.{i} = self.{sort_snake}_equalities.root(t.{i});"
        ))
    });
    writedoc! {out, "
        #[allow(dead_code)]
        pub fn insert_{relation_snake}(&mut self, mut t: {relation}) {{
            self.{relation_snake}_all.insert(t);
            {assign_roots}
            self.{relation_snake}_dirty.insert(t);
        }}
    "}
}

fn write_pub_new_element(out: &mut impl Write, sort: &str) -> io::Result<()> {
    let sort_snake = sort.to_case(Snake);
    writedoc! {out, "
        #[allow(dead_code)]
        pub fn new_{sort_snake}(&mut self) -> {sort} {{
            let size = self.{sort_snake}_equalities.len();
            self.{sort_snake}_equalities.increase_size(size + 1);
            let el = {sort}::from(size as u32);
            self.{sort_snake}_dirty.insert(el);
            self.{sort_snake}_all.insert(el);
            el
        }}
    "}
}

fn write_pub_iter_sort(out: &mut impl Write, sort: &str) -> io::Result<()> {
    let sort_snake = sort.to_case(Snake);
    writedoc! {out, "
        #[allow(dead_code)]
        pub fn iter_{sort_snake}(&mut self) -> impl '_ + Iterator<Item={sort}> {{
            self.{sort_snake}_all.iter().copied()
        }}
    "}
}

fn write_close_data_struct(out: &mut impl Write, signature: &Signature) -> io::Result<()> {
    let new_tuples = signature.relations().format_with("\n", |(relation, _), f| {
        let relation_snake = relation.to_case(Snake);
        f(&format_args!("  {relation_snake}_new: Vec<{relation}>,"))
    });
    let new_els = signature.sorts().keys().format_with("\n", |sort, f| {
        let sort_snake = sort.to_case(Snake);
        f(&format_args!("  {sort_snake}_new_el_num: usize,"))
    });
    let new_eqs = signature.sorts().keys().format_with("\n", |sort, f| {
        let sort_snake = sort.to_case(Snake);
        f(&format_args!(
            "  {sort_snake}_new_eqs: Vec<({sort}, {sort})>,"
        ))
    });
    writedoc! {out, "
        struct CloseData {{
            {new_tuples}
            {new_els}
            {new_eqs}
        }}
    "}
}

fn write_close_data_impl(out: &mut impl Write, signature: &Signature) -> io::Result<()> {
    let new_tuples = signature.relations().format_with("", |(relation, _), f| {
        let relation_snake = relation.to_case(Snake);
        f(&format_args!("  {relation_snake}_new: Vec::new(),"))
    });
    let new_els = signature.sorts().keys().format_with("\n", |sort, f| {
        let sort_snake = sort.to_case(Snake);
        f(&format_args!("  {sort_snake}_new_el_num: 0,"))
    });
    let new_eqs = signature.sorts().keys().format_with("\n", |sort, f| {
        let sort_snake = sort.to_case(Snake);
        f(&format_args!("  {sort_snake}_new_eqs: Vec::new(),"))
    });
    writedoc! {out, "
        impl CloseData {{
            fn new() -> CloseData {{
                CloseData{{ {new_tuples} {new_els} {new_eqs} }}
            }}
        }}
    "}
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
                let iter_name = IterName(relation, age, &query_spec);
                write!(out, "{iter_name}")?;
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
            let iter_name = IterName(function, TupleAge::All, &query_spec);
            write!(out, "{iter_name}")?;
            write!(out, "(")?;
            for arg in args {
                write!(out, "tm{}, ", arg.0)?;
            }
            write!(out, ").next() {{\n")?;

            write!(out, "Some(result) => result.{},\n", dom.len())?;

            write!(out, "None => {{\n")?;

            write!(
                out,
                "let new_el = {}((self.{}_equalities.len() + data.{}_new_el_num) as u32);\n",
                cod,
                cod.to_case(Snake),
                cod.to_case(Snake)
            )?;

            write!(out, "data.{}_new_el_num += 1;\n", cod.to_case(Snake))?;

            write!(
                out,
                "data.{}_new.push({}(",
                function.to_case(Snake),
                function
            )?;
            for tm in args.iter() {
                write!(out, "tm{}, ", tm.0)?;
            }
            write!(out, "new_el));\n")?;

            write!(out, "new_el\n")?;

            write!(out, "}},\n")?;

            write!(out, "}};\n")?;
        }
        AddTuple { relation, args } => {
            write!(
                out,
                "data.{}_new.push({}(",
                relation.to_case(Snake),
                relation
            )?;
            for tm in args {
                write!(out, "tm{}, ", tm.0)?;
            }
            write!(out, "));\n")?;
        }
        Equate { sort, lhs, rhs } => {
            write!(
                out,
                "data.{}_new_eqs.push((tm{}, tm{}));\n",
                sort.to_case(Snake),
                lhs.0,
                rhs.0
            )?;
        }
    }
    Ok(())
}

fn write_process_sort_close_data_fn(
    out: &mut impl Write,
    signature: &Signature,
    sort: &str,
) -> io::Result<()> {
    let sort_snake = sort.to_case(Snake);

    writedoc! {out, "
        fn process_{sort_snake}_close_data(&mut self, data: &mut CloseData) {{
            let equalities_old_len = self.{sort_snake}_equalities.len();
            for (lhs, rhs) in data.{sort_snake}_new_eqs.drain(..) {{
                let lhs = self.{sort_snake}_equalities.root(lhs);
                let rhs = self.{sort_snake}_equalities.root(rhs);
                if lhs == rhs {{
                    continue;
                }}
                let lhs_is_old = (lhs.0 as usize) < equalities_old_len;
                let rhs_is_old = (rhs.0 as usize) < equalities_old_len;
                match (lhs_is_old, rhs_is_old) {{
                    (false, false) => {{
                        self.{sort_snake}_equalities.union_into(lhs, rhs);
                    }}
                    (true, false) => {{
                        self.{sort_snake}_equalities.union_into(rhs, lhs);
                    }}
                    (false, true) => {{
                        self.{sort_snake}_equalities.union_into(lhs, rhs);
                    }}
                    (true, true) => {{
                        self.{sort_snake}_equalities.union_into(lhs, rhs);
    "}?;
    for (relation, arity) in signature.relations() {
        if let None = arity.iter().find(|s| **s == sort) {
            continue;
        }
        let relation_snake = relation.to_case(Snake);
        let clauses = arity
            .iter()
            .enumerate()
            .filter(|(_, s)| **s == sort)
            .format_with(" && ", |(i, _), f| f(&format_args!("t.{i} == lhs")));
        writedoc! {out, "
            let {relation_snake}_contains_lhs = |t: &&{relation}| {clauses};
            data.{relation_snake}_new.extend(
                self.{relation_snake}_all.iter().filter({relation_snake}_contains_lhs)
            );
            self.{relation_snake}_all.retain(|t| !{relation_snake}_contains_lhs(&t));
        "}?;
    }

    writedoc! {out, "
                    }}
                }}
            }}
            self.{sort_snake}_dirty.clear();
            for new_id in equalities_old_len..self.{sort_snake}_equalities.len() {{
                let tm = {sort}(new_id as u32);
                if tm == self.{sort_snake}_equalities.root(tm) {{
                    self.{sort_snake}_dirty.insert(tm);
                    self.{sort_snake}_all.insert(tm);
                }}
            }}
            data.{sort_snake}_new_el_num = 0;
        }}
    "}
}

fn write_axiom_step_fn(
    out: &mut impl Write,
    signature: &Signature,
    query_action: &QueryAction,
    axiom_index: usize,
) -> io::Result<()> {
    let queries = &query_action.queries;
    let actions = &query_action.actions;

    writedoc! {out, "
        fn axiom_{axiom_index}_step(&self, data: &mut CloseData) {{
    "}?;

    for new_index in 0..queries.len() {
        write!(out, "// Query {new_index} is for dirty data.\n")?;
        let query_ages = queries.iter().enumerate().map(|(i, query)| {
            let age = if i == new_index {
                TupleAge::Dirty
            } else {
                TupleAge::All
            };
            (query, age)
        });
        write_query_loop_headers(out, signature, query_ages)?;
        for action in actions.iter() {
            write_action(out, signature, action)?;
        }
        write_query_loop_footers(out, queries.len())?;
    }

    writedoc! {out, "
        }}
    "}
}

fn write_functionality_step_fn(out: &mut impl Write, function: &Function) -> io::Result<()> {
    let Function { name, dom, cod } = function;
    let cod_snake = cod.to_case(Snake);
    let name_snake = name.to_case(Snake);

    let dirty_query = QuerySpec::new();
    let dirty_iter = IterName(name, TupleAge::Dirty, &dirty_query);

    let all_query = QuerySpec {
        projections: (0..dom.len()).collect(),
        diagonals: BTreeSet::new(),
    };
    let all_iter = IterName(name, TupleAge::All, &all_query);

    let dirty_result = dom.len();
    let all_result = dom.len() + 1;

    let dirty_vars = (0..dom.len() + 1).format_with(", ", |i, f| f(&format_args!("tm{i}")));
    let all_vars = (0..dom.len() + 1).format_with(", ", |i, f| {
        if i < dom.len() {
            f(&format_args!("_"))
        } else {
            f(&format_args!("tm{all_result}"))
        }
    });
    let old_args = (0..dom.len()).format_with(", ", |i, f| f(&format_args!("tm{i}")));

    writedoc! {out, "
        fn functionality_{name_snake}_step(&mut self, data: &mut CloseData) {{
            for {name}({dirty_vars}) in self.{dirty_iter}() {{
                for {name}({all_vars}) in self.{all_iter}({old_args}) {{
                    data.{cod_snake}_new_eqs.push((tm{dirty_result}, tm{all_result}));
                }}
            }}
        }}
    "}
}

fn write_closure(
    out: &mut impl Write,
    signature: &Signature,
    query_actions: &[QueryAction],
) -> io::Result<()> {
    write!(out, "#[allow(dead_code)]\n")?;
    write!(out, "pub fn close(&mut self) {{\n")?;
    write!(out, "let mut data = CloseData::new();\n")?;
    write!(out, "\n")?;

    write!(out, "while self.is_dirty() {{\n")?;
    for i in 0..query_actions.len() {
        write!(out, "self.axiom_{i}_step(&mut data);\n")?;
    }

    for function in signature.functions().keys() {
        let function_snake = function.to_case(Snake);
        write!(
            out,
            "self.functionality_{function_snake}_step(&mut data);\n"
        )?;
    }

    for (sort, _) in signature.sorts() {
        let sort_snake = sort.to_case(Snake);
        write!(out, "self.process_{sort_snake}_close_data(&mut data);\n")?;
    }

    for (relation, arity) in signature.relations() {
        write!(out, "self.{}_dirty.clear();\n", relation.to_case(Snake))?;
        write!(
            out,
            "for t in data.{}_new.drain(..) {{\n",
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
        write_process_sort_close_data_fn(out, signature, sort)?;
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

    for (i, query_action) in query_actions.iter().enumerate() {
        write_axiom_step_fn(out, signature, query_action, i)?;
    }
    for function in signature.functions().values() {
        write_functionality_step_fn(out, function)?;
    }

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
    for sort in signature.sorts().keys() {
        write_sort_type(out, sort)?;
        write_sort_from_u32_impl(out, sort)?;
        write_sort_into_u32_impl(out, sort)?;
    }

    write!(out, "\n")?;
    for (rel, arity) in signature.relations() {
        write_tuple_type(out, rel, &arity)?;
    }
    write!(out, "\n")?;

    write_close_data_struct(out, signature)?;
    write_close_data_impl(out, signature)?;
    write!(out, "\n")?;

    write_theory_struct(out, name, signature)?;
    write_theory_impl(out, name, signature, query_actions, index_selection)?;

    Ok(())
}

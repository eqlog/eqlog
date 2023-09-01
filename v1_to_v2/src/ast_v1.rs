use crate::source_display::Location;
use askama::Template;
use convert_case::{Case::Snake, Casing};
use itertools::Itertools;
use std::fmt::{self, Debug};

#[derive(Clone, PartialEq, Eq, Hash, Debug, Template)]
#[template(source = r#"type {{ name }};"#, ext = "txt")]
pub struct Sort {
    pub name: String,
    pub location: Option<Location>,
}

#[derive(Clone, PartialEq, Eq, Hash, Debug, Template)]
#[template(
    source = r#"pred {{ name.to_case(Snake) }}(
{%- for sort in arity -%}
    {{ sort }}
    {%- if !loop.last -%}, {% endif -%}
{%- endfor -%}
);"#,
    ext = "txt"
)]
pub struct Predicate {
    pub name: String,
    pub arity: Vec<String>,
    pub location: Option<Location>,
}

#[derive(Clone, PartialEq, Eq, Hash, Debug, Template)]
#[template(
    source = r#"func {{ name.to_case(Snake) }}(
{%- for sort in dom -%}
    {{ sort }}
    {%- if !loop.last -%}, {% endif -%}
{%- endfor -%}
) -> {{ cod }};"#,
    ext = "txt"
)]
pub struct Function {
    pub name: String,
    pub dom: Vec<String>,
    pub cod: String,
    pub location: Option<Location>,
}

#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub struct Term(pub usize);
impl From<usize> for Term {
    fn from(n: usize) -> Term {
        Term(n)
    }
}
impl Into<usize> for Term {
    fn into(self) -> usize {
        self.0
    }
}

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub enum TermData {
    Variable(String),
    Wildcard,
    Application(String, Vec<Term>),
}

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub struct TermUniverse(Vec<(TermData, Option<Location>)>);

impl TermUniverse {
    pub fn new() -> TermUniverse {
        TermUniverse(Vec::new())
    }
    pub fn new_term(&mut self, data: TermData, location: Option<Location>) -> Term {
        let tm = Term(self.0.len());
        self.0.push((data, location));
        tm
    }
    pub fn data(&self, tm: Term) -> &TermData {
        &self.0[tm.0].0
    }
    pub fn data_ref(&self, tm: &Term) -> &TermData {
        self.data(*tm)
    }
}

struct SubtermIterator<'a> {
    universe: &'a TermUniverse,
    stack: Vec<(Term, usize)>,
}

impl<'a> Iterator for SubtermIterator<'a> {
    type Item = Term;

    fn next(&mut self) -> Option<Self::Item> {
        let (tm, next_child) = match self.stack.pop() {
            Some(top) => top,
            None => return None,
        };

        use TermData::*;
        let mut child = match self.universe.data(tm) {
            Variable(_) | Wildcard => return Some(tm),
            Application(_, args) if args.len() == next_child => return Some(tm),
            Application(_, args) => {
                debug_assert!(next_child < args.len());
                args[next_child]
            }
        };

        self.stack.push((tm, next_child + 1));
        while let Application(_, args) = self.universe.data(child) {
            match args.first() {
                None => break,
                Some(arg) => {
                    self.stack.push((child, 1));
                    child = *arg;
                }
            }
        }
        Some(child)
    }
}

#[derive(Clone, PartialEq, Eq, Hash, Debug, Template)]
#[template(
    source = r#"{%- match (self.universe.data_ref(self.term)) -%}
  {%- when TermData::Variable with (name) -%}
    {{ name }}
  {%- when TermData::Wildcard -%}
    _
  {%- when TermData::Application with (func, args) -%}
    {{ func.to_case(Snake) }}(
    {%- for arg in args -%}
      {{ TermWithUniverse::new(arg, self.universe) }}
      {%- if !loop.last -%}, {% endif -%}
    {%- endfor -%}
    )
{%- endmatch -%}"#,
    ext = "txt"
)]
pub struct TermWithUniverse<'a> {
    term: Term,
    universe: &'a TermUniverse,
}

impl<'a> TermWithUniverse<'a> {
    fn new(term: &&Term, universe: &'a TermUniverse) -> Self {
        TermWithUniverse {
            term: **term,
            universe,
        }
    }
}

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub enum AtomData {
    Equal(Term, Term),
    Defined(Term, Option<String>),
    Predicate(String, Vec<Term>),
}

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub struct Atom {
    pub data: AtomData,
    pub location: Option<Location>,
}

#[derive(Clone, PartialEq, Eq, Hash, Debug, Template)]
#[template(
    source = r#"{%- match self.atom.data -%}
  {%- when AtomData::Equal with (lhs, rhs) -%}
    {{ TermWithUniverse::new(lhs, self.universe) }} = {{ TermWithUniverse::new(rhs, self.universe) }}
  {%- when AtomData::Defined with (tm, opt_sort) -%}
    {{ TermWithUniverse::new(tm, self.universe) }}
    {%- match opt_sort -%}
      {%- when Some with (sort) -%}
        : {{sort}}
      {%- when None -%}
        !
    {%- endmatch -%}
  {%- when AtomData::Predicate with (pred, args) -%}
    {{ pred.to_case(Snake) }}(
    {%- for arg in args -%}
      {{ TermWithUniverse::new(arg, self.universe) }}
      {%- if !loop.last -%}, {% endif -%}
    {%- endfor -%}
    )
{%- endmatch -%}"#,
    ext = "txt"
)]
pub struct AtomWithUniverse<'a> {
    atom: &'a Atom,
    universe: &'a TermUniverse,
}

impl<'a> AtomWithUniverse<'a> {
    fn new(atom: &'a Atom, universe: &'a TermUniverse) -> Self {
        AtomWithUniverse { atom, universe }
    }
}

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub enum SequentData {
    Implication {
        premise: Vec<Atom>,
        conclusion: Vec<Atom>,
    },
    Reduction {
        premise: Vec<Atom>,
        from: Term,
        to: Term,
    },
    Bireduction {
        premise: Vec<Atom>,
        lhs: Term,
        rhs: Term,
    },
}

#[derive(Clone, PartialEq, Eq, Hash)]
pub struct Sequent {
    pub universe: TermUniverse,
    pub data: SequentData,
}

#[derive(Clone, PartialEq, Eq, Hash, Debug, Template)]
#[template(
    source = r#"rule {
{%- match self.sequent.data -%}
{%- when SequentData::Implication with {premise, conclusion} -%}
{%- for atom in premise %}
    if {{ AtomWithUniverse::new(atom, self.sequent.universe) }};
{%- endfor -%}
{%- for atom in conclusion %}
    then {{ AtomWithUniverse::new(atom, self.sequent.universe) }};
{%- endfor -%}
{%- when SequentData::Reduction with {premise, from, to} -%}
{%- for atom in premise %}
    if {{ AtomWithUniverse::new(atom, self.sequent.universe) }};
{%- endfor -%}
{%- match self.sequent.universe.data_ref(from) -%}
{%- when TermData::Application with (func, args) -%}
{%- for arg in args %}
    if t_{{loop.index0}} = {{ TermWithUniverse::new(arg, self.sequent.universe) }};
{%- endfor -%}
{%- when TermData::Variable with (name) -%}
{%- when TermData::Wildcard -%}
{%- endmatch %}
    if to = {{ TermWithUniverse::new(to, self.sequent.universe) }};
{%- match self.sequent.universe.data_ref(from) -%}
{%- when TermData::Application with (func, args) %}
    then {{ func }}(
{%- for arg in args -%}
t_{{loop.index0}}
{%- if !loop.last -%}, {% endif -%}
{%- endfor -%}
) = to;
{%- when TermData::Variable with (name) %}
    then {{ name }} = to;
{%- when TermData::Wildcard %}
    then _ = to;
{%- endmatch -%}
{%- when SequentData::Bireduction with {premise, lhs, rhs} -%}
BIREDUCTIONS ARE NOT SUPPORTED
{%- endmatch %}
}"#,
    ext = "txt"
)]
pub struct Axiom {
    pub sequent: Sequent,
    pub location: Option<Location>,
}

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub struct QueryArgument {
    pub variable: Term,
    pub sort: Option<String>,
    pub location: Option<Location>,
}

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub enum QueryResult {
    NoResult,
    SingleResult(Term),
    TupleResult(Vec<Term>),
}

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub struct UserQuery {
    pub universe: TermUniverse,
    pub name: String,
    pub arguments: Vec<QueryArgument>,
    pub result: QueryResult,
    pub where_formula: Option<Vec<Atom>>,
    pub location: Option<Location>,
}

#[derive(Clone, PartialEq, Eq, Hash, Debug, Template)]
#[template(
    source = r#"{%- match self -%}
  {%- when Decl::Sort with (sort) -%}
    {{ sort }}
  {%- when Decl::Func with (func) -%}
    {{ func }}
  {%- when Decl::Pred with (pred) -%}
    {{ pred }}
  {%- when Decl::Axiom with (axiom) -%}
    {{ axiom }}
  {%- when Decl::Query with (query) -%}
    NOT SUPPORTED
{%- endmatch -%}"#,
    ext = "txt"
)]
pub enum Decl {
    Sort(Sort),
    Func(Function),
    Pred(Predicate),
    Axiom(Axiom),
    Query(UserQuery),
}

impl Decl {
    pub fn location(&self) -> Option<Location> {
        match self {
            Decl::Sort(sort) => sort.location,
            Decl::Func(func) => func.location,
            Decl::Pred(pred) => pred.location,
            Decl::Axiom(axiom) => axiom.location,
            Decl::Query(query) => query.location,
        }
    }
}

// Debug printing of AST. Each AST node type N that is relative to a TermUniverse gets a struct
// NDebug that bundles the node with the TermUniverse it belongs to, and this struct implements
// Debug such that it will recursively print the whole tree structure of the node .

#[derive(Copy, Clone)]
struct TermDebug<'a> {
    term: Term,
    universe: &'a TermUniverse,
}

impl<'a> Debug for TermDebug<'a> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let TermDebug { term, universe } = *self;
        use TermData::*;
        match universe.data(term) {
            Variable(name) => f.write_str(name),
            Wildcard => write!(f, "_{}", term.0),
            Application(func, args) => {
                let args_displ = args.iter().copied().format_with(", ", |arg, f| {
                    f(&format_args!(
                        "{:?}",
                        TermDebug {
                            term: arg,
                            universe
                        }
                    ))
                });
                write!(f, "{func}({args_displ})")
            }
        }
    }
}

impl Term {
    #[allow(dead_code)]
    pub fn debug<'a>(self, universe: &'a TermUniverse) -> impl 'a + Debug + Copy + Clone {
        TermDebug {
            term: self,
            universe,
        }
    }
}

#[derive(Clone)]
pub struct AtomDebug<'a> {
    atom: &'a Atom,
    universe: &'a TermUniverse,
}

impl<'a> Debug for AtomDebug<'a> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let AtomDebug { atom, universe } = self;
        use AtomData::*;
        match &atom.data {
            Equal(lhs, rhs) => {
                let lhs = lhs.debug(universe);
                let rhs = rhs.debug(universe);
                write!(f, "{lhs:?} = {rhs:?}")?;
            }
            Defined(tm, sort) => {
                let tm = tm.debug(universe);
                match sort {
                    Some(sort) => write!(f, "{tm:?}: {sort}")?,
                    None => write!(f, "{tm:?}!")?,
                }
            }
            Predicate(pred, args) => {
                let args_displ = args.iter().copied().format_with(", ", |arg, f| {
                    f(&format_args!(
                        "{:?}",
                        TermDebug {
                            term: arg,
                            universe
                        }
                    ))
                });
                write!(f, "{pred}({args_displ})")?;
            }
        }
        Ok(())
    }
}

impl Atom {
    #[allow(dead_code)]
    pub fn debug<'a>(&'a self, universe: &'a mut TermUniverse) -> AtomDebug<'a> {
        AtomDebug {
            atom: self,
            universe,
        }
    }
}

pub struct FormulaDebug<'a> {
    atoms: &'a [Atom],
    universe: &'a TermUniverse,
}

impl<'a> Debug for FormulaDebug<'a> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let FormulaDebug { atoms, universe } = self;
        let atoms = atoms.into_iter().format_with(" & ", |atom, f| {
            f(&format_args!("{:?}", AtomDebug { atom, universe }))
        });
        write!(f, "{atoms}")?;
        Ok(())
    }
}

pub fn formula_debug<'a>(atoms: &'a [Atom], universe: &'a TermUniverse) -> FormulaDebug<'a> {
    FormulaDebug { atoms, universe }
}

impl Debug for Sequent {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let Sequent { universe, data } = self;
        use SequentData::*;
        match data {
            Implication {
                premise,
                conclusion,
            } => {
                let premise = formula_debug(premise.as_slice(), universe);
                let conclusion = formula_debug(conclusion.as_slice(), universe);
                write!(f, "{premise:?} => {conclusion:?}")?;
            }
            Reduction { premise, from, to } => {
                let premise = formula_debug(premise.as_slice(), universe);
                let from = from.debug(universe);
                let to = to.debug(universe);
                write!(f, "{premise:?} => {from:?} ~> {to:?}")?;
            }
            Bireduction { premise, lhs, rhs } => {
                let premise = formula_debug(premise.as_slice(), universe);
                let lhs = lhs.debug(universe);
                let rhs = rhs.debug(universe);
                write!(f, "{premise:?} => {lhs:?} <~> {rhs:?}")?;
            }
        }
        Ok(())
    }
}

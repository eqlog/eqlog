mod rule;
mod table;
mod types;

pub use rule::*;
pub use table::*;
pub use types::*;

use crate::eqlog_util::*;
use crate::flat_eqlog::*;
use crate::fmt_util::*;
use by_address::ByAddress;
use convert_case::{Case, Casing};
use eqlog_eqlog::*;
use indoc::{formatdoc, writedoc};
use itertools::Itertools;
use std::collections::{BTreeMap, BTreeSet};
use std::fmt::{Display, Formatter, Result};
use std::iter::once;
use std::iter::repeat;

use Case::{Snake, UpperCamel};

fn display_func_snake<'a>(
    func: Func,
    eqlog: &'a Eqlog,
    identifiers: &'a BTreeMap<Ident, String>,
) -> impl 'a + Display {
    let ident = eqlog
        .iter_semantic_func()
        .find_map(|(_sym_scope, ident, func0)| eqlog.are_equal_func(func, func0).then_some(ident))
        .expect("should be surjective");
    format!("{}", identifiers.get(&ident).unwrap()).to_case(Snake)
}

fn display_imports() -> impl Display {
    FmtFn(|f| {
        writedoc! { f, "
            #[allow(unused)]
            use std::collections::{{btree_set, BTreeSet, BTreeMap}};
            #[allow(unused)]
            use std::fmt;
            #[allow(unused)]
            use eqlog_runtime::Unification;
            #[allow(unused)]
            use std::ops::Bound;
            #[allow(unused)]
            use std::ptr::NonNull;
        "}
    })
}

// #[derive(Copy, Clone, PartialEq, Eq, Debug, Hash, PartialOrd, Ord)]
// pub struct SortName(pub u32);
fn display_sort_struct(sort: &str) -> impl Display + '_ {
    FmtFn(move |f| {
        writedoc! {f, "
            #[allow(dead_code)]
            #[derive(Copy, Clone, PartialEq, Eq, Debug, Hash, PartialOrd, Ord)]
            pub struct {sort}(pub u32);
        "}
    })
}

fn display_sort_impl(sort: &str) -> impl Display + '_ {
    FmtFn(move |f| {
        writedoc! {f, "
            impl Into<u32> for {sort} {{ fn into(self) -> u32 {{ self.0 }} }}
            impl From<u32> for {sort} {{ fn from(x: u32) -> Self {{ {sort}(x) }} }}
            impl fmt::Display for {sort} {{
                fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {{
                    write!(f, \"{{:?}}\", self)
                }}
            }}
        "}
    })
}

fn display_ctor<'a>(
    ctor: CtorDeclNode,
    eqlog: &'a Eqlog,
    identifiers: &'a BTreeMap<Ident, String>,
) -> impl 'a + Display {
    FmtFn(move |f: &mut Formatter| -> Result {
        let ctor_ident = eqlog
            .iter_ctor_decl()
            .find_map(|(ctor0, ctor_ident, _)| {
                if eqlog.are_equal_ctor_decl_node(ctor0, ctor) {
                    Some(ctor_ident)
                } else {
                    None
                }
            })
            .unwrap();

        let ctor_name: String = identifiers.get(&ctor_ident).unwrap().to_case(UpperCamel);
        let ss: SymbolScope = eqlog.ctor_symbol_scope(ctor).unwrap();

        let ctor_func = eqlog.semantic_func(ss, ctor_ident).unwrap();
        let domain: Vec<Type> = type_list_vec(
            eqlog.flat_domain(ctor_func).expect("should be total"),
            eqlog,
        );

        let domain = domain
            .into_iter()
            .map(|typ| display_type(typ, eqlog, identifiers))
            .format(", ");

        write!(f, "{}({})", ctor_name, domain)
    })
}

fn display_enum<'a>(
    enum_decl: EnumDeclNode,
    eqlog: &'a Eqlog,
    identifiers: &'a BTreeMap<Ident, String>,
) -> impl 'a + Display {
    FmtFn(move |f: &mut Formatter| -> Result {
        let ctors = eqlog
            .iter_ctor_enum()
            .filter_map(|(ctor, enum_decl0)| {
                if eqlog.are_equal_enum_decl_node(enum_decl, enum_decl0) {
                    Some(ctor)
                } else {
                    None
                }
            })
            .map(|ctor| format!("{},\n", display_ctor(ctor, eqlog, identifiers)))
            .format("");

        let enum_ident = eqlog
            .iter_enum_decl()
            .find_map(|(enum_decl0, enum_ident, _)| {
                if eqlog.are_equal_enum_decl_node(enum_decl, enum_decl0) {
                    Some(enum_ident)
                } else {
                    None
                }
            })
            .unwrap();
        let enum_name = identifiers.get(&enum_ident).unwrap().to_case(UpperCamel);

        writedoc! {f, "
            #[allow(unused)]
            #[derive(Copy, Clone, PartialEq, Eq, Debug, Hash, PartialOrd, Ord)]
            pub enum {enum_name}Case {{
            {ctors}
            }}
        "}
    })
}

fn display_func_args_struct<'a>(
    func: Func,
    eqlog: &'a Eqlog,
    identifiers: &'a BTreeMap<Ident, String>,
) -> impl 'a + Display {
    FmtFn(move |f| {
        let rel = eqlog.func_rel(func).unwrap();
        let func_camel = display_rel(rel, eqlog, identifiers)
            .to_string()
            .to_case(UpperCamel);
        let dom = type_list_vec(eqlog.flat_domain(func).unwrap(), eqlog);
        let args = dom
            .iter()
            .copied()
            .map(|typ| {
                FmtFn(move |f| {
                    let type_camel = display_type(typ, eqlog, identifiers)
                        .to_string()
                        .to_case(UpperCamel);
                    write!(f, "pub {type_camel}")
                })
            })
            .format(", ");
        // The #[allow(unused)] is there for functions that cannot be made defined via the Rust API. At
        // the moment, those are non-constructor functions valued in an enum type.
        writedoc! {f, "
            #[allow(unused)]
            #[derive(Copy, Clone, PartialEq, Eq, Debug, Hash, PartialOrd, Ord)]
            struct {func_camel}Args({args});
        "}
    })
}

fn display_sort_fields(sort: &str) -> impl Display + '_ {
    FmtFn(move |f| {
        let sort_snake = sort.to_case(Snake);
        writedoc! {f, "
            {sort_snake}_equalities: Unification<{sort}>,
            {sort_snake}_old: BTreeSet<u32>,
            {sort_snake}_new: BTreeSet<u32>,
            {sort_snake}_weights: Vec<usize>,
            {sort_snake}_uprooted: Vec<{sort}>,
        "}
    })
}

fn display_is_dirty_fn<'a>(
    eqlog: &'a Eqlog,
    identifiers: &'a BTreeMap<Ident, String>,
) -> impl Display + 'a {
    FmtFn(move |f| {
        let rels_dirty = eqlog
            .iter_rel()
            .map(|rel| {
                FmtFn(move |f| {
                    let rel_snake = display_rel(rel, eqlog, identifiers)
                        .to_string()
                        .to_case(Snake);
                    let has_new_data_fn_name =
                        display_has_new_data_fn_name(rel, eqlog, identifiers);
                    writedoc! {f, " || {has_new_data_fn_name}(self.{rel_snake}_table)"}
                })
            })
            .format("");

        let types_dirty = eqlog
            .iter_type()
            .map(|typ| {
                FmtFn(move |f| {
                    let type_snake = display_type(typ, eqlog, identifiers)
                        .to_string()
                        .to_case(Snake);
                    write!(f, " || !self.{type_snake}_new.is_empty()")
                })
            })
            .format("");

        let uprooted_dirty = eqlog
            .iter_type()
            .map(|typ| {
                FmtFn(move |f| {
                    let type_snake = display_type(typ, eqlog, identifiers)
                        .to_string()
                        .to_case(Snake);
                    write!(f, " || !self.{type_snake}_uprooted.is_empty()")
                })
            })
            .format("");

        writedoc! {f, "
            fn is_dirty(&self) -> bool {{
                self.empty_join_is_dirty {rels_dirty} {types_dirty} {uprooted_dirty}
            }}
        "}
    })
}

fn display_pub_predicate_holds_fn<'a>(
    rel: Rel,
    eqlog: &'a Eqlog,
    identifiers: &'a BTreeMap<Ident, String>,
) -> impl Display + 'a {
    FmtFn(move |f| {
        let relation_snake = display_rel(rel, eqlog, identifiers)
            .to_string()
            .to_case(Snake);
        let arity_types: Vec<Type> = type_list_vec(eqlog.flat_arity(rel).unwrap(), eqlog);
        let arity_camel: Vec<String> = arity_types
            .iter()
            .map(|&typ| {
                display_type(typ, eqlog, identifiers)
                    .to_string()
                    .to_case(UpperCamel)
            })
            .collect();

        let rel_fn_args = arity_camel
            .iter()
            .enumerate()
            .format_with("", |(i, s), f| f(&format_args!(", mut arg{i}: {s}")));

        let canonicalize = arity_camel
            .iter()
            .enumerate()
            .format_with("\n", |(i, s), f| {
                let sort_snake = s.to_case(Snake);
                f(&format_args!("arg{i} = self.root_{sort_snake}(arg{i});"))
            });

        let rel_args_doc =
            (0..arity_types.len()).format_with(", ", |i, f| f(&format_args!("arg{i}")));
        let row_args =
            (0..arity_types.len()).format_with(", ", |i, f| f(&format_args!("arg{i}.0")));

        let contains_fn_name = display_contains_fn_name(rel, eqlog, identifiers);

        writedoc! {f, "
            /// Returns `true` if `{relation_snake}({rel_args_doc})` holds.
            #[allow(dead_code)]
            pub fn {relation_snake}(&self{rel_fn_args}) -> bool {{
                {canonicalize}
                let row = [{row_args}];
                {contains_fn_name}(self.{relation_snake}_table, row)
            }}
        "}
    })
}

fn display_pub_function_eval_fn<'a>(
    func: Func,
    eqlog: &'a Eqlog,
    identifiers: &'a BTreeMap<Ident, String>,
    index_selection: &'a IndexSelection,
) -> impl 'a + Display {
    FmtFn(move |f| {
        let rel = eqlog.func_rel(func).unwrap();

        let relation = display_rel(rel, eqlog, identifiers)
            .to_string()
            .to_case(UpperCamel);
        let relation_snake = relation.to_case(Snake);
        let relation_snake = relation_snake.as_str();

        let flat_dom = type_list_vec(eqlog.flat_domain(func).unwrap(), eqlog);
        let flat_dom_len = flat_dom.len();

        let cod = eqlog.codomain(func).unwrap();
        let cod_camel = display_type(cod, eqlog, identifiers)
            .to_string()
            .to_case(UpperCamel);
        let cod_camel = &cod_camel;

        let params = flat_dom
            .iter()
            .copied()
            .enumerate()
            .map(|(i, typ)| {
                FmtFn(move |f| {
                    let type_camel = display_type(typ, eqlog, identifiers)
                        .to_string()
                        .to_case(UpperCamel);
                    write!(f, "mut arg{i}: {type_camel}, ")
                })
            })
            .format("");

        let result_type = FmtFn(move |f| {
            if eqlog.is_total_func(func) {
                write!(f, "{cod_camel}")
            } else {
                write!(f, "Option<{cod_camel}>")
            }
        });

        let canonicalize = flat_dom
            .iter()
            .copied()
            .enumerate()
            .map(|(i, typ)| {
                FmtFn(move |f| {
                    let type_snake = display_type(typ, eqlog, identifiers)
                        .to_string()
                        .to_case(Snake);
                    write!(f, "arg{i} = self.root_{type_snake}(arg{i});")
                })
            })
            .format("\n");

        let doc_args = (0..flat_dom.len())
            .map(|i| FmtFn(move |f| write!(f, "arg{i}")))
            .format(", ")
            .to_string();

        let eval_fn = display_eval_fn_name(func, eqlog, identifiers);

        let table_eval_args = (0..flat_dom_len)
            .map(|i| FmtFn(move |f| write!(f, "arg{i}.0")))
            .format(", ");
        let result = if eqlog.is_total_func(func) {
            "result.unwrap().into()"
        } else {
            "result.map(|x| x.into())"
        };

        writedoc! {f, "
            /// Evaluates `{relation_snake}({doc_args})`.
            #[allow(dead_code)]
            pub fn {relation_snake}(&self, {params}) -> {result_type} {{
            {canonicalize}
                
            let result: Option<u32> = {eval_fn}(&self.{relation_snake}_table, {table_eval_args}).into();

            {result}
            }}
        "}
    })
}

fn display_pub_iter_fn<'a>(
    rel: Rel,
    eqlog: &'a Eqlog,
    identifiers: &'a BTreeMap<Ident, String>,
    index_selection: &'a IndexSelection,
) -> impl Display + 'a {
    FmtFn(move |f| {
        let is_function = match eqlog.rel_case(rel) {
            RelCase::FuncRel(_) => true,
            RelCase::PredRel(_) => false,
        };
        let relation = display_rel(rel, eqlog, identifiers);
        let rel_snake = display_rel(rel, eqlog, identifiers)
            .to_string()
            .to_case(Snake);
        let rel_snake = rel_snake.as_str();
        let arity_tys: Vec<Type> = type_list_vec(eqlog.flat_arity(rel).unwrap(), eqlog);
        let arity_tys = &arity_tys;
        let arity: Vec<String> = arity_tys
            .iter()
            .map(move |ty| {
                display_type(*ty, eqlog, identifiers)
                    .to_string()
                    .to_case(UpperCamel)
            })
            .collect();
        let arity = arity.as_slice();
        let rel_type = if arity.len() == 1 {
            arity[0].clone()
        } else {
            format!("({})", arity.iter().format(", "))
        };

        let docstring = match (is_function, arity.len()) {
            //(false, 0) => todo!("Shouldn't generate an iter_...() function for truth values."),
            (false, 1) => {
                formatdoc! {"
                    /// Returns an iterator over elements satisfying the `{relation}` predicate.
                "}
            }
            (false, n) => {
                assert!(n != 1);
                formatdoc! {"
                    /// Returns an iterator over tuples of elements satisfying the `{relation}` predicate.
                "}
            }
            (true, 0) => panic!("Functions cannot have empty arity"),
            (true, 1) => {
                formatdoc! {"
                    /// Returns an iterator over `{relation}` constants.
                    /// The iterator may yield more than one element if the model is not closed.
                "}
            }
            (true, n) => {
                assert!(n > 1);
                formatdoc! {"
                    /// Returns an iterator over tuples in the graph of the `{relation}` function.
                    /// The relation yielded by the iterator need not be functional if the model is not closed.
                "}
            }
        };

        let query_spec = QuerySpec::all();
        let indices = index_selection
            .get(&display_rel(rel, eqlog, identifiers).to_string())
            .unwrap()
            .get(&query_spec)
            .unwrap();
        let index_its = indices
            .into_iter()
            .enumerate()
            .map(|(i, index)| {
                FmtFn(move |f| {
                    let getter_fn = display_index_getter_fn_name(index, rel, eqlog, identifiers);
                    let row_unpack_args = index
                        .order
                        .iter()
                        .map(|i| FmtFn(move |f| write!(f, "arg{i}")))
                        .format(",");
                    let row_args = arity_tys
                        .iter()
                        .enumerate()
                        .map(|(i, typ)| {
                            FmtFn(move |f| {
                                let type_camel = display_type(*typ, eqlog, identifiers)
                                    .to_string()
                                    .to_case(UpperCamel);
                                write!(f, "{type_camel}::from(*arg{i})")
                            })
                        })
                        .format(",");

                    let row = FmtFn(move |f| {
                        if arity_tys.len() == 1 {
                            write!(f, "{row_args}")
                        } else {
                            write!(f, "({row_args})")
                        }
                    });
                    writedoc! {f, "
                        let index_it{i} =
                        {getter_fn}(&self.{rel_snake}_table)
                        .iter()
                        .map(|[{row_unpack_args}]| {{
                        {row}
                        }});
                    "}
                })
            })
            .format("\n");

        let index_it_chains = (0..indices.len())
            .map(|i| FmtFn(move |f| write!(f, ".chain(index_it{i})")))
            .format("");

        writedoc! {f, "
            {docstring}
            #[allow(dead_code)]
            pub fn iter_{rel_snake}(&self) -> impl '_ + Iterator<Item={rel_type}> {{
            {index_its}

            [].into_iter(){index_it_chains}
            }}
        "}
    })
}

fn display_pub_insert_relation<'a>(
    rel: Rel,
    eqlog: &'a Eqlog,
    identifiers: &'a BTreeMap<Ident, String>,
    is_function: bool,
) -> impl Display + 'a {
    FmtFn(move |f| {
        let rel_snake = display_rel(rel, eqlog, identifiers)
            .to_string()
            .to_case(Snake);
        let rel_snake = rel_snake.as_str();

        let arity_types = type_list_vec(eqlog.flat_arity(rel).unwrap(), eqlog);
        let arity_camel: Vec<String> = arity_types
            .iter()
            .map(|&typ| {
                display_type(typ, eqlog, identifiers)
                    .to_string()
                    .to_case(UpperCamel)
            })
            .collect();

        let rel_args: Vec<FlatVar> = (0..arity_types.len()).map(FlatVar).collect();

        let rel_fn_args = rel_args
            .iter()
            .copied()
            .zip(arity_camel.iter())
            .map(|(arg, typ_camel)| {
                FmtFn(move |f: &mut Formatter| -> Result {
                    let arg = display_var(arg);
                    write!(f, "mut {arg}: {typ_camel}")
                })
            })
            .format(", ");

        let canonicalize = rel_args
            .iter()
            .copied()
            .zip(arity_types.iter())
            .map(|(arg, typ)| {
                FmtFn(move |f: &mut Formatter| -> Result {
                    let arg = display_var(arg);
                    let type_snake = display_type(*typ, eqlog, identifiers)
                        .to_string()
                        .to_case(Snake);
                    write!(f, "{arg} = self.root_{type_snake}({arg});")
                })
            })
            .format("\n");

        let weight_static_name = display_weight_static_name(rel, eqlog, identifiers).to_string(); // Convert to String
        let update_weights = rel_args
            .iter()
            .copied()
            .zip(arity_types.iter())
            .enumerate()
            .map(move |(i, (arg, typ))| {
                let weight_static_name = weight_static_name.clone(); // Clone the String
                FmtFn(move |f: &mut Formatter| -> Result {
                    let arg = display_var(arg);
                    let type_snake = display_type(*typ, eqlog, identifiers)
                        .to_string()
                        .to_case(Snake);
                    writedoc! {f, "
                        let weight{i} = &mut self.{type_snake}_weights[{arg}.0 as usize];
                        *weight{i} = weight{i}.saturating_add({weight_static_name});
                    "}
                })
            })
            .format("\n");

        let docstring = if is_function {
            let dom_len = arity_types.len() - 1;
            let func_args = rel_args[..dom_len]
                .iter()
                .copied()
                .map(display_var)
                .format(", ");
            let result = display_var(*rel_args.last().expect("func can't have empty arity"));
            formatdoc! {"
                /// Makes the equation `{rel_snake}({func_args}) = {result}` hold.
            "}
        } else {
            let rel_args = rel_args.iter().copied().map(display_var).format(", ");
            formatdoc! {"
                /// Makes `{rel_snake}({rel_args})` hold.
            "}
        };

        let row_args = rel_args
            .iter()
            .copied()
            .map(|var| {
                FmtFn(move |f| {
                    let var = display_var(var);
                    write!(f, "{var}.0")
                })
            })
            .format(", ");

        let insert_fn_name = display_insert_fn_name(rel, eqlog, identifiers);

        writedoc! {f, "
            {docstring}
            #[allow(dead_code)]
            pub fn insert_{rel_snake}(&mut self, {rel_fn_args}) {{
                {canonicalize}
                let row = [{row_args}];
                if {insert_fn_name}(self.{rel_snake}_table, row) {{
                    {update_weights}
                }}
            }}
        "}
    })
}

fn display_new_element_fn_internal<'a>(
    typ: Type,
    eqlog: &'a Eqlog,
    identifiers: &'a BTreeMap<Ident, String>,
) -> impl 'a + Display {
    FmtFn(move |f| {
        let type_camel = display_type(typ, eqlog, identifiers)
            .to_string()
            .to_case(UpperCamel);
        let type_snake = type_camel.to_case(Snake);
        let type_snake = type_snake.as_str();

        let parent_func = eqlog.parent_model_func(typ);
        let parent_param = FmtFn(move |f| {
            let parent_func = match parent_func {
                Some(parent_func) => parent_func,
                None => return Ok(()),
            };

            let parent_type = eqlog.codomain(parent_func).unwrap();
            write!(
                f,
                "parent: {}",
                display_type(parent_type, eqlog, identifiers)
            )
        });

        let insert_parent = FmtFn(move |f| {
            if parent_func.is_none() {
                return Ok(());
            }

            write!(f, "self.insert_{type_snake}_parent(el.into(), parent);")
        });

        writedoc! {f, "
            /// Adjoins a new element of type [{type_camel}].
            #[allow(dead_code)]
            fn new_{type_snake}_internal(&mut self, {parent_param}) -> {type_camel} {{
                let old_len = self.{type_snake}_equalities.len();
                self.{type_snake}_equalities.increase_size_to(old_len + 1);
                let el = u32::try_from(old_len).unwrap();

                self.{type_snake}_new.insert(el);

                assert!(self.{type_snake}_weights.len() == old_len);
                self.{type_snake}_weights.push(0);
                
                {insert_parent}

                {type_camel}::from(el)
            }}
        "}
    })
}

fn display_new_element_fn<'a>(
    typ: Type,
    eqlog: &'a Eqlog,
    identifiers: &'a BTreeMap<Ident, String>,
) -> impl 'a + Display {
    FmtFn(move |f| {
        let type_camel = display_type(typ, eqlog, identifiers)
            .to_string()
            .to_case(UpperCamel);
        let type_snake = type_camel.to_case(Snake);

        let parent_func = eqlog.parent_model_func(typ);
        let parent_param = FmtFn(move |f| {
            let parent_func = match parent_func {
                Some(parent_func) => parent_func,
                None => return Ok(()),
            };

            let parent_type = eqlog.codomain(parent_func).unwrap();
            write!(
                f,
                "parent: {}",
                display_type(parent_type, eqlog, identifiers)
            )
        });

        let parent_arg = FmtFn(move |f| {
            if parent_func.is_none() {
                return Ok(());
            }
            write!(f, "parent")
        });

        writedoc! {f, "
            /// Adjoins a new element of type [{type_camel}].
            #[allow(dead_code)]
            pub fn new_{type_snake}(&mut self, {parent_param}) -> {type_camel} {{
                self.new_{type_snake}_internal({parent_arg})
            }}
        "}
    })
}

fn display_new_enum_element<'a>(
    enum_decl: EnumDeclNode,
    eqlog: &'a Eqlog,
    identifiers: &'a BTreeMap<Ident, String>,
) -> impl Display + 'a {
    FmtFn(move |f: &mut Formatter| -> Result {
        let enum_ident = eqlog
            .iter_enum_decl()
            .find_map(|(enum_decl0, enum_ident, _)| {
                if enum_decl0 == enum_decl {
                    Some(enum_ident)
                } else {
                    None
                }
            })
            .unwrap();
        let enum_name = identifiers.get(&enum_ident).unwrap();
        let enum_name_camel = enum_name.to_case(UpperCamel);
        let enum_name_camel = enum_name_camel.as_str();
        let enum_name_snake = enum_name.to_case(Snake);

        let ctors = eqlog.iter_ctor_enum().filter_map(|(ctor, enum_decl0)| {
            if eqlog.are_equal_enum_decl_node(enum_decl0, enum_decl) {
                Some(ctor)
            } else {
                None
            }
        });

        let match_branches = ctors
            .map(|ctor| {
                FmtFn(move |f: &mut Formatter| -> Result {
                    let ctor_sym_scope = eqlog.ctor_symbol_scope(ctor).unwrap();
                    let ctor_ident = eqlog
                        .iter_ctor_decl()
                        .find_map(|(ctor0, ident, _)| {
                            if eqlog.are_equal_ctor_decl_node(ctor, ctor0) {
                                Some(ident)
                            } else {
                                None
                            }
                        })
                        .unwrap();
                    let ctor_name = identifiers.get(&ctor_ident).unwrap();
                    let ctor_name_snake = ctor_name.to_case(Snake);
                    let ctor_name_camel = ctor_name.to_case(UpperCamel);

                    let ctor_func: Func = eqlog.semantic_func(ctor_sym_scope, ctor_ident).unwrap();
                    let ctor_arg_types: Vec<Type> =
                        type_list_vec(eqlog.flat_domain(ctor_func).unwrap(), eqlog);
                    let ctor_vars = (0..ctor_arg_types.len())
                        .map(|i| display_var(FlatVar(i)))
                        .format(", ");
                    let func_vars = ctor_vars.clone();

                    writedoc! {f, "
                        {enum_name_camel}Case::{ctor_name_camel}({ctor_vars}) => {{
                            self.define_{ctor_name_snake}({func_vars})
                        }}
                    "}
                })
            })
            .format("");

        writedoc! {f, "
            /// Adjoins a new element of type [{enum_name_camel}].
            #[allow(dead_code)]
            pub fn new_{enum_name_snake}(&mut self, value: {enum_name_camel}Case) -> {enum_name_camel} {{
                match value {{
                    {match_branches}
                }}
            }}
        "}
    })
}

fn display_enum_cases_fn<'a>(
    enum_decl: EnumDeclNode,
    eqlog: &'a Eqlog,
    identifiers: &'a BTreeMap<Ident, String>,
) -> impl Display + 'a {
    FmtFn(move |f: &mut Formatter| -> Result {
        let enum_ident = eqlog
            .iter_enum_decl()
            .find_map(|(enum_decl0, enum_ident, _)| {
                if enum_decl0 == enum_decl {
                    Some(enum_ident)
                } else {
                    None
                }
            })
            .unwrap();
        let enum_name = identifiers.get(&enum_ident).unwrap();
        let enum_name_camel = enum_name.to_case(UpperCamel);
        let enum_name_camel = enum_name_camel.as_str();
        let enum_name_snake = enum_name.to_case(Snake);

        let ctors = eqlog.iter_ctor_enum().filter_map(|(ctor, enum_decl0)| {
            if eqlog.are_equal_enum_decl_node(enum_decl0, enum_decl) {
                Some(ctor)
            } else {
                None
            }
        });

        let ctor_value_iters = ctors
            .map(|ctor| {
                FmtFn(move |f: &mut Formatter| -> Result {
                    let ctor_sym_scope = eqlog.ctor_symbol_scope(ctor).unwrap();
                    let ctor_ident = eqlog
                        .iter_ctor_decl()
                        .find_map(|(ctor0, ident, _)| {
                            if eqlog.are_equal_ctor_decl_node(ctor, ctor0) {
                                Some(ident)
                            } else {
                                None
                            }
                        })
                        .unwrap();
                    let ctor_name = identifiers.get(&ctor_ident).unwrap();
                    let ctor_name_snake = ctor_name.to_case(Snake);
                    let ctor_name_camel = ctor_name.to_case(UpperCamel);

                    let ctor_func: Func = eqlog.semantic_func(ctor_sym_scope, ctor_ident).unwrap();
                    let arg_num = type_list_vec(eqlog.flat_domain(ctor_func).unwrap(), eqlog).len();

                    let ctor_arg_vars = (0..arg_num).map(FlatVar);
                    let result_var = FlatVar(arg_num);
                    let tuple_vars = ctor_arg_vars.clone().chain(once(result_var));

                    let ctor_arg_vars = ctor_arg_vars.map(display_var).format(", ");
                    let result_var = display_var(result_var);
                    let tuple_vars = tuple_vars.map(display_var).format(", ");

                    // TODO: We probably want to use an index insted of a linear search here.
                    // However, this function is not needed during the close method, so those
                    // indices should only exist when the host program uses this function, probably
                    // lazily. But we don't have machinery for index lifetimes yet.
                    writedoc! {f, "
                        .chain(self.iter_{ctor_name_snake}().filter_map(move |({tuple_vars})| {{
                            if el == {result_var} {{
                                Some({enum_name_camel}Case::{ctor_name_camel}({ctor_arg_vars}))
                            }} else {{
                                None
                            }}
                        }}))
                    "}
                })
            })
            .format("\n");

        // We need to allow the unused parens here in case of nullary constructors. For those, the
        // iter_{ctor_name_snake} function yields elements instead of tuples, but the argument to
        // the closure we pass to filter_map above still has parens around the single variable.
        writedoc! {f, "
            /// Returns an iterator over ways to destructure an [{enum_name_camel}] element.
            #[allow(dead_code)]
            pub fn {enum_name_snake}_cases<'a>(&'a self, el: {enum_name_camel}) -> impl 'a + Iterator<Item = {enum_name_camel}Case> {{
            let el = self.{enum_name_snake}_equalities.root_const(el);
            #[allow(unused_parens)]
            [].into_iter(){ctor_value_iters}
            }}

            /// Returns the first way to destructure an [{enum_name_camel}] element.
            #[allow(dead_code)]
            pub fn {enum_name_snake}_case(&self, el: {enum_name_camel}) -> {enum_name_camel}Case {{
                self.{enum_name_snake}_cases(el).next().unwrap()
            }}
        "}
    })
}

fn display_equate_elements<'a>(
    typ: Type,
    eqlog: &'a Eqlog,
    identifiers: &'a BTreeMap<Ident, String>,
) -> impl Display + 'a {
    FmtFn(move |f| {
        let type_camel = format!("{}", display_type(typ, eqlog, identifiers)).to_case(UpperCamel);
        let type_snake = type_camel.to_case(Snake);
        writedoc! {f, "
            /// Enforces the equality `lhs = rhs`.
            #[allow(dead_code)]
            pub fn equate_{type_snake}(&mut self, mut lhs: {type_camel}, mut rhs: {type_camel}) {{
                lhs = self.{type_snake}_equalities.root(lhs);
                rhs = self.{type_snake}_equalities.root(rhs);
                if lhs == rhs {{
                    return;
                }}

                let lhs_weight = self.{type_snake}_weights[lhs.0 as usize];
                let rhs_weight = self.{type_snake}_weights[rhs.0 as usize];
                let (root, child) =
                    if lhs_weight >= rhs_weight {{
                        (lhs, rhs)
                    }} else {{
                        (rhs, lhs)
                    }};

                self.{type_snake}_equalities.union_roots_into(child, root);
                
                self.{type_snake}_old.remove(&child.0);
                self.{type_snake}_new.remove(&child.0);
                self.{type_snake}_uprooted.push(child);
            }}
        "}
    })
}

fn display_root_fn(sort: &str) -> impl Display + '_ {
    FmtFn(move |f| {
        let sort_snake = sort.to_case(Snake);
        writedoc! {f, "
            /// Returns the canonical representative of the equivalence class of `el`.
            #[allow(dead_code)]
            pub fn root_{sort_snake}(&self, el: {sort}) -> {sort} {{
                if el.0 as usize >= self.{sort_snake}_equalities.len() {{
                    el
                }} else {{
                    self.{sort_snake}_equalities.root_const(el)
                }}
            }}
        "}
    })
}

fn display_are_equal_fn(sort: &str) -> impl Display + '_ {
    FmtFn(move |f| {
        let sort_snake = sort.to_case(Snake);
        writedoc! {f, "
            /// Returns `true` if `lhs` and `rhs` are in the same equivalence class.
            #[allow(dead_code)]
            pub fn are_equal_{sort_snake}(&self, lhs: {sort}, rhs: {sort}) -> bool {{
                self.root_{sort_snake}(lhs) == self.root_{sort_snake}(rhs)
            }}
        "}
    })
}

fn display_iter_sort_fn(sort: &str) -> impl Display + '_ {
    FmtFn(move |f| {
        let sort_snake = sort.to_case(Snake);
        let sort_camel = sort.to_case(UpperCamel);
        writedoc! {f, "
            /// Returns and iterator over elements of sort `{sort}`.
            /// The iterator yields canonical representatives only.
            #[allow(dead_code)]
            pub fn iter_{sort_snake}(&self) -> impl '_ + Iterator<Item={sort}> {{
                self.{sort_snake}_new.iter().chain(self.{sort_snake}_old.iter()).copied().map({sort_camel}::from)
            }}
        "}
    })
}

fn display_canonicalize_rel_block<'a>(
    rel: Rel,
    eqlog: &'a Eqlog,
    identifiers: &'a BTreeMap<Ident, String>,
) -> impl 'a + Display {
    FmtFn(move |f| {
        let rel_snake = display_rel(rel, eqlog, identifiers)
            .to_string()
            .to_case(Snake);

        let arity = type_list_vec(eqlog.flat_arity(rel).unwrap(), eqlog);
        let tys: BTreeSet<_> = arity.iter().copied().collect();
        for typ in tys {
            let type_snake = display_type(typ, eqlog, identifiers)
                .to_string()
                .to_case(Snake);

            let canonicalize_row = arity
                .iter()
                .copied()
                .enumerate()
                .map(|(i, type_i)| {
                    FmtFn(move |f| {
                        let type_i_snake = display_type(type_i, eqlog, identifiers)
                            .to_string()
                            .to_case(Snake);
                        write!(f, "row[{i}] = self.root_{type_i_snake}(row[{i}].into()).0;")
                    })
                })
                .format("\n");

            let adjust_weights = |op: &'static str| {
                arity
                    .iter()
                    .copied()
                    .enumerate()
                    .map(move |(i, type_i)| {
                        FmtFn(move |f| {
                            let type_i_snake = display_type(type_i, eqlog, identifiers)
                                .to_string()
                                .to_case(Snake);
                            let weight_static_name =
                                display_weight_static_name(rel, eqlog, identifiers);
                            writedoc! {f, "
                                let weight{i} = &mut self.{type_i_snake}_weights[row[{i}] as usize];
                                *weight{i} = weight{i}.saturating_{op}({weight_static_name});
                            "}
                        })
                    })
                    .format("\n")
            };
            let reduce_weights = adjust_weights("sub");
            let increase_weights = adjust_weights("add");

            let drain_fn_name = display_drain_with_element_fn_name(rel, typ, eqlog, identifiers);
            let insert_fn_name = display_insert_fn_name(rel, eqlog, identifiers);

            writedoc! {f, "
                for el in self.{type_snake}_uprooted.iter().copied() {{
                    let rows = {drain_fn_name}(self.{rel_snake}_table, el.0);
                    for mut row in rows {{
                        {reduce_weights}
                        {canonicalize_row}
                        if {insert_fn_name}(self.{rel_snake}_table, row) {{
                            {increase_weights}
                        }}
                    }}
                }}
            "}?;
        }
        Ok(())
    })
}

fn display_canonicalize_fn<'a>(
    eqlog: &'a Eqlog,
    identifiers: &'a BTreeMap<Ident, String>,
) -> impl 'a + Display {
    FmtFn(move |f| {
        let rel_blocks = eqlog
            .iter_rel()
            .map(|rel| display_canonicalize_rel_block(rel, eqlog, identifiers))
            .format("\n");

        let clear_uprooted_vecs = eqlog
            .iter_type()
            .map(|typ| {
                FmtFn(move |f: &mut Formatter| -> Result {
                    let type_snake =
                        format!("{}", display_type(typ, eqlog, identifiers)).to_case(Snake);
                    write!(f, "self.{type_snake}_uprooted.clear();")
                })
            })
            .format("\n");

        writedoc! {f, "
            fn canonicalize(&mut self) {{
                {rel_blocks}

                {clear_uprooted_vecs}
            }}
        "}
    })
}

fn display_model_delta_struct<'a>(
    eqlog: &'a Eqlog,
    identifiers: &'a BTreeMap<Ident, String>,
) -> impl Display + 'a {
    FmtFn(move |f| {
        let new_tuples = eqlog
            .iter_rel()
            .map(|rel| {
                FmtFn(move |f| {
                    let rel_snake = display_rel(rel, eqlog, identifiers)
                        .to_string()
                        .to_case(Snake);
                    let row_type = display_rel_row_type(rel, eqlog);
                    write!(f, "new_{rel_snake}: Vec<{row_type}>,")
                })
            })
            .format("\n");

        let new_equalities = eqlog
            .iter_type()
            .map(|typ| {
                FmtFn(move |f| {
                    let type_snake = display_type(typ, eqlog, identifiers)
                        .to_string()
                        .to_case(Snake);
                    write!(f, "new_{type_snake}_equalities: Vec<(u32, u32)>,")
                })
            })
            .format("\n");

        let new_defines = eqlog
            .iter_func()
            .filter(|func| eqlog.function_can_be_made_defined(*func))
            .map(|func| {
                FmtFn(move |f| {
                    let rel = eqlog.func_rel(func).unwrap();
                    let rel_snake = display_rel(rel, eqlog, identifiers)
                        .to_string()
                        .to_case(Snake);
                    let args_type = display_func_args_type(func, eqlog);
                    write!(f, "new_{rel_snake}_def: Vec<{args_type}>,")
                })
            })
            .format("\n");

        writedoc! {f, "
            #[derive(Debug, Clone)]
            struct ModelDelta {{
            {new_tuples}
            {new_equalities}
            {new_defines}
            }}
        "}
    })
}

fn display_model_delta_impl<'a>(
    eqlog: &'a Eqlog,
    identifiers: &'a BTreeMap<Ident, String>,
) -> impl Display + 'a {
    FmtFn(move |f| {
        writedoc! {f, "
            impl ModelDelta {{
        "}
        .unwrap();

        let new_fn = display_model_delta_new_fn(eqlog, identifiers);
        write!(f, "{}", new_fn).unwrap();

        let apply_surjective_fn = display_model_delta_apply_surjective_fn();
        write!(f, "{}", apply_surjective_fn).unwrap();

        let apply_non_surjective_fn = display_model_delta_apply_non_surjective_fn();
        write!(f, "{}", apply_non_surjective_fn).unwrap();

        let apply_equalities_fn = display_model_delta_apply_equalities_fn(eqlog, identifiers);
        write!(f, "{}", apply_equalities_fn).unwrap();

        let apply_tuples_fn = display_model_delta_apply_tuples_fn(eqlog, identifiers);
        write!(f, "{}", apply_tuples_fn).unwrap();

        let apply_def_fn = display_model_delta_apply_def_fn(eqlog, identifiers);
        write!(f, "{}", apply_def_fn).unwrap();

        writedoc! {f, "
            }}
        "}
    })
}

fn display_model_delta_new_fn<'a>(
    eqlog: &'a Eqlog,
    identifiers: &'a BTreeMap<Ident, String>,
) -> impl Display + 'a {
    FmtFn(move |f| {
        let new_tuples = eqlog
            .iter_rel()
            .map(|rel| {
                FmtFn(move |f| {
                    let relation_snake = display_rel(rel, eqlog, identifiers)
                        .to_string()
                        .to_case(Snake);
                    write!(f, "new_{relation_snake}: Vec::new(),")
                })
            })
            .format("\n");

        let new_equalities = eqlog
            .iter_type()
            .map(|typ| {
                FmtFn(move |f| {
                    let type_snake = display_type(typ, eqlog, identifiers)
                        .to_string()
                        .to_case(Snake);
                    write!(f, "new_{type_snake}_equalities: Vec::new(),")
                })
            })
            .format("\n");
        let new_defines = eqlog
            .iter_func()
            .filter(|&func| eqlog.function_can_be_made_defined(func))
            .map(|func| {
                FmtFn(move |f| {
                    let rel = eqlog.func_rel(func).unwrap();
                    let func_snake = display_rel(rel, eqlog, identifiers)
                        .to_string()
                        .to_case(Snake);
                    write!(f, "new_{func_snake}_def: Vec::new(),")
                })
            })
            .format("\n");

        writedoc! {f, "
            fn new() -> ModelDelta {{
                ModelDelta{{
            {new_tuples}
            {new_equalities}
            {new_defines}
                }}
            }}
        "}
    })
}

fn display_model_delta_apply_surjective_fn() -> impl Display {
    FmtFn(|f| {
        writedoc! {f, "
            fn apply_surjective(&mut self, model: &mut Model) {{
                self.apply_equalities(model);
                self.apply_tuples(model);
            }}
        "}
    })
}

fn display_model_delta_apply_non_surjective_fn() -> impl Display {
    FmtFn(|f| {
        writedoc! {f, "
            fn apply_non_surjective(&mut self, model: &mut Model) {{
                self.apply_func_defs(model);
            }}
        "}
    })
}

fn display_model_delta_apply_equalities_fn<'a>(
    eqlog: &'a Eqlog,
    identifiers: &'a BTreeMap<Ident, String>,
) -> impl Display + 'a {
    FmtFn(move |f| {
        let type_equalities = eqlog
            .iter_type()
            .map(|typ| {
                FmtFn(move |f: &mut Formatter| -> Result {
                    let type_snake =
                        format!("{}", display_type(typ, eqlog, identifiers)).to_case(Snake);

                    writedoc! {f, "
                        for (lhs, rhs) in self.new_{type_snake}_equalities.drain(..) {{
                            model.equate_{type_snake}(lhs.into(), rhs.into());
                        }}
                    "}
                })
            })
            .format("\n");

        writedoc! {f, "
            #[allow(unused)]
            fn apply_equalities(&mut self, model: &mut Model) {{
            {type_equalities}
            }}
        "}
    })
}

fn display_model_delta_apply_tuples_fn<'a>(
    eqlog: &'a Eqlog,
    identifiers: &'a BTreeMap<Ident, String>,
) -> impl 'a + Display {
    FmtFn(move |f| {
        let relations = eqlog
            .iter_rel()
            .map(|rel| {
                FmtFn(move |f| {
                    let arity = type_list_vec(eqlog.flat_arity(rel).unwrap(), eqlog);
                    let rel_snake = display_rel(rel, eqlog, identifiers)
                        .to_string()
                        .to_case(Snake);
                    let args_destructure =
                        (0..arity.len()).map(FlatVar).map(display_var).format(", ");
                    let insert_args = (0..arity.len())
                        .map(|i| {
                            FmtFn(move |f| {
                                let var = FlatVar(i);
                                let var = display_var(var);
                                write!(f, "{var}.into()")
                            })
                        })
                        .format(", ");

                    writedoc! {f, "
                    for [{args_destructure}] in self.new_{rel_snake}.drain(..) {{
                        model.insert_{rel_snake}({insert_args});
                    }}
                "}
                })
            })
            .format("\n");

        // allow(unused_variables) is there for theories without relations.
        writedoc! {f, "
            #[allow(unused_variables)]
            fn apply_tuples(&mut self, model: &mut Model) {{
                {relations}
            }}
        "}
    })
}

fn display_model_delta_apply_def_fn<'a>(
    eqlog: &'a Eqlog,
    identifiers: &'a BTreeMap<Ident, String>,
) -> impl Display + 'a {
    FmtFn(move |f| {
        let func_defs = eqlog
            .iter_semantic_func()
            .filter_map(|(_, ident, func)| {
                if !eqlog.function_can_be_made_defined(func) {
                    return None;
                }

                let func_name = identifiers.get(&ident).unwrap();
                let func_snake = func_name.to_case(Snake);

                let domain = type_list_vec(eqlog.flat_domain(func).unwrap(), eqlog);

                let args_destructure = (0..domain.len()).map(FlatVar).map(display_var).format(", ");
                let define_args = (0..domain.len())
                    .map(|i| {
                        FmtFn(move |f| {
                            let var = FlatVar(i);
                            let var = display_var(var);
                            write!(f, "{var}.into()")
                        })
                    })
                    .format(", ");

                Some(FmtFn(move |f: &mut Formatter| -> Result {
                    writedoc! {f, "
                            for [{args_destructure}] in self.new_{func_snake}_def.drain(..) {{
                                model.define_{func_snake}({define_args});
                            }}
                        "}
                }))
            })
            .format("\n");

        // allow(unused_variables) is there for theories without functions.
        writedoc! {f, "
            #[allow(unused_variables)]
            fn apply_func_defs(&mut self, model: &mut Model) {{
                {func_defs}
            }}
        "}
    })
}

fn display_var(var: FlatVar) -> impl Display {
    FmtFn(move |f: &mut Formatter| -> Result {
        let var = var.0;
        write!(f, "tm{var}")?;
        Ok(())
    })
}

fn display_drop_dirt_fn<'a>(
    eqlog: &'a Eqlog,
    identifiers: &'a BTreeMap<Ident, String>,
) -> impl Display + 'a {
    FmtFn(move |f| {
        let relations = eqlog
            .iter_rel()
            .map(|rel| {
                FmtFn(move |f| {
                    let move_new_to_old_fn_name =
                        display_move_new_to_old_fn_name(rel, eqlog, identifiers);
                    let rel_snake = display_rel(rel, eqlog, identifiers)
                        .to_string()
                        .to_case(Snake);
                    writedoc! {f, "
                        {move_new_to_old_fn_name}(self.{rel_snake}_table);
                    "}
                })
            })
            .format("\n");
        let types = eqlog
            .iter_type()
            .map(|typ| {
                FmtFn(move |f| {
                    let type_snake = display_type(typ, eqlog, identifiers)
                        .to_string()
                        .to_case(Snake);
                    write!(
                        f,
                        "self.{type_snake}_old.append(&mut self.{type_snake}_new);"
                    )
                })
            })
            .format("\n");

        writedoc! {f, "
            fn drop_dirt(&mut self) {{
            self.empty_join_is_dirty = false;

            {relations}

            {types}
            }}
        "}
    })
}

fn display_rule_env_var<'a>(
    rule: &'a str,
    analysis: &'a FlatRuleAnalysis<'a>,
    eqlog: &'a Eqlog,
    identifiers: &'a BTreeMap<Ident, String>,
) -> impl Display + 'a {
    FmtFn(move |f| {
        let rule_camel = rule.to_case(UpperCamel);

        let table_fields = analysis
            .used_rels
            .iter()
            .map(|rel| {
                FmtFn(move |f| {
                    let rel_snake = display_rel(*rel, eqlog, identifiers)
                        .to_string()
                        .to_case(Snake);
                    write!(f, "{rel_snake}_table: self.{rel_snake}_table,")
                })
            })
            .format("\n");

        let type_set_fields = analysis
            .used_types
            .iter()
            .map(|typ| {
                FmtFn(move |f| {
                    let type_snake = display_type(*typ, eqlog, identifiers)
                        .to_string()
                        .to_case(Snake);
                    writedoc! {f, "
                        {type_snake}_new: &self.{type_snake}_new,
                        {type_snake}_old: &self.{type_snake}_old,
                    "}
                })
            })
            .format("\n");

        let new_rel_fields = analysis
            .used_rels
            .iter()
            .map(|rel| {
                FmtFn(move |f| {
                    let rel_snake = display_rel(*rel, eqlog, identifiers)
                        .to_string()
                        .to_case(Snake);

                    writedoc! {f, "
                        new_{rel_snake}: &mut delta.new_{rel_snake},
                    "}?;

                    if let RelCase::FuncRel(func) = eqlog.rel_case(*rel) {
                        if eqlog.function_can_be_made_defined(func) {
                            writedoc! {f, "
                                new_{rel_snake}_def: &mut delta.new_{rel_snake}_def,
                            "}?;
                        }
                    }

                    Ok(())
                })
            })
            .format("\n");

        let new_type_equalities_fields = analysis
            .used_types
            .iter()
            .map(|typ| {
                FmtFn(move |f| {
                    let type_snake = display_type(*typ, eqlog, identifiers)
                        .to_string()
                        .to_case(Snake);

                    writedoc! {f, "
                        new_{type_snake}_equalities: &mut delta.new_{type_snake}_equalities,
                    "}
                })
            })
            .format("\n");

        writedoc! {f, "
            let mut env = {rule_camel}Env {{
                {table_fields}
                {type_set_fields}
                {new_rel_fields}
                {new_type_equalities_fields}
            }};
        "}
    })
}

fn display_close_until_fn<'a>(
    rules: &'a [FlatRule],
    analyses: &'a [FlatRuleAnalysis],
    eqlog: &'a Eqlog,
    identifiers: &'a BTreeMap<Ident, String>,
) -> impl Display + 'a {
    FmtFn(move |f| {
        let rules = rules
            .iter()
            .zip(analyses.iter())
            .map(|(rule, analysis)| {
                FmtFn(move |f: &mut Formatter| -> Result {
                    let name = rule.name.as_str();
                    let rule_fn_name = display_rule_fn_name(name);
                    let env_var = display_rule_env_var(name, analysis, eqlog, identifiers);
                    writedoc! {f, r#"
                        {env_var}
                        {rule_fn_name}(&mut env);
                    "#}
                })
            })
            .format("\n");

        writedoc! {f, "
            /// Closes the model under all axioms until `condition` is satisfied.
            /// Depending on the axioms and `condition`, this may run indefinitely.
            /// Returns `true` if the `condition` eventually holds.
            /// Returns `false` if the model could be closed under all axioms but `condition` still does not hold.
            #[allow(dead_code)]
            pub fn close_until(&mut self, condition: impl Fn(&Self) -> bool) -> bool
            {{
                let mut delta = ModelDelta::new();

                self.canonicalize();
                if condition(self) {{
                    return true;
                }}

                while self.is_dirty() {{
                    loop {{
            {rules}

                        self.drop_dirt();
                        delta.apply_surjective(self);
                        self.canonicalize();

                        if condition(self) {{
                            return true;
                        }}

                        if !self.is_dirty() {{
                            break;
                        }}
                    }}

                    delta.apply_non_surjective (self);
                    if condition(self) {{
                        return true;
                    }}
                }}

                false
            }}
        "}
    })
}

fn display_close_fn() -> impl Display {
    FmtFn(|f| {
        writedoc! {f, "
            /// Closes the model under all axioms.
            /// Depending on the axioms and the model, this may run indefinitely.
            #[allow(dead_code)]
            pub fn close(&mut self) {{
                self.close_until(|_: &Self| false);
            }}
        "}
    })
}

fn display_new_fn<'a>(
    eqlog: &'a Eqlog,
    identifiers: &'a BTreeMap<Ident, String>,
) -> impl Display + 'a {
    FmtFn(move |f| {
        writeln!(f, "/// Creates an empty model.").unwrap();
        writeln!(f, "#[allow(dead_code)]").unwrap();
        writeln!(f, "pub fn new() -> Self {{").unwrap();
        writeln!(f, "Self {{").unwrap();
        for typ in eqlog.iter_type() {
            let type_snake = display_type(typ, eqlog, identifiers)
                .to_string()
                .to_case(Snake);
            writeln!(f, "{type_snake}_equalities: Unification::new(),").unwrap();
            writeln!(f, "{type_snake}_weights: Vec::new(),").unwrap();
            writeln!(f, "{type_snake}_new: BTreeSet::new(),").unwrap();
            writeln!(f, "{type_snake}_old: BTreeSet::new(),").unwrap();
            writeln!(f, "{type_snake}_uprooted: Vec::new(),").unwrap();
        }
        for rel in eqlog.iter_rel() {
            let rel_snake = display_rel(rel, eqlog, identifiers)
                .to_string()
                .to_case(Snake);
            //let rel_camel = rel_snake.to_case(UpperCamel);
            let new_fn_name = display_table_new_fn_name(rel, eqlog, identifiers);
            //writeln!(f, "{rel_snake}: {rel_camel}TableOld::new(),").unwrap();
            writeln!(f, "{rel_snake}_table: {new_fn_name}(),").unwrap();
        }
        writeln!(f, "empty_join_is_dirty: true,").unwrap();
        writeln!(f, "}}").unwrap();
        write!(f, "}}").unwrap();
        Ok(())
    })
}

fn display_define_fn<'a>(
    func: Func,
    eqlog: &'a Eqlog,
    identifiers: &'a BTreeMap<Ident, String>,
) -> impl Display + 'a {
    FmtFn(move |f| {
        let func_snake = display_func_snake(func, eqlog, identifiers);

        let domain = type_list_vec(eqlog.flat_domain(func).expect("should be total"), eqlog);
        let codomain = eqlog.codomain(func).expect("should be total");

        let codomain_camel =
            format!("{}", display_type(codomain, eqlog, identifiers)).to_case(UpperCamel);
        let codomain_snake = codomain_camel.to_case(Snake);

        let func_arg_vars: Vec<FlatVar> = (0..domain.len()).map(FlatVar).collect();
        let result_var = FlatVar(domain.len());

        let fn_args = func_arg_vars
            .iter()
            .copied()
            .zip(domain.iter().copied())
            .map(|(var, var_typ)| {
                FmtFn(move |f: &mut Formatter| -> Result {
                    let type_camel = format!("{}", display_type(var_typ, eqlog, identifiers))
                        .to_case(UpperCamel);
                    let var = display_var(var);
                    write!(f, "{var}: {type_camel}")
                })
            })
            .format(", ");

        let args = func_arg_vars
            .iter()
            .copied()
            .map(display_var)
            .format(", ")
            .to_string();
        let rel_args = func_arg_vars
            .iter()
            .copied()
            .chain(once(result_var))
            .map(display_var)
            .format(", ");
        let result_var = display_var(result_var);

        let codomain_parent_func = eqlog.parent_model_func(codomain);
        let parent_arg = FmtFn(move |f| {
            if codomain_parent_func.is_none() {
                return Ok(());
            }

            let parent_var = display_var(FlatVar(0));
            write!(f, "{parent_var}")
        });

        writedoc! {f, "
            /// Enforces that `{func_snake}({args})` is defined, adjoining a new element if necessary.
            #[allow(dead_code)]
            pub fn define_{func_snake}(&mut self, {fn_args}) -> {codomain_camel} {{
                match self.{func_snake}({args}) {{
                    Some(result) => result,
                    None => {{
                        // TODO: The parent var, if any, is only correct if the codomain type
                        // is defined in the same model (and not a parent model) that the function
                        // is declared in.
                        let {result_var} = self.new_{codomain_snake}_internal({parent_arg});
                        self.insert_{func_snake}({rel_args});
                        {result_var}
                    }}
                }}
            }}
        "}
    })
}

fn display_theory_drop_impl<'a>(
    theory_type_name: &'a str,
    eqlog: &'a Eqlog,
    identifiers: &'a BTreeMap<Ident, String>,
) -> impl Display + 'a {
    FmtFn(move |f| {
        let drop_tables = eqlog
            .iter_rel()
            .map(|rel| {
                FmtFn(move |f| {
                    let rel_snake = display_rel(rel, eqlog, identifiers)
                        .to_string()
                        .to_case(Snake);
                    let drop_fn_name = display_table_drop_fn_name(rel, eqlog, identifiers);
                    write!(
                        f,
                        "{drop_fn_name}(NonNull::new_unchecked(self.{rel_snake}_table as *mut _));"
                    )
                })
            })
            .format("\n");

        writedoc! {f, "
            impl Drop for {theory_type_name} {{
            fn drop(&mut self) {{
            #[allow(unused_unsafe)]
            unsafe {{
            {drop_tables}
            }}
            }}
            }}"}
    })
}

fn display_theory_struct<'a>(
    name: &'a str,
    eqlog: &'a Eqlog,
    identifiers: &'a BTreeMap<Ident, String>,
) -> impl Display + 'a {
    FmtFn(move |f| {
        writeln!(f, "/// A model of the `{name}` theory.").unwrap();
        writeln!(f, "pub struct {} {{", name).unwrap();
        for typ in eqlog.iter_type() {
            let type_camel = display_type(typ, eqlog, identifiers)
                .to_string()
                .to_case(UpperCamel);
            let sort_fields = display_sort_fields(type_camel.as_str());
            write!(f, "{}", sort_fields).unwrap();
            writeln!(f, "").unwrap();
        }

        for rel in eqlog.iter_rel() {
            let rel_snake = display_rel(rel, eqlog, identifiers)
                .to_string()
                .to_case(Snake);
            let rel_camel = rel_snake.to_case(UpperCamel);
            writeln!(f, "{rel_snake}_table: &'static mut {rel_camel}Table,").unwrap();
        }

        writeln!(f, "empty_join_is_dirty: bool,").unwrap();
        writeln!(f, "}}").unwrap();
        write!(f, "type Model = {name};").unwrap();
        Ok(())
    })
}

fn display_theory_impl<'a>(
    name: &'a str,
    rules: &'a [FlatRule],
    analyses: &'a [FlatRuleAnalysis],
    eqlog: &'a Eqlog,
    identifiers: &'a BTreeMap<Ident, String>,
    index_selection: &'a IndexSelection,
) -> impl Display + 'a {
    FmtFn(move |f| {
        writeln!(f, "impl {} {{", name).unwrap();

        let new_fn = display_new_fn(eqlog, identifiers);
        write!(f, "{}", new_fn).unwrap();
        writeln!(f, "").unwrap();

        let close_fn = display_close_fn();
        write!(f, "{}", close_fn).unwrap();

        let close_until_fn = display_close_until_fn(rules, analyses, eqlog, identifiers);
        write!(f, "{}", close_until_fn).unwrap();

        for typ in eqlog.iter_type() {
            let type_name = display_type(typ, eqlog, identifiers)
                .to_string()
                .to_case(UpperCamel);

            let iter_sort_fn = display_iter_sort_fn(type_name.as_str());
            write!(f, "{}", iter_sort_fn).unwrap();

            let root_fn = display_root_fn(type_name.as_str());
            write!(f, "{}", root_fn).unwrap();

            let are_equal_fn = display_are_equal_fn(type_name.as_str());
            write!(f, "{}", are_equal_fn).unwrap();

            writeln!(f, "").unwrap();
        }

        for typ in eqlog.iter_type() {
            let new_element_fn_internal = display_new_element_fn_internal(typ, eqlog, identifiers);
            writeln!(f, "{new_element_fn_internal}").unwrap();

            let equate_elements = display_equate_elements(typ, eqlog, identifiers);
            write!(f, "{}", equate_elements).unwrap();
        }

        for typ in eqlog.iter_type() {
            if eqlog.is_normal_type(typ) || eqlog.is_model_type(typ) {
                let new_el_fn = display_new_element_fn(typ, eqlog, identifiers);
                writeln!(f, "{new_el_fn}").unwrap();
            } else if eqlog.is_enum_type(typ) {
                let type_def_sym_scope = eqlog.type_definition_symbol_scope(typ).unwrap();
                let enum_node = eqlog
                    .iter_enum_decl()
                    .find_map(|(enum_node, ident, _)| {
                        let typ0 = eqlog.semantic_type(type_def_sym_scope, ident)?;
                        if eqlog.are_equal_type(typ0, typ) {
                            Some(enum_node)
                        } else {
                            None
                        }
                    })
                    .unwrap();
                let new_enum_el_fn = display_new_enum_element(enum_node, eqlog, identifiers);
                let enum_cases_fn = display_enum_cases_fn(enum_node, eqlog, identifiers);
                writedoc! {f, "
                    {new_enum_el_fn}
                    {enum_cases_fn}
                "}
                .unwrap();
            } else {
                unreachable!("Unhandled type kind");
            }
        }

        for func in eqlog.iter_func() {
            let rel = eqlog.func_rel(func).unwrap();
            let eval_fn = display_pub_function_eval_fn(func, eqlog, identifiers, index_selection);
            write!(f, "{eval_fn}").unwrap();

            let iter_fn = display_pub_iter_fn(rel, eqlog, identifiers, index_selection);
            write!(f, "{}", iter_fn).unwrap();

            let insert_relation = display_pub_insert_relation(rel, eqlog, identifiers, true);
            write!(f, "{}", insert_relation).unwrap();

            writeln!(f, "").unwrap();
        }

        for func in eqlog.iter_func() {
            if eqlog.function_can_be_made_defined(func) {
                let define_fn = display_define_fn(func, eqlog, identifiers);
                write!(f, "{}", define_fn).unwrap();
            }
        }

        for pred in eqlog.iter_pred() {
            let rel = eqlog.pred_rel(pred).unwrap();
            let arity = type_list_vec(eqlog.flat_arity(rel).unwrap(), eqlog);
            let arity: Vec<String> = arity
                .into_iter()
                .map(|typ| display_type(typ, eqlog, identifiers).to_string())
                .collect();
            let arity: Vec<&str> = arity.iter().map(|s| s.as_str()).collect();

            let predicate_holds_fn = display_pub_predicate_holds_fn(rel, eqlog, identifiers);
            write!(f, "{}", predicate_holds_fn).unwrap();

            if !arity.is_empty() {
                let iter_fn = display_pub_iter_fn(rel, eqlog, identifiers, index_selection);
                write!(f, "{}", iter_fn).unwrap();
            }

            let insert_relation = display_pub_insert_relation(rel, eqlog, identifiers, false);
            write!(f, "{}", insert_relation).unwrap();

            writeln!(f, "").unwrap();
        }

        let canonicalize_fn = display_canonicalize_fn(eqlog, identifiers);
        write!(f, "{canonicalize_fn}\n").unwrap();

        let is_dirty_fn = display_is_dirty_fn(eqlog, identifiers);
        write!(f, "{}", is_dirty_fn).unwrap();

        writeln!(f, "").unwrap();

        let drop_dirt_fn = display_drop_dirt_fn(eqlog, identifiers);
        write!(f, "{}", drop_dirt_fn).unwrap();

        write!(f, "}}").unwrap();
        Ok(())
    })
}

pub fn display_table_struct_decls<'a>(
    eqlog: &'a Eqlog,
    identifiers: &'a BTreeMap<Ident, String>,
) -> impl 'a + Display {
    eqlog
        .iter_rel()
        .map(move |rel| display_table_struct_decl(rel, eqlog, identifiers))
        .format("\n")
}

pub fn display_table_extern_decls<'a>(
    eqlog: &'a Eqlog,
    identifiers: &'a BTreeMap<Ident, String>,
    symbol_prefix: &'a str,
    index_selection: &'a IndexSelection,
) -> impl 'a + Display {
    FmtFn(move |f| {
        let rel_tables_fns = eqlog
            .iter_rel()
            .map(move |rel| {
                FmtFn(move |f| {
                    let rel_name = display_rel(rel, eqlog, identifiers).to_string();
                    let indices = index_selection.get(&rel_name).unwrap();
                    let types: BTreeSet<Type> =
                        type_list_vec(eqlog.flat_arity(rel).unwrap(), eqlog)
                            .into_iter()
                            .collect();

                    let new_fn_decl =
                        display_table_new_fn_decl(rel, eqlog, identifiers, symbol_prefix);
                    writeln!(f, "{new_fn_decl}")?;

                    let drop_fn_decl =
                        display_table_drop_fn_decl(rel, eqlog, identifiers, symbol_prefix);
                    writeln!(f, "{drop_fn_decl}")?;

                    let contains_fn_decl =
                        display_contains_fn_decl(rel, eqlog, identifiers, symbol_prefix);
                    writeln!(f, "{contains_fn_decl}")?;

                    match eqlog.rel_case(rel) {
                        RelCase::FuncRel(func) => {
                            let eval_fn_decl =
                                display_eval_fn_decl(func, eqlog, identifiers, symbol_prefix);
                            writeln!(f, "{eval_fn_decl}")?;
                        }
                        RelCase::PredRel(pred) => {}
                    }

                    let insert_fn_decl =
                        display_insert_fn_decl(rel, eqlog, identifiers, symbol_prefix);
                    writeln!(f, "{insert_fn_decl}")?;

                    for typ in types {
                        let drain_fn_decl = display_drain_with_element_fn_decl(
                            rel,
                            typ,
                            eqlog,
                            identifiers,
                            symbol_prefix,
                        );
                        writeln!(f, "{drain_fn_decl}")?;
                    }

                    let move_new_to_old_fn_decl =
                        display_move_new_to_old_fn_decl(rel, eqlog, identifiers, symbol_prefix);
                    writeln!(f, "{move_new_to_old_fn_decl}")?;

                    let has_new_data_fn_decl =
                        display_has_new_data_fn_decl(rel, eqlog, identifiers, symbol_prefix);
                    writeln!(f, "{has_new_data_fn_decl}")?;

                    let index_specs: BTreeSet<&IndexSpec> = indices.values().flatten().collect();
                    for index in index_specs {
                        let index_getter_fn_decl = display_index_getter_decl(
                            index,
                            rel,
                            eqlog,
                            identifiers,
                            symbol_prefix,
                        );
                        writeln!(f, "{index_getter_fn_decl}")?;
                    }

                    let weight_static_decl =
                        display_weight_static_decl(rel, eqlog, identifiers, symbol_prefix);
                    write!(f, "{weight_static_decl}")
                })
            })
            .format("\n");

        writedoc! {f, r#"
            #[allow(unused, clashing_extern_declarations)]
            unsafe extern "Rust" {{
            {rel_tables_fns}
            }}
        "#}
    })
}

fn display_table_modules<'a>(
    eqlog: &'a Eqlog,
    identifiers: &'a BTreeMap<Ident, String>,
    index_selection: &'a IndexSelection,
    symbol_prefix: &'a str,
) -> impl 'a + Display {
    eqlog
        .iter_rel()
        .map(move |rel| {
            FmtFn(move |f| {
                let rel_string = display_rel(rel, eqlog, identifiers).to_string();
                let rel_snake = rel_string.to_case(Snake);

                let index_selection = index_selection.get(&rel_string).unwrap();

                let lib =
                    display_table_lib(rel, index_selection, eqlog, identifiers, symbol_prefix);

                writedoc! {f, "
                mod {rel_snake} {{
                    {lib}
                }}
            "}
            })
        })
        .format("\n")
}

fn display_rule_modules<'a>(
    rules: &'a [FlatRule],
    analyses: &'a [FlatRuleAnalysis],
    index_selection: &'a IndexSelection,
    eqlog: &'a Eqlog,
    identifiers: &'a BTreeMap<Ident, String>,
    symbol_prefix: &'a str,
) -> impl 'a + Display {
    rules
        .iter()
        .zip(analyses)
        .map(move |(rule, analysis)| {
            FmtFn(move |f| {
                let lib = display_rule_lib(
                    rule,
                    analysis,
                    index_selection,
                    eqlog,
                    identifiers,
                    symbol_prefix,
                );
                let rule_snake = rule.name.to_case(Snake);
                writedoc! {f, "
                mod {rule_snake} {{
                    {lib}
                }}
            "}
            })
        })
        .format("\n")
}

pub fn display_module<'a>(
    name: &'a str,
    eqlog: &'a Eqlog,
    identifiers: &'a BTreeMap<Ident, String>,
    rules: &'a [FlatRule],
    analyses: &'a [FlatRuleAnalysis],
    index_selection: &'a IndexSelection,
    symbol_prefix: &'a str,
    build_type: BuildType,
) -> impl 'a + Display {
    FmtFn(move |f| {
        let imports = display_imports();
        write!(f, "{}", imports)?;
        write!(f, "\n")?;

        match build_type {
            BuildType::Component => {}
            BuildType::Module => {
                display_table_modules(eqlog, identifiers, index_selection, symbol_prefix).fmt(f)?;
                display_rule_modules(
                    rules,
                    analyses,
                    index_selection,
                    eqlog,
                    identifiers,
                    symbol_prefix,
                )
                .fmt(f)?;
            }
        }

        writeln!(f, "{}", display_table_struct_decls(eqlog, identifiers))?;
        writeln!(
            f,
            "{}",
            display_table_extern_decls(eqlog, identifiers, symbol_prefix, index_selection)
        )?;

        let rule_env_structs = analyses
            .iter()
            .map(|analysis| display_rule_env_struct(analysis, eqlog, identifiers))
            .format("\n");
        writeln!(f, "{rule_env_structs}")?;

        let rule_eval_fns = rules
            .iter()
            .map(|rule| display_rule_fn_decl(rule.name.as_str(), symbol_prefix))
            .format("\n");
        writedoc! {f, r#"
            #[allow(clashing_extern_declarations)]
            unsafe extern "Rust" {{
                {rule_eval_fns}
            }}
        "#}?;

        for typ in eqlog.iter_type() {
            let type_camel = display_type(typ, eqlog, identifiers)
                .to_string()
                .to_case(UpperCamel);
            let sort_struct = display_sort_struct(type_camel.as_str());
            write!(f, "{}", sort_struct)?;
            let sort_impl = display_sort_impl(type_camel.as_str());
            write!(f, "{}", sort_impl)?;
        }
        write!(f, "\n")?;

        for (enum_decl, _, _) in eqlog.iter_enum_decl() {
            writeln!(f, "{}", display_enum(enum_decl, eqlog, identifiers))?;
        }

        for func in eqlog.iter_func() {
            let func_args_struct = display_func_args_struct(func, eqlog, identifiers);
            writeln!(f, "{func_args_struct}")?;
        }

        write!(f, "\n")?;

        let model_delta_struct = display_model_delta_struct(eqlog, identifiers);
        write!(f, "{}", model_delta_struct)?;

        let theory_struct = display_theory_struct(name, eqlog, identifiers);
        write!(f, "{}", theory_struct)?;

        let model_delta_impl = display_model_delta_impl(eqlog, identifiers);
        write!(f, "{}", model_delta_impl)?;
        write!(f, "\n")?;

        let theory_impl =
            display_theory_impl(name, rules, analyses, eqlog, identifiers, index_selection);
        write!(f, "{}", theory_impl)?;

        let drop_impl = display_theory_drop_impl(name, eqlog, identifiers);
        write!(f, "{}", drop_impl)?;

        Ok(())
    })
}

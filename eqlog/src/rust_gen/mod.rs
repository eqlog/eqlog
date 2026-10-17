mod context;
mod dynamic;
mod flat_eqlog;
mod indices;
mod native_indices;
mod rule;
mod stratified;
mod transport;
mod types;

pub(crate) use context::RustGenCtx;
pub use rule::*;
pub use types::*;

use crate::algebra::signature::{FuncId, MorphismMemberTypes, TypeId, TypeKind};
use crate::ast::EnumDeclId;
use crate::flat_eqlog::*;
use crate::fmt_util::*;
use crate::options::ModelMode;
use crate::ram::*;
use convert_case::{Case, Casing};
use indoc::{formatdoc, writedoc};
use itertools::Itertools;
use std::collections::{BTreeMap, BTreeSet};
use std::fmt::{Display, Formatter, Result};
use std::iter::once;

use Case::{Snake, UpperCamel, UpperSnake};

impl From<usize> for ElVar {
    fn from(i: usize) -> Self {
        ElVar {
            name: format!("el{i}").into(),
        }
    }
}

fn display_func(func: FuncId, ctx: &RustGenCtx<'_>) -> String {
    ctx.func_name(func).to_case(Snake)
}

pub(crate) fn display_type<'a>(typ: TypeId, ctx: &'a RustGenCtx<'a>) -> impl 'a + Display {
    FmtFn(move |f| write!(f, "{}", ctx.type_name(typ)))
}

pub(crate) fn display_rel(rel: FlatRel, ctx: &RustGenCtx<'_>) -> String {
    ctx.rel_name(rel)
}

fn display_imports() -> impl Display {
    FmtFn(|f| {
        writedoc! { f, "
            #[allow(unused)]
            use std::collections::{{btree_set, BTreeSet, BTreeMap}};
            #[allow(unused)]
            use std::fmt;
            #[allow(unused)]
            use eqlog_runtime::*;
            #[allow(unused)]
            use std::ops::Bound;
            #[allow(unused)]
            use std::ptr::NonNull;
            #[allow(unused)]
            use std::cell::LazyCell;
            #[allow(unused)]
            use std::ops::DerefMut;
        "}
    })
}

// #[derive(Copy, Clone, PartialEq, Eq, Debug, Hash, PartialOrd, Ord)]
// pub struct TypeName(pub u32);
fn display_type_struct<'a>(typ: TypeId, ctx: &'a RustGenCtx<'a>) -> impl 'a + Display {
    FmtFn(move |f| {
        let type_name = display_type(typ, ctx).to_string().to_case(UpperCamel);
        writedoc! {f, "
            #[allow(dead_code)]
            #[derive(Copy, Clone, PartialEq, Eq, Debug, Hash, PartialOrd, Ord)]
            pub struct {type_name}(pub u32);
        "}
    })
}

fn display_type_impl<'a>(typ: TypeId, ctx: &'a RustGenCtx<'a>) -> impl 'a + Display {
    FmtFn(move |f| {
        let type_name = display_type(typ, ctx).to_string().to_case(UpperCamel);
        writedoc! {f, "
            impl Into<u32> for {type_name} {{ fn into(self) -> u32 {{ self.0 }} }}
            impl From<u32> for {type_name} {{ fn from(x: u32) -> Self {{ {type_name}(x) }} }}
            impl fmt::Display for {type_name} {{
                fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {{
                    write!(f, \"{{:?}}\", self)
                }}
            }}
        "}
    })
}

fn display_ctor<'a>(ctor: crate::ast::CtorDeclId, ctx: &'a RustGenCtx<'a>) -> impl 'a + Display {
    FmtFn(move |f: &mut Formatter| -> Result {
        let ctor_name: String = ctx.ast().ctor_decl(ctor).name.to_case(UpperCamel);
        let ctor_func = ctx
            .signature()
            .func_for_ctor_decl(ctor)
            .expect("constructor declaration should have a function id");
        let domain = flat_domain(ctor_func, ctx.signature());

        let domain = domain
            .into_iter()
            .map(|typ| display_type(typ, ctx))
            .format(", ");

        write!(f, "{}({})", ctor_name, domain)
    })
}

fn display_enum<'a>(enum_decl: EnumDeclId, ctx: &'a RustGenCtx<'a>) -> impl 'a + Display {
    FmtFn(move |f: &mut Formatter| -> Result {
        let ctors = ctx
            .ast()
            .enum_decl(enum_decl)
            .ctors
            .iter()
            .copied()
            .map(|ctor| format!("{},\n", display_ctor(ctor, ctx)))
            .format("");

        let enum_name = ctx.ast().enum_decl(enum_decl).name.to_case(UpperCamel);

        writedoc! {f, "
            #[allow(unused)]
            #[derive(Copy, Clone, PartialEq, Eq, Debug, Hash, PartialOrd, Ord)]
            pub enum {enum_name}Case {{
            {ctors}
            }}
        "}
    })
}

fn display_func_args_struct<'a>(func: FuncId, ctx: &'a RustGenCtx<'a>) -> impl 'a + Display {
    FmtFn(move |f| {
        let rel = FlatRel::Func(func);
        let func_camel = display_rel(rel, ctx).to_string().to_case(UpperCamel);
        let dom = flat_domain(func, ctx.signature());
        let args = dom
            .iter()
            .copied()
            .map(|typ| {
                FmtFn(move |f| {
                    let type_camel = display_type(typ, ctx).to_string().to_case(UpperCamel);
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

fn display_type_fields<'a>(typ: TypeId, ctx: &'a RustGenCtx<'a>) -> impl 'a + Display {
    FmtFn(move |f| {
        let typ = display_type(typ, ctx).to_string();
        let type_snake = typ.to_case(Snake);
        writedoc! {f, "
            {type_snake}_equalities: Unification<{typ}>,
            {type_snake}_weights: Vec<usize>,
            {type_snake}_uprooted: Vec<{typ}>,
        "}
    })
}

fn membership_self_type(rel: FlatRel) -> Option<TypeId> {
    match rel {
        FlatRel::ModelMember(typ) => Some(typ),
        FlatRel::Pred(_) | FlatRel::Func(_) => None,
    }
}

fn display_member_parent_checks<'a>(
    typ: TypeId,
    member: &'a str,
    expected: Vec<String>,
    ctx: &'a RustGenCtx<'a>,
) -> impl Display + 'a {
    FmtFn(move |f| {
        if ctx.signature().type_(typ).parents.is_empty() {
            return Ok(());
        }
        let relation = display_rel(FlatRel::ModelMember(typ), ctx);
        let parents = expected.iter().format(", ");
        writedoc! {f, "
            assert!(
                self.__contains_{relation}({parents}, {member}),
                \"invalid dependent argument: member element has a different parent model\"
            );
        "}
    })
}

fn display_nested_mor_app_source_parents<'a>(
    func: FuncId,
    types: MorphismMemberTypes,
    rel_args: &'a [ElVar],
    ctx: &'a RustGenCtx<'_>,
    index_selection: &'a IndexSelection,
) -> impl Display + 'a {
    FmtFn(move |f| {
        let parent_types = &ctx.signature().type_(types.member_type).parents;
        let outer_len = ctx.signature().func(func).parents.len();
        let arg_pos = outer_len + 1;
        let model_ids = ctx
            .signature()
            .ids_for_model_type(types.model_type(ctx.signature()))
            .expect("morphism type should have model ids");
        let dom_func = display_func(model_ids.dom, ctx);
        let mor_args = rel_args[..=outer_len].iter().format(", ").to_string();
        let arg = &rel_args[arg_pos];
        let member_rel = FlatInRel::Rel(FlatRel::ModelMember(types.member_type));
        let query = QuerySpec::member_parents(types.member_type, ctx.signature());
        let index = index_selection.current_query(&member_rel, query);
        let parent_rows = {
            let index_expr = display_index_expr(&member_rel, index, ctx);
            assert_eq!(index.order[0], parent_types.len());
            let unpack = index.order[1..]
                .iter()
                .map(|i| format!("parent{i}"))
                .format(", ");
            let parents = parent_types
                .iter()
                .enumerate()
                .map(|(i, &typ)| {
                    let type_name = display_type(typ, ctx).to_string().to_case(UpperCamel);
                    format!("{type_name}::from(parent{i})")
                })
                .format(", ");
            formatdoc! {"
                    {index_expr}.get({arg}.0).into_iter()
                        .flat_map(|rows| rows.iter())
                        .map(|[{unpack}]| ({parents}))
                "}
        };
        let source_pattern = (0..=outer_len)
            .map(|i| format!("parent{i}"))
            .chain(once("..".to_string()))
            .format(", ");
        let source_checks = parent_types[..=outer_len]
            .iter()
            .enumerate()
            .map(|(i, &typ)| {
                let type_name = display_type(typ, ctx).to_string().to_case(Snake);
                let expected = if i == outer_len {
                    "dependent_domain".to_string()
                } else {
                    rel_args[i].to_string()
                };
                format!("self.root_{type_name}(parent{i}) == self.root_{type_name}({expected})")
            })
            .format(" && ");

        writedoc! {f, "
            let dependent_domain = self.{dom_func}({mor_args})
                .expect(\"invalid dependent argument: morphism application requires a defined domain\");
            let mut dependent_source_parents = {parent_rows}
                .filter(|&({source_pattern})| {source_checks})
                .peekable();
            assert!(
                dependent_source_parents.peek().is_some(),
                \"invalid dependent argument: morphism application argument is not a member of the morphism domain\"
            );
        "}
    })
}

fn display_nested_mor_app_image_parents<'a>(
    func: FuncId,
    types: MorphismMemberTypes,
    rel_args: &'a [ElVar],
    ctx: &'a RustGenCtx<'_>,
) -> impl Display + 'a {
    FmtFn(move |f| {
        let parent_types = &ctx.signature().type_(types.member_type).parents;
        let outer_len = ctx.signature().func(func).parents.len();
        let model_ids = ctx
            .signature()
            .ids_for_model_type(types.model_type(ctx.signature()))
            .expect("morphism type should have model ids");
        let cod_func = display_func(model_ids.cod, ctx);
        let mor_args = rel_args[..=outer_len].iter().format(", ").to_string();
        let mut result_parents: Vec<String> = rel_args[..outer_len]
            .iter()
            .map(ToString::to_string)
            .collect();
        result_parents.push("dependent_codomain".to_string());
        let mut parent_images = String::new();
        for (i, &typ) in parent_types.iter().enumerate().skip(outer_len + 1) {
            let parent_func = ctx
                .signature()
                .mor_app_func(MorphismMemberTypes {
                    morphism_type: types.morphism_type,
                    member_type: typ,
                })
                .expect("nested parents should have morphism applications");
            let parent_func = display_func(parent_func, ctx);
            let parent_rel = display_rel(FlatRel::ModelMember(typ), ctx);
            result_parents.push(format!("image_parent{i}"));
            let parent_args = result_parents.iter().format(", ");
            parent_images.push_str(&formatdoc! {"
                let image_parent{i} = self.{parent_func}({mor_args}, parent{i})?;
                if !self.{parent_rel}({parent_args}) {{
                    return None;
                }}
            "});
        }
        let image_pattern = (0..parent_types.len())
            .map(|i| {
                if i <= outer_len {
                    "_".to_string()
                } else {
                    format!("parent{i}")
                }
            })
            .format(", ");
        let result_parents = result_parents.iter().format(", ");
        writedoc! {f, "
            let dependent_codomain = self.{cod_func}({mor_args})
                .expect(\"invalid dependent argument: morphism application requires a defined codomain\");
            let mut dependent_image_parents = dependent_source_parents.filter_map(|({image_pattern})| {{
                {parent_images}
                Some(({result_parents}))
            }});
        "}
    })
}

/// For `h.B.T(x)`, check that `x: b.T` with `b: dom(h).B`. Inserting
/// an image also requires that it belongs to `h.B(b).T` inside `cod(h)`.
fn display_nested_mor_app_type_checks<'a>(
    func: FuncId,
    types: MorphismMemberTypes,
    rel_args: &'a [ElVar],
    checked_len: usize,
    ctx: &'a RustGenCtx<'_>,
    index_selection: &'a IndexSelection,
) -> impl Display + 'a {
    FmtFn(move |f| {
        let arg_pos = ctx.signature().func(func).parents.len() + 1;
        let result_pos = arg_pos + 1;
        if checked_len <= arg_pos {
            return Ok(());
        }
        let source_parents =
            display_nested_mor_app_source_parents(func, types, rel_args, ctx, index_selection);
        writedoc! {f, "
            {{
                {source_parents}
        "}?;
        if checked_len > result_pos {
            let image_parents = display_nested_mor_app_image_parents(func, types, rel_args, ctx);
            let result_parents = (0..ctx.signature().type_(types.member_type).parents.len())
                .map(|i| format!("parent{i}"))
                .format(", ")
                .to_string();
            let member_rel = display_rel(FlatRel::ModelMember(types.member_type), ctx);
            let result = &rel_args[result_pos];
            writedoc! {f, "
                {image_parents}
                assert!(dependent_image_parents.any(|({result_parents})| {{
                    self.{member_rel}({result_parents}, {result})
                }}), \"invalid dependent argument: nested morphism application requires defined parent images and a result in the mapped parent models\");
            "}?;
        }
        writeln!(f, "}}")
    })
}

fn display_dependent_type_checks<'a>(
    rel: FlatRel,
    arity_types: &'a [TypeId],
    rel_args: &'a [ElVar],
    checked_len: usize,
    ctx: &'a RustGenCtx<'_>,
    index_selection: &'a IndexSelection,
) -> impl Display + 'a {
    FmtFn(move |f| {
        assert!(checked_len <= arity_types.len());
        assert_eq!(arity_types.len(), rel_args.len());

        let mor_app = match rel {
            FlatRel::Func(func) => ctx
                .signature()
                .types_for_mor_app_func(func)
                .map(|types| (func, types)),
            FlatRel::ModelMember(_) | FlatRel::Pred(_) => None,
        };
        if let Some((func, types)) = mor_app {
            let parent_model_type = types.model_type(ctx.signature());
            let member_type = types.member_type;
            if ctx.signature().type_(member_type).parents.last() != Some(&parent_model_type) {
                let checks = display_nested_mor_app_type_checks(
                    func,
                    types,
                    rel_args,
                    checked_len,
                    ctx,
                    index_selection,
                );
                return write!(f, "{checks}");
            }
            let flat_dom_len = flat_domain(func, ctx.signature()).len();
            assert!(flat_dom_len >= 2);
            let mor_pos = flat_dom_len - 2;
            let arg_pos = flat_dom_len - 1;
            let result_pos = flat_dom_len;

            let model_ids = ctx
                .signature()
                .ids_for_model_type(parent_model_type)
                .expect("member parent should be a model type");
            let dom_func = display_func(model_ids.dom, ctx);
            let cod_func = display_func(model_ids.cod, ctx);
            let member_rel = display_rel(FlatRel::ModelMember(member_type), ctx);
            let mor_func_args = rel_args[..=mor_pos].iter().format(", ").to_string();
            let outer_parents = rel_args[..mor_pos]
                .iter()
                .map(|v| format!("{v}"))
                .collect::<Vec<_>>()
                .join(", ");
            let member_prefix = if outer_parents.is_empty() {
                String::new()
            } else {
                format!("{outer_parents}, ")
            };

            if checked_len > arg_pos {
                let arg_expr = &rel_args[arg_pos];
                writedoc! {f, "
                    let dependent_parent_{arg_pos} = self.{dom_func}({mor_func_args})
                        .expect(\"invalid dependent argument: morphism application requires a defined domain\");
                    assert!(
                        self.{member_rel}({member_prefix}dependent_parent_{arg_pos}, {arg_expr}),
                        \"invalid dependent argument: morphism application argument is not a member of the morphism domain\"
                    );
                "}?;
            }

            if checked_len > result_pos {
                let result_expr = &rel_args[result_pos];
                writedoc! {f, "
                    let dependent_parent_{result_pos} = self.{cod_func}({mor_func_args})
                        .expect(\"invalid dependent argument: morphism application requires a defined codomain\");
                    assert!(
                        self.{member_rel}({member_prefix}dependent_parent_{result_pos}, {result_expr}),
                        \"invalid dependent argument: morphism application result is not a member of the morphism codomain\"
                    );
                "}?;
            }

            return Ok(());
        }

        for pos in 0..checked_len {
            let typ = arity_types[pos];
            let parents = &ctx.signature().type_(typ).parents;
            if parents.is_empty() {
                continue;
            }
            if membership_self_type(rel) == Some(typ) {
                continue;
            }
            if rel.parent_columns(ctx.signature()).is_none()
                && arity_types.get(..parents.len()) != Some(parents.as_slice())
            {
                continue;
            }

            let member = rel_args[pos].to_string();
            let columns = rel
                .parent_columns(ctx.signature())
                .map(|columns| columns[pos].clone())
                .unwrap_or_else(|| (0..parents.len()).collect());
            let parents = columns
                .iter()
                .map(|&column| rel_args[column].to_string())
                .collect();
            let checks = display_member_parent_checks(typ, &member, parents, ctx);
            write!(f, "{checks}")?;
        }

        Ok(())
    })
}

fn display_pub_predicate_holds_fn<'a>(
    rel: FlatRel,
    ctx: &'a RustGenCtx<'a>,
    index_selection: &'a IndexSelection,
) -> impl Display + 'a {
    FmtFn(move |f| {
        let is_membership = membership_self_type(rel).is_some();
        let relation_snake = display_rel(rel, ctx).to_string().to_case(Snake);
        let arity_types = rel.arity(ctx.signature());
        let arity_camel: Vec<String> = arity_types
            .iter()
            .map(|&typ| display_type(typ, ctx).to_string().to_case(UpperCamel))
            .collect();

        let rel_fn_args = arity_camel
            .iter()
            .enumerate()
            .format_with("", |(i, s), f| f(&format_args!(", mut arg{i}: {s}")))
            .to_string();

        let canonicalize = arity_camel
            .iter()
            .enumerate()
            .format_with("\n", |(i, s), f| {
                let type_snake = s.to_case(Snake);
                f(&format_args!("arg{i} = self.root_{type_snake}(arg{i});"))
            })
            .to_string();

        let rel_args: Vec<ElVar> = (0..arity_types.len())
            .map(|i| ElVar {
                name: format!("arg{i}").into(),
            })
            .collect();
        let dependent_checks = display_dependent_type_checks(
            rel,
            &arity_types,
            &rel_args,
            arity_types.len(),
            ctx,
            index_selection,
        );

        let rel_args_doc = (0..arity_types.len())
            .format_with(", ", |i, f| f(&format_args!("arg{i}")))
            .to_string();

        // A representative keeps an ownership row in its element index even
        // while the relation's parent columns await canonicalization.
        let membership_lookup = FmtFn(move |f| match rel {
            FlatRel::ModelMember(typ) => {
                let arity = rel.arity(ctx.signature());
                let member_pos = arity.len() - 1;
                let element_index = display_element_index_field_name(rel, typ, ctx);
                let checks = arity
                    .iter()
                    .enumerate()
                    .map(|(i, &typ)| {
                        let camel = display_type(typ, ctx).to_string().to_case(UpperCamel);
                        let snake = camel.to_case(Snake);
                        format!("self.root_{snake}({camel}(row[{i}])) == arg{i}")
                    })
                    .format(" && ");
                writedoc! {f, "
                    self.{element_index}.get(&arg{member_pos}.0)
                        .is_some_and(|rows| rows.iter().any(|row| {checks}))
                "}
            }
            FlatRel::Pred(_) | FlatRel::Func(_) => Ok(()),
        });

        let rel = FlatInRel::Rel(rel);
        let query = QuerySpec::one(rel.clone(), ctx.signature());
        let index = index_selection.current_query(&rel, query);
        let index_expr = display_index_expr(&rel, index, ctx);
        let row_args = index.order.iter().map(|i| format!("arg{i}.0")).format(", ");
        let contains = if is_membership {
            format!("self.__contains_{relation_snake}({rel_args_doc})")
        } else {
            format!("{index_expr}.contains([{row_args}])")
        };
        let membership_check = FmtFn(|f| {
            if !is_membership {
                return Ok(());
            }
            writedoc! {f, "
                fn __contains_{relation_snake}(&self{rel_fn_args}) -> bool {{
                    {canonicalize}
                    {membership_lookup}
                }}
            "}
        });

        writedoc! {f, "
            /// Returns `true` if `{relation_snake}({rel_args_doc})` holds.
            #[allow(dead_code)]
            pub fn {relation_snake}(&self{rel_fn_args}) -> bool {{
            {canonicalize}
            {dependent_checks}

            {contains}
            }}

            {membership_check}
        "}
    })
}

fn display_pub_function_eval_fn<'a>(
    func: FuncId,
    ctx: &'a RustGenCtx<'a>,
    index_selection: &'a IndexSelection,
) -> impl 'a + Display {
    FmtFn(move |f| {
        let rel = FlatRel::Func(func);

        let relation_snake = display_rel(rel, ctx).to_string().to_case(Snake);
        let relation_snake = relation_snake.as_str();

        let flat_dom = flat_domain(func, ctx.signature());
        let flat_dom_len = flat_dom.len();

        let cod = ctx.signature().func(func).codomain;
        let cod_camel = display_type(cod, ctx).to_string().to_case(UpperCamel);
        let cod_camel = &cod_camel;

        let params = flat_dom
            .iter()
            .copied()
            .enumerate()
            .map(|(i, typ)| {
                FmtFn(move |f| {
                    let type_camel = display_type(typ, ctx).to_string().to_case(UpperCamel);
                    write!(f, "mut arg{i}: {type_camel}, ")
                })
            })
            .format("");

        let canonicalize = flat_dom
            .iter()
            .copied()
            .enumerate()
            .map(|(i, typ)| {
                FmtFn(move |f| {
                    let type_snake = display_type(typ, ctx).to_string().to_case(Snake);
                    write!(f, "arg{i} = self.root_{type_snake}(arg{i});")
                })
            })
            .format("\n");

        let rel_args: Vec<ElVar> = (0..=flat_dom_len)
            .map(|i| ElVar {
                name: format!("arg{i}").into(),
            })
            .collect();
        let mut arity_types = flat_dom.clone();
        arity_types.push(cod);
        let dependent_checks = display_dependent_type_checks(
            rel,
            &arity_types,
            &rel_args,
            flat_dom_len,
            ctx,
            index_selection,
        );

        let doc_args = (0..flat_dom.len())
            .map(|i| FmtFn(move |f| write!(f, "arg{i}")))
            .format(", ")
            .to_string();

        let query_spec = QuerySpec::eval_func(func, ctx.signature());
        let flat_in_rel = FlatInRel::Rel(FlatRel::Func(func));

        let index = index_selection.current_query(&flat_in_rel, query_spec);
        let index_expr = display_index_expr(&flat_in_rel, index, ctx);
        assert_eq!(*index.order.last().unwrap(), flat_dom_len);
        let gets = index.order[..flat_dom_len]
            .iter()
            .map(|i| format!("let set = set.get(arg{i}.0)?;"))
            .format("\n");

        writedoc! {f, "
            /// Evaluates `{relation_snake}({doc_args})`.
            #[allow(dead_code)]
            pub fn {relation_snake}(&self, {params}) -> Option<{cod_camel}> {{
            {canonicalize}
            {dependent_checks}

            let set = {index_expr};
            {gets}
            let [result] = set.iter().next()?;
            Some(result.into())
            }}
        "}
    })
}

fn display_pub_iter_fn<'a>(
    rel: FlatRel,
    ctx: &'a RustGenCtx<'a>,
    index_selection: &'a IndexSelection,
) -> impl Display + 'a {
    FmtFn(move |f| {
        let is_function = matches!(rel, FlatRel::Func(_));
        let relation = display_rel(rel, ctx);
        let rel_snake = display_rel(rel, ctx).to_string().to_case(Snake);
        let rel_snake = rel_snake.as_str();
        let arity_tys = rel.arity(ctx.signature());
        let arity_tys = &arity_tys;
        let arity: Vec<String> = arity_tys
            .iter()
            .map(move |ty| display_type(*ty, ctx).to_string().to_case(UpperCamel))
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

        let flat_in_rel = FlatInRel::Rel(rel);
        let query_spec = QuerySpec::all();
        let index = index_selection.current_query(&flat_in_rel, query_spec);
        let index_expr = display_index_expr(&flat_in_rel, index, ctx);
        let row_unpack_args = index.order.iter().map(|i| format!("arg{i}")).format(", ");
        let row_args = arity_tys
            .iter()
            .enumerate()
            .map(|(i, &typ)| {
                let type_camel = display_type(typ, ctx).to_string().to_case(UpperCamel);
                format!("{type_camel}::from(arg{i})")
            })
            .format(", ");
        let row = if arity_tys.len() == 1 {
            row_args.to_string()
        } else {
            format!("({row_args})")
        };
        writedoc! {f, "
            {docstring}
            #[allow(dead_code)]
            pub fn iter_{rel_snake}(&self) -> impl '_ + Iterator<Item={rel_type}> {{
            {index_expr}.iter().map(|[{row_unpack_args}]| {row})
            }}
        "}
    })
}

fn display_insert_row_block<'a>(
    args: &'a [ElVar],
    rel: FlatRel,
    ctx: &'a RustGenCtx<'a>,
    index_selection: &'a IndexSelection,
) -> impl Display + 'a {
    FmtFn(move |f| {
        let flat = FlatInRel::Rel(rel);
        let index = index_selection.current_primary(&flat);
        let field = display_current_index_field_name(&flat, index, ctx);
        let args = index
            .order
            .iter()
            .map(|&i| &args[i])
            .format(", ")
            .to_string();
        if ctx.has_shared_indices(&flat) {
            writedoc! {f, "
                self.{field}_own.insert([{args}]);
                self.{field}_all.insert([{args}]);
            "}
        } else {
            writeln!(f, "self.{field}.insert([{args}]);")
        }
    })
}

fn display_pub_insert_relation<'a>(
    rel: FlatRel,
    ctx: &'a RustGenCtx<'a>,
    index_selection: &'a IndexSelection,
    is_function: bool,
) -> impl Display + 'a {
    FmtFn(move |f| {
        let rel_snake = display_rel(rel, ctx).to_string().to_case(Snake);
        let rel_snake = rel_snake.as_str();

        let arity_types = rel.arity(ctx.signature());
        let arity_camel: Vec<String> = arity_types
            .iter()
            .map(|&typ| display_type(typ, ctx).to_string().to_case(UpperCamel))
            .collect();

        let rel_args: Vec<ElVar> = (0..arity_types.len()).map(ElVar::from).collect();
        let rel_args = rel_args.as_slice();

        let rel_fn_args = rel_args
            .iter()
            .cloned()
            .zip(arity_camel.iter())
            .map(|(arg, typ_camel)| {
                FmtFn(move |f: &mut Formatter| -> Result { write!(f, "{arg}: {typ_camel}") })
            })
            .format(", ")
            .to_string();

        let canonicalize = rel_args
            .iter()
            .cloned()
            .zip(arity_types.iter())
            .map(|(arg, typ)| {
                FmtFn(move |f: &mut Formatter| -> Result {
                    let type_snake = display_type(*typ, ctx).to_string().to_case(Snake);
                    write!(f, "let {arg} = self.root_{type_snake}({arg});")
                })
            })
            .format("\n")
            .to_string();

        let dependent_checks = display_dependent_type_checks(
            rel,
            &arity_types,
            rel_args,
            arity_types.len(),
            ctx,
            index_selection,
        );

        let unwrap_args = rel_args
            .iter()
            .cloned()
            .map(|arg| {
                FmtFn(move |f: &mut Formatter| -> Result { write!(f, "let {arg}: u32 = {arg}.0;") })
            })
            .format("\n");

        let weight_static_name = display_weight_static_name(rel, ctx).to_string();
        let update_weights = rel_args
            .iter()
            .cloned()
            .zip(arity_types.iter())
            .enumerate()
            .map(move |(i, (arg, typ))| {
                let weight_static_name = weight_static_name.clone();
                FmtFn(move |f: &mut Formatter| -> Result {
                    let type_snake = display_type(*typ, ctx)
                        .to_string()
                        .to_case(Snake);
                    writedoc! {f, "
                        let weight{i}: &mut usize = &mut self.{type_snake}_weights[usize::try_from({arg}).unwrap()];
                        *weight{i} = weight{i}.saturating_add({weight_static_name});
                    "}
                })
            })
            .format("\n");

        let docstring = if is_function {
            let dom_len = arity_types.len() - 1;
            let func_args = rel_args[..dom_len]
                .iter()
                .cloned()
                .map(display_var)
                .format(", ");
            let result = rel_args
                .last()
                .expect("func can't have empty arity")
                .clone();
            formatdoc! {"
                /// Makes the equation `{rel_snake}({func_args}) = {result}` hold.
            "}
        } else {
            let rel_args = rel_args.iter().cloned().map(display_var).format(", ");
            formatdoc! {"
                /// Makes `{rel_snake}({rel_args})` hold.
            "}
        };

        let index_inserts = display_insert_row_block(rel_args, rel, ctx, index_selection);

        let flat_rel = FlatInRel::Rel(rel);
        let index_spec = index_selection.current_primary(&flat_rel);
        let flat_rel = &flat_rel;
        let contains_checks = {
            let index_expr = if ctx.has_shared_indices(flat_rel) {
                let own = display_own_index_field_name(flat_rel, index_spec, ctx);
                let all = display_all_index_field_name(flat_rel, index_spec, ctx);
                format!("(if retain_support {{ &self.{own} }} else {{ &self.{all} }})")
            } else {
                display_index_expr(flat_rel, index_spec, ctx).to_string()
            };
            let IndexSpec { order, age: _ } = index_spec;
            let row_args = order.iter().map(|i| rel_args[*i].clone()).format(", ");
            FmtFn(move |f| {
                writedoc! {f, "
                        if {index_expr}.contains([{row_args}]) {{
                        return;
                        }}
                    "}
            })
        };

        let mut type_positions: BTreeMap<TypeId, Vec<usize>> = BTreeMap::new();
        for (i, typ) in arity_types.iter().copied().enumerate() {
            type_positions.entry(typ).or_default().push(i);
        }

        let el_index_inserts = type_positions
            .iter()
            .map(move |(typ, positions)| {
                (0..positions.len())
                    .map(move |pos_index| {
                        FmtFn(move |f| {
                            let pos = positions[pos_index];
                            let pos_arg = rel_args[pos].clone();
                            let checks = (0..pos_index)
                                .map(move |prev_pos_index| {
                                    let prev_pos = positions[prev_pos_index];
                                    let prev_pos_arg = rel_args[prev_pos].clone();
                                    let pos_arg = pos_arg.clone();
                                    FmtFn(move |f| write!(f, "&& {pos_arg} != {prev_pos_arg}"))
                                })
                                .format(" ");

                            let pos_arg = rel_args[pos].clone();
                            let rel_args = rel_args.iter().format(", ");
                            let el_index_field =
                                display_element_index_field_name(rel, *typ, ctx).to_string();
                            writedoc! {f, "
                            if true {checks} {{
                            self.{el_index_field}.entry({pos_arg}).or_default().push([{rel_args}]);
                            }}
                        "}
                        })
                    })
                    .format("\n")
            })
            .format("\n");

        let invalidate = indices::invalidate(rel, index_selection, ctx);
        let internal_insert = ctx.internal_insert_name(rel);
        let supported_insert = ctx.supported_insert_name(rel);
        let args = rel_args.iter().format(", ").to_string();
        let parent_checks = FmtFn(|f| match rel {
            FlatRel::ModelMember(typ) => {
                let (member, parents) = rel_args.split_last().unwrap();
                let member = member.to_string();
                let parents = parents.iter().map(ToString::to_string).collect();
                let checks = display_member_parent_checks(typ, &member, parents, ctx);
                write!(f, "{checks}")
            }
            FlatRel::Pred(_) | FlatRel::Func(_) => Ok(()),
        });
        // Derived rows may precede their typing facts or endpoint equalities.
        writedoc! {f, "
            {docstring}
            #[allow(dead_code)]
            pub fn insert_{rel_snake}(&mut self, {rel_fn_args}) {{
                {canonicalize}
                {dependent_checks}
                {parent_checks}
                self.{internal_insert}({args});
            }}

            fn {internal_insert}(&mut self, {rel_fn_args}) {{
                self.{supported_insert}(false, {args});
            }}

            #[allow(unused_variables)]
            fn {supported_insert}(&mut self, retain_support: bool, {rel_fn_args}) {{
                {canonicalize}
                {unwrap_args}

                {contains_checks}

                self.__closed = false;
                {invalidate}
                {index_inserts}

                {el_index_inserts}

                {update_weights}
            }}
        "}
    })
}

fn display_new_element_fn_internal<'a>(
    typ: TypeId,
    ctx: &'a RustGenCtx<'a>,
    index_selection: &'a IndexSelection,
) -> impl 'a + Display {
    FmtFn(move |f| {
        let type_camel = display_type(typ, ctx).to_string().to_case(UpperCamel);
        let type_snake = type_camel.to_case(Snake);
        let type_snake = type_snake.as_str();

        let parent_types = ctx.signature().type_(typ).parents.clone();
        let parent_param = FmtFn(move |f| {
            parent_types
                .iter()
                .copied()
                .enumerate()
                .try_for_each(|(i, parent_type)| {
                    let type_camel = display_type(parent_type, ctx)
                        .to_string()
                        .to_case(UpperCamel);
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "parent{i}: {type_camel}")
                })
        });

        let insert_parent = FmtFn(move |f| {
            if ctx.signature().type_(typ).parents.is_empty() {
                return Ok(());
            }
            let insert = ctx.internal_insert_name(FlatRel::ModelMember(typ));
            let parent_args = (0..ctx.signature().type_(typ).parents.len())
                .map(|i| format!("parent{i}"))
                .collect::<Vec<_>>()
                .join(", ");
            writedoc! {f, "
                self.{insert}({parent_args}, el.into());
            "}
        });

        let parent_checks = FmtFn(move |f| {
            for (i, &parent) in ctx.signature().type_(typ).parents.iter().enumerate() {
                let parent_snake = display_type(parent, ctx).to_string().to_case(Snake);
                let member = format!("self.root_{parent_snake}(parent{i})");
                let expected = (0..i).map(|j| format!("parent{j}")).collect();
                let checks = display_member_parent_checks(parent, &member, expected, ctx);
                write!(f, "{checks}")?;
            }
            Ok(())
        });

        let type_set_rel = FlatInRel::TypeSet(typ);
        let index = index_selection.current_primary(&type_set_rel);
        let index_field = display_current_index_field_name(&type_set_rel, index, ctx);

        writedoc! {f, "
            /// Adjoins a new element of type [{type_camel}].
            #[allow(dead_code)]
            fn new_{type_snake}_internal(&mut self, {parent_param}) -> {type_camel} {{
                {parent_checks}
                let old_len = self.{type_snake}_equalities.len();
                self.{type_snake}_equalities.increase_size_to(old_len + 1);
                let el = u32::try_from(old_len).unwrap();

                self.{index_field}.insert([el]);
                self.__allocated = true;
                self.__closed = false;

                assert!(self.{type_snake}_weights.len() == old_len);
                self.{type_snake}_weights.push(0);

                {insert_parent}

                {type_camel}::from(el)
            }}
        "}
    })
}

fn display_new_element_fn<'a>(typ: TypeId, ctx: &'a RustGenCtx<'a>) -> impl 'a + Display {
    FmtFn(move |f| {
        let type_camel = display_type(typ, ctx).to_string().to_case(UpperCamel);
        let type_snake = type_camel.to_case(Snake);

        let parent_types = ctx.signature().type_(typ).parents.clone();
        let parent_param = FmtFn(move |f| {
            parent_types
                .iter()
                .copied()
                .enumerate()
                .try_for_each(|(i, parent_type)| {
                    let type_camel = display_type(parent_type, ctx)
                        .to_string()
                        .to_case(UpperCamel);
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "parent{i}: {type_camel}")
                })
        });

        let parent_arg = FmtFn(move |f| {
            let n = ctx.signature().type_(typ).parents.len();
            write!(
                f,
                "{}",
                (0..n)
                    .map(|i| format!("parent{i}"))
                    .collect::<Vec<_>>()
                    .join(", ")
            )
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
    enum_decl: EnumDeclId,
    ctx: &'a RustGenCtx<'a>,
) -> impl Display + 'a {
    FmtFn(move |f: &mut Formatter| -> Result {
        let enum_name = &ctx.ast().enum_decl(enum_decl).name;
        let enum_name_camel = enum_name.to_case(UpperCamel);
        let enum_name_camel = enum_name_camel.as_str();
        let enum_name_snake = enum_name.to_case(Snake);

        let ctors = ctx.ast().enum_decl(enum_decl).ctors.iter().copied();

        let match_branches = ctors
            .map(|ctor| {
                FmtFn(move |f: &mut Formatter| -> Result {
                    let ctor_name = &ctx.ast().ctor_decl(ctor).name;
                    let ctor_name_snake = ctor_name.to_case(Snake);
                    let ctor_name_camel = ctor_name.to_case(UpperCamel);

                    let ctor_func = ctx
                        .signature()
                        .func_for_ctor_decl(ctor)
                        .expect("constructor declaration should have a function id");
                    let ctor_arg_types = flat_domain(ctor_func, ctx.signature());
                    let ctor_vars = (0..ctor_arg_types.len()).map(ElVar::from).format(", ");
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

fn display_enum_cases_fn<'a>(enum_decl: EnumDeclId, ctx: &'a RustGenCtx<'a>) -> impl Display + 'a {
    FmtFn(move |f: &mut Formatter| -> Result {
        let enum_name = &ctx.ast().enum_decl(enum_decl).name;
        let enum_name_camel = enum_name.to_case(UpperCamel);
        let enum_name_camel = enum_name_camel.as_str();
        let enum_name_snake = enum_name.to_case(Snake);

        let ctors = ctx.ast().enum_decl(enum_decl).ctors.iter().copied();

        let ctor_value_iters = ctors
            .map(|ctor| {
                FmtFn(move |f: &mut Formatter| -> Result {
                    let ctor_name = &ctx.ast().ctor_decl(ctor).name;
                    let ctor_name_snake = ctor_name.to_case(Snake);
                    let ctor_name_camel = ctor_name.to_case(UpperCamel);

                    let ctor_func = ctx
                        .signature()
                        .func_for_ctor_decl(ctor)
                        .expect("constructor declaration should have a function id");
                    let arg_num = flat_domain(ctor_func, ctx.signature()).len();

                    let ctor_arg_vars = (0..arg_num).map(ElVar::from);
                    let result_var = ElVar::from(arg_num);
                    let tuple_vars = ctor_arg_vars.clone().chain(once(result_var.clone()));

                    let ctor_arg_vars = ctor_arg_vars.format(", ");
                    let tuple_vars = tuple_vars.map(display_var).format(", ");

                    // TODO: Use a lazy inverse index to avoid scanning constructor tuples.
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
    typ: TypeId,
    ctx: &'a RustGenCtx<'a>,
    index_selection: &'a IndexSelection,
    track_model_merges: bool,
) -> impl Display + 'a {
    FmtFn(move |f| {
        let type_camel = format!("{}", display_type(typ, ctx)).to_case(UpperCamel);
        let type_snake = type_camel.to_case(Snake);

        let type_set_rel = FlatInRel::TypeSet(typ);
        let index = index_selection.current_primary(&type_set_rel);
        let index_field = display_current_index_field_name(&type_set_rel, index, ctx);
        let parents = &ctx.signature().type_(typ).parents;
        let parent_params = parents
            .iter()
            .enumerate()
            .map(|(i, &parent)| {
                let parent_camel = display_type(parent, ctx).to_string().to_case(UpperCamel);
                format!("parent{i}: {parent_camel}, ")
            })
            .join("");
        let parent_args: Vec<_> = (0..parents.len()).map(|i| format!("parent{i}")).collect();
        let lhs_checks = display_member_parent_checks(typ, "lhs", parent_args.clone(), ctx);
        let rhs_checks = display_member_parent_checks(typ, "rhs", parent_args, ctx);
        let parent_doc = if parents.is_empty() {
            ""
        } else {
            "/// Both elements must belong to the supplied enclosing models, outermost first."
        };
        let invalidate_models = match ctx.signature().type_(typ).kind {
            TypeKind::Model if track_model_merges => format!("self.__model_owners_changed = true; self.__merged_{type_snake}.extend([lhs.0, rhs.0]);"),
            TypeKind::Model | TypeKind::Plain | TypeKind::Enum | TypeKind::Mor(_) => String::new(),
        };

        writedoc! {f, "
            /// Enforces the equality `lhs = rhs`.
            {parent_doc}
            #[allow(dead_code)]
            pub fn equate_{type_snake}(&mut self, {parent_params}lhs: {type_camel}, rhs: {type_camel}) {{
                let lhs = self.root_{type_snake}(lhs);
                let rhs = self.root_{type_snake}(rhs);
                {lhs_checks}
                {rhs_checks}
                self.__equate_{type_snake}(lhs, rhs);
            }}

            fn __equate_{type_snake}(&mut self, mut lhs: {type_camel}, mut rhs: {type_camel}) {{
                lhs = self.{type_snake}_equalities.root(lhs);
                rhs = self.{type_snake}_equalities.root(rhs);
                if lhs == rhs {{
                    return;
                }}
                self.__closed = false;
                {invalidate_models}
                let lhs_weight = self.{type_snake}_weights[lhs.0 as usize];
                let rhs_weight = self.{type_snake}_weights[rhs.0 as usize];
                let (root, child) =
                    if lhs_weight >= rhs_weight {{
                        (lhs, rhs)
                    }} else {{
                        (rhs, lhs)
                    }};

                self.{type_snake}_equalities.union_roots_into(child, root);
                self.{index_field}.remove([child.0]);
                self.{type_snake}_uprooted.push(child);
            }}
        "}
    })
}

fn display_root_fn<'a>(typ: TypeId, ctx: &'a RustGenCtx<'a>) -> impl 'a + Display {
    FmtFn(move |f| {
        let type_name = display_type(typ, ctx).to_string().to_case(UpperCamel);
        let type_snake = type_name.to_case(Snake);
        writedoc! {f, "
            /// Returns the canonical representative of the equivalence class of `el`.
            #[allow(dead_code)]
            pub fn root_{type_snake}(&self, el: {type_name}) -> {type_name} {{
                if el.0 as usize >= self.{type_snake}_equalities.len() {{
                    el
                }} else {{
                    self.{type_snake}_equalities.root_const(el)
                }}
            }}
        "}
    })
}

fn display_are_equal_fn<'a>(typ: TypeId, ctx: &'a RustGenCtx<'a>) -> impl 'a + Display {
    FmtFn(move |f| {
        let type_name = display_type(typ, ctx).to_string().to_case(UpperCamel);
        let type_snake = type_name.to_case(Snake);
        writedoc! {f, "
            /// Returns `true` if `lhs` and `rhs` are in the same equivalence class.
            #[allow(dead_code)]
            pub fn are_equal_{type_snake}(&self, lhs: {type_name}, rhs: {type_name}) -> bool {{
                self.root_{type_snake}(lhs) == self.root_{type_snake}(rhs)
            }}
        "}
    })
}

fn display_iter_type_fn<'a>(
    typ: TypeId,
    ctx: &'a RustGenCtx<'a>,
    index_selection: &'a IndexSelection,
) -> impl 'a + Display {
    FmtFn(move |f| {
        let type_snake = display_type(typ, ctx).to_string().to_case(Snake);
        let type_camel = type_snake.to_case(UpperCamel);
        let rel = FlatInRel::TypeSet(typ);
        let query = QuerySpec::all();
        let index = index_selection.current_query(&rel, query);
        let index_field = display_current_index_field_name(&rel, index, ctx);

        writedoc! {f, "
            /// Returns an iterator over elements of type `{type_camel}`.
            /// The iterator yields canonical representatives only.
            #[allow(dead_code)]
            pub fn iter_{type_snake}(&self) -> impl '_ + Iterator<Item={type_camel}> {{
            self.{index_field}.iter()
            .map(|[el]| {type_camel}::from(el))
            }}
        "}
    })
}

fn display_remove_from_index_expr<'a>(
    rel: FlatInRel,
    index: IndexSpec,
    row_args: &'a [ElVar],
    ctx: &'a RustGenCtx<'a>,
) -> impl 'a + Display {
    FmtFn(move |f| {
        let permuted_row_args = index
            .order
            .iter()
            .map(|i| row_args[*i].clone())
            .format(", ");

        let field_name = display_own_index_field_name(&rel, &index, ctx);

        write!(f, "self.{field_name}.remove([{permuted_row_args}])")
    })
}

fn display_canonicalize_rel_block<'a>(
    rel: FlatRel,
    ctx: &'a RustGenCtx<'a>,
    index_selection: &'a IndexSelection,
) -> impl 'a + Display {
    FmtFn(move |f| {
        let supported_insert = ctx.supported_insert_name(rel);

        let arity = rel.arity(ctx.signature());
        let arity_len = arity.len();
        let types: BTreeSet<_> = arity.iter().copied().collect();
        let row_args: Vec<ElVar> = (0..arity.len()).map(ElVar::from).collect();
        let row_args = row_args.as_slice();

        let fill_non_canonical_rows_vec = types
            .into_iter()
            .map(|typ| {
                FmtFn(move |f| {
                    let type_snake = display_type(typ, ctx).to_string().to_case(Snake);
                    let element_index_field = display_element_index_field_name(rel, typ, ctx);

                    writedoc! {f, "
                        for el in self.{type_snake}_uprooted.iter().copied() {{
                        if let Some(rows) = self.{element_index_field}.remove(&el.0) {{
                        non_canonical_rows.push(rows);
                        }}
                        }}
                    "}
                })
            })
            .format("\n");

        let reduce_weights =
            arity
                .iter()
                .copied()
                .enumerate()
                .map(move |(i, type_i)| {
                    FmtFn(move |f| {
                        let type_i_snake = display_type(type_i, ctx)
                            .to_string()
                            .to_case(Snake);
                        let weight_static_name = display_weight_static_name(rel, ctx);
                        let el = row_args[i].clone();
                        writedoc! {f, "
                            let weight{i}: &mut usize = &mut self.{type_i_snake}_weights[usize::try_from({el}).unwrap()];
                            *weight{i} = weight{i}.saturating_sub({weight_static_name});
                        "}
                    })
                })
                .format("\n");

        let flat_rel = FlatInRel::Rel(rel);
        let primary = index_selection.current_primary(&flat_rel).clone();
        let invalidate = indices::invalidate(rel, index_selection, ctx);
        let remove_from_primary = display_remove_from_index_expr(flat_rel, primary, row_args, ctx);

        // An inherited canonical copy must not suppress the replacement of
        // an owned alias: it may depend on that alias through a cycle.
        let insert_row_args = row_args
            .iter()
            .zip(arity.iter())
            .map(|(arg, typ)| {
                FmtFn(move |f| {
                    let type_snake = display_type(*typ, ctx).to_string().to_case(UpperCamel);
                    write!(f, "{type_snake}({arg})")
                })
            })
            .format(",");

        let row_args = row_args.iter().format(", ");

        writedoc! {f, "
            #[allow(unused_mut)]
            let mut non_canonical_rows: Vec<Vec<[u32; {arity_len}]>> = Vec::new();
            {fill_non_canonical_rows_vec}

            if !non_canonical_rows.is_empty() {{
                {invalidate}
            }}
            for [{row_args}] in non_canonical_rows.into_iter().flatten() {{
            let was_in_indices = {remove_from_primary};

            if !was_in_indices {{
            continue;
            }}

            {reduce_weights}

            self.{supported_insert}(true, {insert_row_args});
            }}
        "}
    })
}

fn display_canonicalize_fn<'a>(
    ctx: &'a RustGenCtx<'a>,
    index_selection: &'a IndexSelection,
) -> impl 'a + Display {
    FmtFn(move |f| {
        let rel_blocks = iter_flat_rels(ctx.signature())
            .filter(|rel| rel.is_model_membership_relation())
            .chain(
                iter_flat_rels(ctx.signature()).filter(|rel| !rel.is_model_membership_relation()),
            )
            .map(|rel| {
                FmtFn(move |f| {
                    let block = display_canonicalize_rel_block(rel, ctx, index_selection);
                    let rel = display_rel(rel, ctx);
                    writedoc! {f, "
                        // Canonicalize {rel}.
                        {block}
                    "}
                })
            })
            .format("\n");

        let clear_uprooted_vecs = ctx
            .signature()
            .iter_types()
            .map(|typ| {
                FmtFn(move |f: &mut Formatter| -> Result {
                    let type_snake = format!("{}", display_type(typ, ctx)).to_case(Snake);
                    write!(f, "self.{type_snake}_uprooted.clear();")
                })
            })
            .format("\n");

        let propagate = match ctx.model_mode() {
            ModelMode::Native => "self.recompute_model_indices();",
            ModelMode::Desugared => "",
        };
        let prune_transport = transport::prune(ctx, index_selection);
        let canonicalize_inherited = FmtFn(|f| {
            let shared: Vec<_> = index_selection
                .current_indices()
                .filter(|(rel, index)| {
                    ctx.has_shared_indices(rel) && index_selection.is_primary(rel, index)
                })
                .collect();
            if shared.is_empty() {
                return Ok(());
            }
            let types: BTreeSet<_> = shared
                .iter()
                .flat_map(|(rel, _)| rel.arity(ctx.signature()))
                .collect();
            for typ in types {
                let name = display_type(typ, ctx).to_string().to_case(Snake);
                writedoc! {f, "
                    let {name}_replacements: BTreeMap<u32, u32> = self.{name}_uprooted
                        .iter().map(|&el| (el.0, self.root_{name}(el).0)).collect();
                "}?;
            }
            for (rel, index) in shared {
                let field = display_current_index_field_name(rel, index, ctx);
                let arity = rel.arity(ctx.signature());
                let replacements = index
                    .order
                    .iter()
                    .map(|&column| {
                        let name = display_type(arity[column], ctx).to_string().to_case(Snake);
                        format!("&{name}_replacements")
                    })
                    .join(", ");
                let relation = match rel {
                    FlatInRel::Rel(relation) => *relation,
                    FlatInRel::RelWithDiagonals { .. }
                    | FlatInRel::TypeSet(_)
                    | FlatInRel::Equality(_) => {
                        unreachable!("only relations have shared primary indices")
                    }
                };
                let invalidate = indices::invalidate(relation, index_selection, ctx);
                writedoc! {f, "
                    if let Some(canonical) = self.{field}_all.replace_keys([{replacements}]) {{
                        self.{field}_all = canonical;
                        {invalidate}
                    }}
                "}?;
            }
            Ok(())
        });
        writedoc! {f, "
            /// Rewrites facts using the current equality representatives without running rules.
            /// Consumer checkpoints retain pending matches after equality replacement.
            /// Element handles remain valid, and repeated calls preserve pending work.
            /// Refreshes query indices, including shared views in native models.
            #[allow(dead_code)]
            pub fn canonicalize(&mut self) {{
                self.__canonicalize_relations();
                {propagate}
            }}

            fn __canonicalize_relations(&mut self) {{
                {rel_blocks}

                {canonicalize_inherited}
                {prune_transport}
                {clear_uprooted_vecs}
            }}
        "}
    })
}

fn display_out_set_field_name<'a>(
    rel: &'a FlatOutRel,
    ctx: &'a RustGenCtx<'a>,
) -> impl 'a + Display {
    FmtFn(move |f| match rel {
        FlatOutRel::Rel(rel) => {
            let rel_snake = display_rel(*rel, ctx).to_string().to_case(Snake);
            write!(f, "new_{rel_snake}")
        }
        FlatOutRel::Equality(typ) => {
            let type_snake = display_type(*typ, ctx).to_string().to_case(Snake);
            write!(f, "new_{type_snake}_equalities")
        }
        FlatOutRel::FuncDomain(func) => {
            let rel_snake = display_rel(FlatRel::Func(*func), ctx)
                .to_string()
                .to_case(Snake);
            write!(f, "new_{rel_snake}_def")
        }
    })
}

fn display_out_set_type<'a>(rel: &'a FlatOutRel, ctx: &'a RustGenCtx<'a>) -> impl 'a + Display {
    FmtFn(move |f| {
        let arity_len = rel.arity(ctx.signature()).len();
        write!(f, "Vec<[u32; {arity_len}]>")
    })
}

fn display_model_delta_struct<'a>(
    outputs: &'a BTreeSet<FlatOutRel>,
    ctx: &'a RustGenCtx<'a>,
) -> impl Display + 'a {
    FmtFn(move |f| {
        let fields = outputs
            .iter()
            .map(|rel| {
                let name = display_out_set_field_name(rel, ctx);
                let typ = display_out_set_type(rel, ctx);
                format!("{name}: {typ},")
            })
            .format("\n");
        writedoc! {f, "
            #[derive(Debug, Clone)]
            struct ModelDelta {{ {fields} }}
        "}
    })
}

fn display_model_delta_impl<'a>(
    outputs: &'a BTreeSet<FlatOutRel>,
    ctx: &'a RustGenCtx<'a>,
) -> impl Display + 'a {
    FmtFn(move |f| {
        writedoc! {f, "
            impl ModelDelta {{
        "}
        .unwrap();

        let new_fn = display_model_delta_new_fn(outputs, ctx);
        write!(f, "{}", new_fn).unwrap();

        let apply_def_fn = display_model_delta_apply_def_fn(outputs, ctx);
        write!(f, "{}", apply_def_fn).unwrap();

        writedoc! {f, "
            }}
        "}
    })
}

fn display_model_delta_new_fn<'a>(
    outputs: &'a BTreeSet<FlatOutRel>,
    ctx: &'a RustGenCtx<'a>,
) -> impl Display + 'a {
    FmtFn(move |f| {
        let fields = outputs
            .iter()
            .map(|rel| {
                let name = display_out_set_field_name(rel, ctx);
                format!("{name}: Vec::new(),")
            })
            .format("\n");
        writedoc! {f, "
            fn new() -> ModelDelta {{ ModelDelta {{ {fields} }} }}
        "}
    })
}

fn display_model_delta_apply_def_fn<'a>(
    outputs: &'a BTreeSet<FlatOutRel>,
    ctx: &'a RustGenCtx<'a>,
) -> impl Display + 'a {
    FmtFn(move |f| {
        let func_defs = outputs
            .iter()
            .filter_map(|output| match output {
                FlatOutRel::FuncDomain(func) => Some(*func),
                FlatOutRel::Rel(_) | FlatOutRel::Equality(_) => None,
            })
            .map(|func| {
                let func_name = display_func(func, ctx).to_string();
                let func_snake = func_name.to_case(Snake);

                let domain = flat_domain(func, ctx.signature());

                let args_destructure = (0..domain.len())
                    .map(ElVar::from)
                    .map(display_var)
                    .format(", ");
                let define_args = (0..domain.len())
                    .map(|i| {
                        FmtFn(move |f| {
                            let var = ElVar::from(i);
                            write!(f, "{var}.into()")
                        })
                    })
                    .format(", ");

                FmtFn(move |f: &mut Formatter| -> Result {
                    writedoc! {f, "
                            for [{args_destructure}] in self.new_{func_snake}_def.drain(..) {{
                                model.define_{func_snake}({define_args});
                            }}
                        "}
                })
            })
            .format("\n");

        writedoc! {f, "
            #[allow(unused_variables)]
            fn apply_func_defs(&mut self, model: &mut Model) {{
                {func_defs}
            }}
        "}
    })
}

impl Display for ElVar {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        let ElVar { name } = self;
        write!(f, "{}", name)
    }
}

// TODO: Remove this legacy function.
fn display_var(var: ElVar) -> impl Display {
    var
}

#[derive(Copy, Clone)]
enum MorphismIndexColumnKind {
    OuterParent(usize),
    Parent,
    Member(TypeId),
    Copy,
}

impl MorphismIndexColumnKind {
    fn needs_mapping(self) -> bool {
        match self {
            MorphismIndexColumnKind::OuterParent(_)
            | MorphismIndexColumnKind::Parent
            | MorphismIndexColumnKind::Member(_) => true,
            MorphismIndexColumnKind::Copy => false,
        }
    }
}

fn parent_prefix_len(rel: &FlatInRel, ctx: &RustGenCtx<'_>) -> usize {
    match rel {
        FlatInRel::Rel(rel) | FlatInRel::RelWithDiagonals { rel, .. } => match rel {
            FlatRel::Pred(pred) => ctx.signature().pred(*pred).parents.len(),
            FlatRel::Func(func) => ctx.signature().func(*func).parents.len(),
            FlatRel::ModelMember(typ) => ctx.signature().type_(*typ).parents.len(),
        },
        FlatInRel::TypeSet(_) | FlatInRel::Equality(_) => 0,
    }
}

fn morphism_index_column_kind(
    rel: &FlatInRel,
    parent_model_type: TypeId,
    column_index: usize,
    prefix_len: usize,
    typ: TypeId,
    ctx: &RustGenCtx<'_>,
) -> MorphismIndexColumnKind {
    if column_index < ctx.signature().type_(parent_model_type).parents.len() {
        return MorphismIndexColumnKind::OuterParent(column_index);
    }

    // Only the flattened enclosing-model prefix is rewritten from dom to
    // cod. An argument that happens to have the same type as a parent
    // model (e.g. tagged_by(Set, S)) must be copied.
    if column_index < prefix_len && typ == parent_model_type {
        return MorphismIndexColumnKind::Parent;
    }

    let maps = match rel {
        FlatInRel::Rel(rel) => {
            rel.column_maps_under(ctx.signature(), column_index, parent_model_type)
        }
        FlatInRel::RelWithDiagonals { .. } | FlatInRel::TypeSet(_) | FlatInRel::Equality(_) => {
            unreachable!("morphism indices use full member relations")
        }
    };
    if maps {
        return MorphismIndexColumnKind::Member(typ);
    }

    MorphismIndexColumnKind::Copy
}

fn display_prefix_tree_type(arity_len: usize) -> impl Display {
    FmtFn(move |f| write!(f, "PrefixTree{arity_len}"))
}

fn display_parent_then_morph_gets(base: String, parent_len: usize) -> String {
    let mut expr = base;
    let mut dim = parent_len + 3;
    for i in 0..parent_len {
        dim -= 1;
        expr = format!("{expr}.get(parents[{i}]).unwrap_or_else(|| PrefixTree{dim}::empty())");
    }
    format!("{expr}.get(*morph).unwrap_or_else(|| PrefixTree2::empty())")
}

fn display_tree_prefix_slice(field: &str, parent_len: usize, leaf_dim: usize) -> String {
    let mut expr = format!("self.{field}()");
    for i in 0..parent_len {
        if i == 0 {
            expr = format!("{expr}.get(parents[{i}])");
        } else {
            expr = format!("{expr}.and_then(|t| t.get(parents[{i}]))");
        }
    }
    format!("{expr}.unwrap_or_else(|| PrefixTree{leaf_dim}::empty())")
}

fn display_mor_app_map_expr<'a>(
    parent_model_type: TypeId,
    typ: TypeId,
    ctx: &'a RustGenCtx<'a>,
    index_selection: &'a IndexSelection,
    prepared: bool,
) -> impl Display + 'a {
    FmtFn(move |f| {
        let morphism_type = ctx
            .signature()
            .ids_for_model_type(parent_model_type)
            .expect("morphism application requires a parent model type")
            .mor;
        let mor_app_func = ctx
            .signature()
            .mor_app_func(MorphismMemberTypes {
                morphism_type,
                member_type: typ,
            })
            .expect("mor_app_func should be defined for member types");
        let mor_app_rel = FlatInRel::Rel(FlatRel::Func(mor_app_func));
        let parent_len = ctx.signature().func(mor_app_func).parents.len();
        let order: Vec<usize> = (0..parent_len + 3).collect();

        let mor_app_indices = index_selection
            .indices
            .get(&mor_app_rel)
            .expect("mor_app rel should have indices");
        let index = index_with_order(mor_app_indices, order.as_slice());
        let name = indices::read_method(&mor_app_rel, index, index_selection, ctx, prepared);
        let gets = display_parent_then_morph_gets(format!("self.{name}()"), parent_len);
        write!(f, "{gets}.clone()")
    })
}

fn display_morphism_index_prefix_walk<'a>(
    columns: &'a [MorphismIndexColumnKind],
    arity_len: usize,
    source_tree: String,
    source_tree_is_ref: bool,
) -> impl Display + 'a {
    FmtFn(move |f| {
        let body = display_morphism_index_prefix_walk_from(
            columns,
            0,
            arity_len,
            source_tree.clone(),
            source_tree_is_ref,
            Vec::new(),
            None,
        );
        write!(f, "{body}")
    })
}

fn display_morphism_index_prefix_walk_from(
    columns: &[MorphismIndexColumnKind],
    pos: usize,
    current_dim: usize,
    source_tree: String,
    source_tree_is_ref: bool,
    target_prefix: Vec<String>,
    driving_map: Option<usize>,
) -> String {
    if pos == columns.len() {
        let target_prefix = target_prefix.iter().format(", ");
        let suffix = if source_tree_is_ref {
            format!("(*{source_tree}).clone()")
        } else {
            format!("{source_tree}.clone()")
        };
        return format!("propagated.push(([{target_prefix}], {suffix}));");
    }

    let el = format!("el{pos}");
    let subtree = format!("{source_tree}_{pos}");
    let subtree_is_ref = current_dim > 1;

    match columns[pos] {
        MorphismIndexColumnKind::OuterParent(_) | MorphismIndexColumnKind::Parent => {
            let (source, target) = match columns[pos] {
                MorphismIndexColumnKind::OuterParent(i) => {
                    let parent = format!("parents[{i}]");
                    (parent.clone(), parent)
                }
                MorphismIndexColumnKind::Parent => ("*dom".to_string(), "*cod".to_string()),
                MorphismIndexColumnKind::Member(_) | MorphismIndexColumnKind::Copy => {
                    unreachable!("only parent columns restrict the source model")
                }
            };
            let mut target_prefix = target_prefix;
            target_prefix.push(target);
            let body = display_morphism_index_prefix_walk_from(
                columns,
                pos + 1,
                current_dim - 1,
                subtree.clone(),
                true,
                target_prefix,
                driving_map,
            );
            formatdoc! {"
                if let Some({subtree}) = {source_tree}.get({source}) {{
                    {body}
                }}
            "}
        }
        MorphismIndexColumnKind::Member(_) => {
            let mut target_prefix = target_prefix;
            target_prefix.push(format!("mapped_{el}"));
            let body = display_morphism_index_prefix_walk_from(
                columns,
                pos + 1,
                current_dim - 1,
                subtree.clone(),
                subtree_is_ref || driving_map == Some(pos),
                target_prefix,
                driving_map,
            );
            if driving_map == Some(pos) {
                return formatdoc! {"
                    for ({el}, images) in map_{el}.iter_restrictions() {{
                        let Some({subtree}) = {source_tree}.get({el}) else {{
                            continue;
                        }};
                        for [mapped_{el}] in images.iter() {{
                            {body}
                        }}
                    }}
                "};
            }
            formatdoc! {"
                for ({el}, {subtree}) in {source_tree}.iter_restrictions() {{
                    let Some(images) = map_{el}.get({el}) else {{
                        continue;
                    }};
                    for [mapped_{el}] in images.iter() {{
                        {body}
                    }}
                }}
            "}
        }
        MorphismIndexColumnKind::Copy => {
            let mut target_prefix = target_prefix;
            target_prefix.push(el.clone());
            let body = display_morphism_index_prefix_walk_from(
                columns,
                pos + 1,
                current_dim - 1,
                subtree.clone(),
                subtree_is_ref,
                target_prefix,
                driving_map,
            );
            formatdoc! {"
                for ({el}, {subtree}) in {source_tree}.iter_restrictions() {{
                    {body}
                }}
            "}
        }
    }
}

fn display_apply_morphism_index_propagated<'a>(
    index_field_name: &'a str,
    arity_len: usize,
    prefix_len: usize,
    suffix_len: usize,
) -> impl Display + 'a {
    FmtFn(move |f| {
        if suffix_len == 0 {
            assert_eq!(prefix_len, arity_len);
            return writedoc! {f, "
                for (row, mapped_dom_set) in propagated {{
                    if mapped_dom_set.is_empty() {{ continue; }}
                    if !retain_own && {index_field_name}_own.contains(row) {{
                        {index_field_name}_own.remove(row);
                    }}
                    if {index_field_name}_all.contains(row) {{ continue; }}
                    let inserted = {index_field_name}_all.insert(row);
                    changed |= retain_own && inserted;
                    relation_changed |= inserted;
                }}
            "};
        }
        let prefix_vars = (0..prefix_len)
            .map(|i| FmtFn(move |f| write!(f, "el{i}")))
            .format(", ");
        let wrap_suffix = (1..prefix_len)
            .rev()
            .map(|i| {
                let tree_type = display_prefix_tree_type(arity_len - i);
                FmtFn(move |f| {
                    writedoc! {f, "
                        let mapped_dom_set = {{
                            let mut tree = {tree_type}::new();
                            tree.insert_restriction(el{i}, mapped_dom_set);
                            tree
                        }};
                    "}
                })
            })
            .format("\n");

        let suffix_type = display_prefix_tree_type(suffix_len);
        let target_slice = (0..prefix_len)
            .fold(format!("Some(&{index_field_name}_all)"), |tree, i| {
                format!("{tree}.and_then(|tree| tree.get(el{i}))")
            });
        let own_slice = (0..prefix_len)
            .fold(format!("Some(&*{index_field_name}_own)"), |tree, i| {
                format!("{tree}.and_then(|tree| tree.get(el{i}))")
            });
        writedoc! {f, "
            for ([{prefix_vars}], mapped_dom_set) in propagated {{
                let mapped_dom_set: {suffix_type} = mapped_dom_set;
                if (retain_own || {own_slice}.is_none())
                    && {target_slice}.is_some_and(|existing| mapped_dom_set.is_subset(existing))
                {{
                    continue;
                }}
                {wrap_suffix}
                if !retain_own {{
                    {index_field_name}_own.remove_restriction(el0, &mapped_dom_set);
                }}
                if {index_field_name}_all.get(el0).is_some_and(|existing| mapped_dom_set.is_subset(existing)) {{
                    continue;
                }}
                changed |= retain_own && !mapped_dom_set.is_empty();
                relation_changed |= !mapped_dom_set.is_empty();
                {index_field_name}_all.insert_restriction(el0, mapped_dom_set);
            }}
        "}
    })
}

fn index_with_order<'a>(indices: &'a [IndexSpec], order: &'a [usize]) -> &'a IndexSpec {
    indices
        .iter()
        .find(|index| index.order.as_ref() == order)
        .unwrap_or_else(|| panic!("missing index with order {order:?}"))
}

fn display_morphism_components<'a>(
    typ: TypeId,
    ctx: &'a RustGenCtx<'a>,
    index_selection: &'a IndexSelection,
    prepared: bool,
) -> impl Display + 'a {
    FmtFn(move |f| {
        let type_snake = display_type(typ, ctx).to_string().to_case(Snake);
        let ids = ctx
            .signature()
            .ids_for_model_type(typ)
            .expect("typ is model type");
        let parent_len = ctx.signature().type_(typ).parents.len();

        let dom_rel = FlatInRel::Rel(FlatRel::Func(ids.dom));
        let cod_rel = FlatInRel::Rel(FlatRel::Func(ids.cod));
        let obj_rel = if parent_len == 0 {
            FlatInRel::TypeSet(typ)
        } else {
            FlatInRel::Rel(FlatRel::ModelMember(typ))
        };

        let dom_indices = index_selection
            .indices
            .get(&dom_rel)
            .expect("dom rel should have indices");
        let cod_indices = index_selection
            .indices
            .get(&cod_rel)
            .expect("cod rel should have indices");
        let obj_indices = index_selection
            .indices
            .get(&obj_rel)
            .expect("object rel should have indices");

        let mut dom_order: Vec<usize> = (0..parent_len).collect();
        dom_order.push(parent_len + 1);
        dom_order.push(parent_len);
        let cod_order: Vec<usize> = (0..parent_len + 2).collect();
        let obj_order: Vec<usize> = (0..parent_len + 1).collect();

        let dom = indices::read_method(
            &dom_rel,
            index_with_order(dom_indices, &dom_order),
            index_selection,
            ctx,
            prepared,
        );
        let cod = indices::read_method(
            &cod_rel,
            index_with_order(cod_indices, &cod_order),
            index_selection,
            ctx,
            prepared,
        );
        let obj = indices::read_method(
            &obj_rel,
            index_with_order(obj_indices, &obj_order),
            index_selection,
            ctx,
            prepared,
        );

        if parent_len == 0 {
            writedoc! {f, "
                let components = self.__morphism_graph_{type_snake}.components(
                    parents, self.{dom}(), self.{cod}(), self.{obj}(),
                );
            "}
        } else {
            let dom = display_tree_prefix_slice(&dom, parent_len, 2);
            let cod = display_tree_prefix_slice(&cod, parent_len, 2);
            let obj = display_tree_prefix_slice(&obj, parent_len, 1);
            writedoc! {f, "
                let components = self.__morphism_graph_{type_snake}.components(
                    parents, {dom}, {cod}, {obj},
                );
            "}
        }
    })
}

fn display_remap_parented_index<'a>(
    flat_in_rel: FlatInRel,
    index_spec: IndexSpec,
    parent_model_type: TypeId,
    ctx: &'a RustGenCtx<'a>,
    index_selection: &'a IndexSelection,
    prepare_maps: Option<&'a BTreeSet<(FlatInRel, IndexSpec)>>,
) -> impl Display + 'a {
    FmtFn(move |f| {
        let flat_arity = flat_in_rel.arity(ctx.signature());
        let preparation = FmtFn(|f| {
            for (rel, index) in prepare_maps.into_iter().flatten() {
                write!(f, "{}", indices::prepare(rel, index, index_selection, ctx))?;
            }
            Ok(())
        });
        let arity: Vec<_> = index_spec
            .order
            .iter()
            .copied()
            .map(|i| flat_arity[i])
            .collect();
        let arity = arity.as_slice();

        let index_field_name =
            display_current_index_field_name(&flat_in_rel, &index_spec, ctx).to_string();
        let index_field_name = index_field_name.as_str();
        let parent_cols = parent_prefix_len(&flat_in_rel, ctx);
        let columns: Vec<_> = index_spec
            .order
            .iter()
            .copied()
            .map(|column_index| {
                morphism_index_column_kind(
                    &flat_in_rel,
                    parent_model_type,
                    column_index,
                    parent_cols,
                    flat_arity[column_index],
                    ctx,
                )
            })
            .collect();
        let prefix_len = columns
            .iter()
            .rposition(|column| column.needs_mapping())
            .expect("index over a parented relation should contain the parent")
            + 1;
        let suffix_len = arity.len() - prefix_len;
        let prefix_columns = &columns[..prefix_len];

        let member_maps = prefix_columns
            .iter()
            .copied()
            .enumerate()
            .filter_map(|(i, column)| match column {
                MorphismIndexColumnKind::Member(typ) => Some(FmtFn(move |f| {
                    let map = display_mor_app_map_expr(
                        parent_model_type,
                        typ,
                        ctx,
                        index_selection,
                        prepare_maps.is_some(),
                    );
                    writedoc! {f, "
                        let map_el{i} = {map};
                    "}
                })),
                MorphismIndexColumnKind::OuterParent(_)
                | MorphismIndexColumnKind::Parent
                | MorphismIndexColumnKind::Copy => None,
            })
            .format("\n");

        let owner_len = ctx.signature().type_(parent_model_type).parents.len() + 1;
        let checkpointed = index_spec
            .order
            .iter()
            .take(owner_len)
            .copied()
            .eq(0..owner_len);
        let target_prefix: Vec<_> = (0..owner_len - 1)
            .map(|i| format!("parents[{i}]"))
            .chain(once("*cod".to_string()))
            .collect();
        let collect_propagated = if checkpointed {
            display_morphism_index_prefix_walk_from(
                prefix_columns,
                owner_len,
                arity.len() - owner_len,
                "source_delta".to_string(),
                true,
                target_prefix.clone(),
                None,
            )
        } else {
            display_morphism_index_prefix_walk(
                prefix_columns,
                arity.len(),
                format!("{index_field_name}_all"),
                true,
            )
            .to_string()
        };
        let apply_propagated = display_apply_morphism_index_propagated(
            index_field_name,
            arity.len(),
            prefix_len,
            suffix_len,
        );
        let suffix_type = display_prefix_tree_type(suffix_len);

        let relation = match flat_in_rel {
            FlatInRel::Rel(rel) => rel,
            FlatInRel::RelWithDiagonals { .. } | FlatInRel::TypeSet(_) | FlatInRel::Equality(_) => {
                unreachable!("only primary relation indices are propagated")
            }
        };
        let invalidate = indices::invalidate(relation, index_selection, ctx);
        if !checkpointed {
            return writedoc! {f, r#"
                {{
                {preparation}
                {member_maps}
                let mut {index_field_name}_all = self.{index_field_name}_all.clone();
                let {index_field_name}_own = &mut self.{index_field_name}_own;
                let mut propagated: Vec<([u32; {prefix_len}], {suffix_type})> = Vec::new();
                {collect_propagated}
                {apply_propagated}
                self.{index_field_name}_all = {index_field_name}_all;
                {invalidate}
                }}
            "#};
        }
        let checkpoint = transport::field(&flat_in_rel, parent_model_type, ctx);
        let key = (0..owner_len - 1)
            .map(|i| format!("parents[{i}]"))
            .chain(["*morph".to_string(), "*dom".to_string(), "*cod".to_string()])
            .join(", ");
        let source_slice = |owner: &str| {
            (0..owner_len).fold(format!("Some(&self.{index_field_name}_all)"), |tree, i| {
                let el = if i + 1 == owner_len {
                    owner.to_string()
                } else {
                    format!("parents[{i}]")
                };
                format!("{tree}.and_then(|tree| tree.get({el}))")
            })
        };
        let dim = arity.len() - owner_len;
        let source_slice = format!(
            "{}.unwrap_or_else(|| PrefixTree{dim}::empty())",
            source_slice("*dom")
        );
        let maps = prefix_columns
            .iter()
            .enumerate()
            .filter_map(|(i, column)| match column {
                MorphismIndexColumnKind::Member(_) => Some(format!("map_el{i}.clone()")),
                MorphismIndexColumnKind::OuterParent(_)
                | MorphismIndexColumnKind::Parent
                | MorphismIndexColumnKind::Copy => None,
            })
            .join(", ");
        let map_columns: Vec<_> = prefix_columns
            .iter()
            .enumerate()
            .filter_map(|(column, kind)| match kind {
                MorphismIndexColumnKind::Member(_) => Some(column),
                MorphismIndexColumnKind::OuterParent(_)
                | MorphismIndexColumnKind::Parent
                | MorphismIndexColumnKind::Copy => None,
            })
            .collect();
        let collect_map_deltas = map_columns
            .iter()
            .enumerate()
            .map(|(map, &column)| {
                let collect = display_morphism_index_prefix_walk_from(
                    prefix_columns,
                    owner_len,
                    arity.len() - owner_len,
                    "source".to_owned(),
                    true,
                    target_prefix.clone(),
                    Some(column),
                );
                let stable = if map + 1 < map_columns.len() {
                    // Attribute a combination to its first changed map column,
                    // so simultaneous image changes do not repeat its suffix.
                    formatdoc! {"
                        let stable_map_el{column} = map_el{column}.difference(&map_deltas[{map}]);
                        let map_el{column} = &stable_map_el{column};
                    "}
                } else {
                    String::new()
                };
                formatdoc! {"
                    if !map_deltas[{map}].is_empty() {{
                        let map_el{column} = &map_deltas[{map}];
                        {collect}
                    }}
                    {stable}
                "}
            })
            .join("\n");
        writedoc! {f, r#"
            {{
            {preparation}
            {member_maps}
            let checkpoint_key = [{key}];
            let source = {source_slice}.clone();
            let (source_delta, map_deltas) = self.{checkpoint}.entry(checkpoint_key)
                .or_insert_with(eqlog_runtime::__private::TransportCheckpoint::new)
                .prepare(&source, &[{maps}], retain_own);
            let maps_changed = map_deltas.iter().any(|map| !map.is_empty());
            if !source_delta.is_empty() || maps_changed {{
            let mut {index_field_name}_all = self.{index_field_name}_all.clone();
            let {index_field_name}_own = &mut self.{index_field_name}_own;
            let mut propagated: Vec<([u32; {prefix_len}], {suffix_type})> = Vec::new();
            let source_delta = &source_delta;
            {collect_propagated}
            if maps_changed {{
            let source = source.difference(source_delta);
            let source = &source;
            {collect_map_deltas}
            }}
            {apply_propagated}
            self.{index_field_name}_all = {index_field_name}_all;
            {invalidate}
            }}
            }}
        "#}
    })
}

fn display_propagate_model_morphisms_fn<'a>(
    typ: TypeId,
    ctx: &'a RustGenCtx<'a>,
    index_selection: &'a IndexSelection,
    plan: Option<&'a PropagationPlan>,
    suffix: &'a str,
) -> impl Display + 'a {
    FmtFn(move |f| {
        let type_snake = display_type(typ, ctx).to_string().to_case(Snake);
        let parent_len = ctx.signature().type_(typ).parents.len();
        let components = display_morphism_components(typ, ctx, index_selection, plan.is_some());
        let prepare_graph = FmtFn(|f| {
            if let Some(plan) = plan {
                for (rel, index) in plan.graph_indices.get(&typ).into_iter().flatten() {
                    write!(f, "{}", indices::prepare(rel, index, index_selection, ctx))?;
                }
            }
            Ok(())
        });
        let relations: Vec<_> = index_selection
            .indices
            .iter()
            .filter(|(rel, _)| ctx.has_shared_indices(rel))
            .filter(|(rel, _)| propagation_includes(plan, rel))
            .filter(|(rel, _)| match rel {
                FlatInRel::Rel(rel) => {
                    rel.parent_model_type(ctx.signature())
                        .is_some_and(|parent| {
                            parent == typ || ctx.signature().type_(parent).parents.contains(&typ)
                        })
                }
                FlatInRel::RelWithDiagonals { .. }
                | FlatInRel::Equality(_)
                | FlatInRel::TypeSet(_) => false,
            })
            .map(|(rel, _)| rel)
            .collect();
        let relation_count = relations.len();
        let frontier = transport::prepare_frontier(typ, &relations, plan, ctx, index_selection);
        let finish_frontier = transport::finish_frontier(typ, &relations, ctx, index_selection);
        let remaps = relations
            .iter()
            .enumerate()
            .map(|(relation_index, &rel)| {
                let index = index_selection.current_primary(rel);
                let remap = display_remap_parented_index(
                    rel.clone(),
                    index.clone(),
                    typ,
                    ctx,
                    index_selection,
                    plan.and_then(|plan| plan.map_indices.get(&(typ, rel.clone()))),
                );
                formatdoc! {"
                    if active[{relation_index}] {{
                        let mut relation_changed = false;
                        {remap}
                        inserted[{relation_index}] = relation_changed;
                    }}
                "}
            })
            .format("\n");

        let child_parents = (0..parent_len)
            .map(|i| format!("parents[{i}]"))
            .chain(once("object".to_string()))
            .format(", ")
            .to_string();
        let children = ctx
            .signature()
            .iter_model_decls()
            .filter(|(_, ids)| ctx.signature().type_(ids.type_).parents.last() == Some(&typ))
            .filter(|(_, ids)| plan.is_none_or(|plan| plan.models.contains(&ids.type_)))
            .map(|(_, ids)| {
                let child_snake = display_type(ids.type_, ctx).to_string().to_case(Snake);
                format!("component_changed |= self.__propagate_{child_snake}_morphisms{suffix}([{child_parents}], retain_component_own);")
            })
            .format("\n")
            .to_string();
        // Cyclic inheritance cannot replace owned facts: every copy might
        // otherwise depend on another copy in the same cycle. This applies
        // to nested graphs too, since outer maps can close an inner path.
        writedoc! {f, "
            #[allow(unused_variables, unused_mut)]
            fn __propagate_{type_snake}_morphisms{suffix}(
                &mut self, parents: [u32; {parent_len}], retain_own: bool,
            ) -> bool {{
                {prepare_graph}
                {components}
                {frontier}
                if !transport_all && transport_work.iter().all(|work| work.is_empty()) {{
                    return false;
                }}
                let mut changed = false;
                for component in components.iter() {{
                    let cyclic = !component.internal.is_empty();
                    let retain_component_own = retain_own || cyclic;
                    loop {{
                        let mut component_changed = false;
                        for &object in &component.objects {{
                            {children}
                        }}
                        for morphism in &component.internal {{
                            let active: [bool; {relation_count}] = std::array::from_fn(
                                |i| transport_all || transport_work[i].needs_visit(morphism),
                            );
                            if !active.iter().any(|&active| active) {{ continue; }}
                            let mut inserted = [false; {relation_count}];
                            component_changed |= self.__propagate_{type_snake}_morphism_selected{suffix}(
                                parents, morphism, retain_component_own, &active, &mut inserted,
                            );
                            if !transport_all {{
                                for (work, inserted) in transport_work.iter_mut().zip(inserted) {{
                                    if inserted {{ work.mark_changed(morphism.cod); }}
                                }}
                            }}
                        }}
                        changed |= component_changed;
                        if !cyclic || !component_changed {{
                            break;
                        }}
                    }}
                    for morphism in &component.outgoing {{
                        let active: [bool; {relation_count}] = std::array::from_fn(
                            |i| transport_all || transport_work[i].needs_visit(morphism),
                        );
                        if !active.iter().any(|&active| active) {{ continue; }}
                        let mut inserted = [false; {relation_count}];
                        changed |= self.__propagate_{type_snake}_morphism_selected{suffix}(
                            parents, morphism, retain_own, &active, &mut inserted,
                        );
                        if !transport_all {{
                            for (work, inserted) in transport_work.iter_mut().zip(inserted) {{
                                if inserted {{ work.mark_changed(morphism.cod); }}
                            }}
                        }}
                    }}
                }}
                {finish_frontier}
                changed
            }}

            #[allow(unused_variables, unused_mut)]
            fn __propagate_{type_snake}_morphism{suffix}(
                &mut self,
                parents: [u32; {parent_len}],
                morphism: &MorphismWithSignature,
                retain_own: bool,
            ) -> bool {{
                self.__propagate_{type_snake}_morphism_selected{suffix}(
                    parents, morphism, retain_own, &[true; {relation_count}], &mut [false; {relation_count}],
                )
            }}

            #[allow(unused_variables, unused_mut)]
            fn __propagate_{type_snake}_morphism_selected{suffix}(
                &mut self,
                parents: [u32; {parent_len}],
                MorphismWithSignature {{ morph, dom, cod }}: &MorphismWithSignature,
                retain_own: bool,
                active: &[bool; {relation_count}],
                inserted: &mut [bool; {relation_count}],
            ) -> bool {{
                let mut changed = false;
                {remaps}
                changed
            }}
        "}
    })
}

fn propagation_includes(plan: Option<&PropagationPlan>, rel: &FlatInRel) -> bool {
    plan.is_none_or(|plan| match rel {
        FlatInRel::Rel(rel) => plan.relations.contains(rel),
        FlatInRel::RelWithDiagonals { .. } | FlatInRel::TypeSet(_) | FlatInRel::Equality(_) => {
            false
        }
    })
}

fn display_recompute_model_indices_fn<'a>(
    ctx: &'a RustGenCtx<'a>,
    index_selection: &'a IndexSelection,
    plan: Option<&'a PropagationPlan>,
    suffix: &'a str,
) -> impl Display + 'a {
    FmtFn(move |f| {
        let propagation_functions = ctx
            .signature()
            .iter_model_decls()
            .filter(|(_, ids)| plan.is_none_or(|plan| plan.models.contains(&ids.type_)))
            .map(|(_, ids)| {
                display_propagate_model_morphisms_fn(ids.type_, ctx, index_selection, plan, suffix)
            })
            .format("\n");
        let propagate = ctx
            .signature()
            .iter_model_decls()
            .filter(|(_, ids)| ctx.signature().type_(ids.type_).parents.is_empty())
            .filter(|(_, ids)| plan.is_none_or(|plan| plan.models.contains(&ids.type_)))
            .map(|(_, ids)| {
                let type_snake = display_type(ids.type_, ctx).to_string().to_case(Snake);
                format!("self.__propagate_{type_snake}_morphisms{suffix}([], false);")
            })
            .format("\n");
        let invalidate = iter_flat_rels(ctx.signature())
            .filter(|rel| ctx.has_shared_indices(&FlatInRel::Rel(*rel)))
            .filter(|rel| propagation_includes(plan, &FlatInRel::Rel(*rel)))
            .map(|rel| indices::invalidate(rel, index_selection, ctx))
            .format("\n")
            .to_string();
        writedoc! {f, "
            {propagation_functions}

            fn recompute_model_indices{suffix}(&mut self) {{
                {invalidate}
                {propagate}
                {invalidate}
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
                self.__close_until(None);
            }}

            fn __check_condition(&mut self, condition: Option<&dyn Fn(&Self) -> bool>) -> bool {{
                if let Some(condition) = condition {{
                    self.canonicalize();
                    return condition(self);
                }}
                false
            }}
        "}
    })
}

fn display_new_fn<'a>(
    ctx: &'a RustGenCtx<'a>,
    index_selection: &'a IndexSelection,
    codegen: &'a stratified::Codegen<'a>,
    native_plans: &'a [NativeIndexPreparation],
) -> impl Display + 'a {
    FmtFn(move |f| {
        writeln!(f, "/// Creates an empty model.").unwrap();
        writeln!(f, "#[allow(dead_code)]").unwrap();
        writeln!(f, "pub fn new() -> Self {{").unwrap();
        writeln!(f, "Self {{").unwrap();
        writeln!(f, "__pending_delta: ModelDelta::new(),")?;
        write!(f, "{}", native_indices::init(native_plans))?;
        write!(f, "{}", transport::fields(ctx, index_selection, true))?;
        write!(f, "{}", codegen.init(index_selection, ctx))?;
        for typ in ctx.signature().iter_types() {
            let type_snake = display_type(typ, ctx).to_string().to_case(Snake);
            writeln!(f, "{type_snake}_equalities: Unification::new(),").unwrap();
            writeln!(f, "{type_snake}_weights: Vec::new(),").unwrap();
            writeln!(f, "{type_snake}_uprooted: Vec::new(),").unwrap();
        }
        for (flat_rel, index) in index_selection.current_indices() {
            let field_name = display_current_index_field_name(&flat_rel, &index, ctx);
            let index_type = if index_selection.is_primary(flat_rel, index) {
                display_index_type(flat_rel, ctx).to_string()
            } else {
                "eqlog_runtime::__private::LazyIndex".to_string()
            };
            if ctx.has_shared_indices(&flat_rel) {
                if index_selection.is_primary(flat_rel, index) {
                    writeln!(f, "{field_name}_own: {index_type}::new(),").unwrap();
                }
                writeln!(f, "{field_name}_all: {index_type}::new(),").unwrap();
            } else {
                writeln!(f, "{field_name}: {index_type}::new(),").unwrap();
            }
        }
        for rel in iter_flat_rels(ctx.signature()) {
            let type_set: BTreeSet<TypeId> = rel.arity(ctx.signature()).into_iter().collect();
            for typ in type_set {
                let field_name = display_element_index_field_name(rel, typ, ctx);
                writeln!(f, "{field_name}: BTreeMap::new(),").unwrap();
            }
        }
        writeln!(f, "__allocated: false,").unwrap();
        writeln!(f, "__closed: false,").unwrap();
        writeln!(f, "}}").unwrap();
        write!(f, "}}").unwrap();
        Ok(())
    })
}

fn display_define_fn<'a>(
    func: FuncId,
    ctx: &'a RustGenCtx<'a>,
    index_selection: &'a IndexSelection,
) -> impl Display + 'a {
    FmtFn(move |f| {
        let func_name = display_func(func, ctx);
        let func_snake = func_name.to_string().to_case(Snake);

        let domain = flat_domain(func, ctx.signature());
        let codomain = ctx.signature().func(func).codomain;

        let codomain_camel = format!("{}", display_type(codomain, ctx)).to_case(UpperCamel);
        let codomain_snake = codomain_camel.to_case(Snake);

        let func_arg_vars: Vec<ElVar> = (0..domain.len()).map(ElVar::from).collect();
        let result_var = ElVar::from(domain.len());

        let fn_args = func_arg_vars
            .iter()
            .cloned()
            .zip(domain.iter().copied())
            .map(|(var, var_typ)| {
                FmtFn(move |f: &mut Formatter| -> Result {
                    let type_camel = format!("{}", display_type(var_typ, ctx)).to_case(UpperCamel);
                    write!(f, "{var}: {type_camel}")
                })
            })
            .format(", ");

        let args = func_arg_vars
            .iter()
            .cloned()
            .map(display_var)
            .format(", ")
            .to_string();
        let rel_args = func_arg_vars
            .iter()
            .cloned()
            .chain(once(result_var.clone()))
            .map(display_var)
            .format(", ");

        if let Some(types) = ctx.signature().types_for_mor_app_func(func) {
            let parent_model = types.model_type(ctx.signature());
            let member_type = types.member_type;
            if ctx.signature().type_(member_type).parents.last().copied() != Some(parent_model) {
                let source_parents = display_nested_mor_app_source_parents(
                    func,
                    types,
                    &func_arg_vars,
                    ctx,
                    index_selection,
                );
                let image_parents =
                    display_nested_mor_app_image_parents(func, types, &func_arg_vars, ctx);
                let parent_args = (0..ctx.signature().type_(member_type).parents.len())
                    .map(|i| format!("parent{i}"))
                    .format(", ")
                    .to_string();
                let arg = func_arg_vars.last().expect("morphism application argument");
                return writedoc! {f, "
                    /// Enforces that `{func_snake}({args})` is defined, adjoining a new element if necessary.
                    #[allow(dead_code)]
                    pub fn define_{func_snake}(&mut self, {fn_args}) -> {codomain_camel} {{
                        if let Some(result) = self.{func_snake}({args}) {{
                            return result;
                        }}
                        let {arg} = self.root_{codomain_snake}({arg});
                        let ({parent_args}) = {{
                            {source_parents}
                            {image_parents}
                            dependent_image_parents.next().expect(
                                \"invalid dependent argument: nested morphism application requires defined parent images\"
                            )
                        }};
                        let {result_var} = self.new_{codomain_snake}_internal({parent_args});
                        self.insert_{func_snake}({rel_args});
                        {result_var}
                    }}
                "};
            }
        }

        let codomain_parents = ctx.signature().type_(codomain).parents.clone();
        let func_is_mor_app = ctx.signature().type_for_mor_app_func(func).is_some();

        let mor_app_cod_args = if domain.len() >= 2 {
            func_arg_vars[..=domain.len() - 2]
                .iter()
                .cloned()
                .map(display_var)
                .format(", ")
                .to_string()
        } else {
            String::new()
        };

        let define_parent_var = if func_is_mor_app && !codomain_parents.is_empty() {
            let model_type = *codomain_parents.last().unwrap();
            let cod_func = ctx
                .signature()
                .ids_for_model_type(model_type)
                .expect("parent model type should have model ids")
                .cod;
            let cod_func_snake = display_func(cod_func, ctx);
            format!("let parent_el = self.define_{cod_func_snake}({mor_app_cod_args});")
        } else {
            String::new()
        };

        let new_parent_args = if codomain_parents.is_empty() {
            String::new()
        } else if func_is_mor_app {
            let outer = func_arg_vars[..codomain_parents.len() - 1]
                .iter()
                .cloned()
                .map(display_var)
                .format(", ")
                .to_string();
            if outer.is_empty() {
                "parent_el".to_string()
            } else {
                format!("{outer}, parent_el")
            }
        } else {
            let columns = ctx
                .signature()
                .func_parent_columns(func)
                .map(|columns| columns.last().unwrap().clone())
                .unwrap_or_else(|| (0..codomain_parents.len()).collect());
            columns
                .into_iter()
                .map(|column| display_var(func_arg_vars[column].clone()))
                .format(", ")
                .to_string()
        };

        writedoc! {f, "
            /// Enforces that `{func_snake}({args})` is defined, adjoining a new element if necessary.
            #[allow(dead_code)]
            pub fn define_{func_snake}(&mut self, {fn_args}) -> {codomain_camel} {{
                match self.{func_snake}({args}) {{
                    Some(result) => result,
                    None => {{
                        {define_parent_var}
                        let {result_var} = self.new_{codomain_snake}_internal({new_parent_args});
                        self.insert_{func_snake}({rel_args});
                        {result_var}
                    }}
                }}
            }}
        "}
    })
}

impl Display for IndexAge {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        match self {
            IndexAge::New => write!(f, "new"),
            IndexAge::Old => write!(f, "old"),
        }
    }
}

fn display_index_field_name<'a>(
    rel: &'a FlatInRel,
    index: &'a IndexSpec,
    ctx: &'a RustGenCtx<'a>,
) -> impl 'a + Display {
    FmtFn(move |f| {
        let order = index.order.iter().format("_");
        let age = index.age;
        match rel {
            FlatInRel::Rel(rel) => {
                let rel_snake = display_rel(*rel, ctx).to_string().to_case(Snake);
                write!(f, "{rel_snake}_{age}_order_{order}")
            }
            FlatInRel::RelWithDiagonals { rel, equalities } => {
                let rel_snake = display_rel(*rel, ctx).to_string().to_case(Snake);
                let equalities = equalities.iter().format("_");
                write!(f, "{rel_snake}_{age}_eqs_{equalities}_order_{order}")
            }
            FlatInRel::TypeSet(typ) => {
                let type_snake = display_type(*typ, ctx).to_string().to_case(Snake);
                write!(f, "{type_snake}_{age}_order_0")
            }
            FlatInRel::Equality(_) => {
                panic!("Equality in relations should have been transformed the equality pass on flat eqlog")
            }
        }
    })
}

fn display_current_index_field_name<'a>(
    rel: &'a FlatInRel,
    index: &'a IndexSpec,
    ctx: &'a RustGenCtx<'a>,
) -> impl 'a + Display {
    FmtFn(move |f| {
        let order = index.order.iter().format("_");
        match rel {
            FlatInRel::Rel(rel) => {
                let rel_snake = display_rel(*rel, ctx).to_string().to_case(Snake);
                write!(f, "{rel_snake}_order_{order}")
            }
            FlatInRel::RelWithDiagonals { rel, equalities } => {
                let rel_snake = display_rel(*rel, ctx).to_string().to_case(Snake);
                let equalities = equalities.iter().format("_");
                write!(f, "{rel_snake}_eqs_{equalities}_order_{order}")
            }
            FlatInRel::TypeSet(typ) => {
                let type_snake = display_type(*typ, ctx).to_string().to_case(Snake);
                write!(f, "{type_snake}_order_0")
            }
            FlatInRel::Equality(_) => {
                panic!("Equality in relations should have been transformed the equality pass on flat eqlog")
            }
        }
    })
}

fn display_own_index_field_name<'a>(
    flat_in_rel: &'a FlatInRel,
    index: &'a IndexSpec,
    ctx: &'a RustGenCtx<'a>,
) -> impl 'a + Display {
    FmtFn(move |f| {
        let index_field = display_current_index_field_name(&flat_in_rel, &index, ctx);
        if ctx.has_shared_indices(&flat_in_rel) {
            write!(f, "{index_field}_own")
        } else {
            write!(f, "{index_field}")
        }
    })
}

fn display_index_expr<'a>(
    flat_in_rel: &'a FlatInRel,
    index: &'a IndexSpec,
    ctx: &'a RustGenCtx<'a>,
) -> impl 'a + Display {
    FmtFn(move |f| {
        let index_field = display_current_index_field_name(&flat_in_rel, &index, ctx);
        if ctx.has_shared_indices(&flat_in_rel) {
            write!(f, "self.{index_field}_all()")
        } else {
            let index_field = display_current_index_field_name(&flat_in_rel, &index, ctx);
            write!(f, "self.{index_field}()")
        }
    })
}

fn display_all_index_field_name<'a>(
    flat_in_rel: &'a FlatInRel,
    index: &'a IndexSpec,
    ctx: &'a RustGenCtx<'a>,
) -> impl 'a + Display {
    FmtFn(move |f| {
        let index_field = display_current_index_field_name(flat_in_rel, index, ctx);
        if ctx.has_shared_indices(&flat_in_rel) {
            write!(f, "{index_field}_all")
        } else {
            write!(f, "{index_field}")
        }
    })
}

fn display_element_index_field_name<'a>(
    rel: FlatRel,
    typ: TypeId,
    ctx: &'a RustGenCtx<'a>,
) -> impl Display + 'a {
    FmtFn(move |f| {
        let rel_snake = display_rel(rel, ctx).to_string().to_case(Snake);
        let type_snake = display_type(typ, ctx).to_string().to_case(Snake);
        write!(f, "{rel_snake}_{type_snake}_element_index")
    })
}

fn display_index_type<'a>(rel: &'a FlatInRel, ctx: &'a RustGenCtx<'a>) -> impl Display + 'a {
    FmtFn(move |f| {
        let arity_len = rel.arity(ctx.signature()).len();
        write!(f, "PrefixTree{arity_len}")
    })
}

fn display_weight_static_name<'a>(rel: FlatRel, ctx: &'a RustGenCtx<'a>) -> impl 'a + Display {
    FmtFn(move |f| {
        let rel_screaming_snake = display_rel(rel, ctx).to_string().to_case(UpperSnake);
        write!(f, "{rel_screaming_snake}_WEIGHT")
    })
}

fn display_weight_static<'a>(
    rel: FlatRel,
    index_selection: &'a IndexSelection,
    ctx: &'a RustGenCtx<'a>,
) -> impl 'a + Display {
    FmtFn(move |f| {
        let static_name = display_weight_static_name(rel, ctx);

        let el_lookup_weight = rel.arity(ctx.signature()).len();

        let index_weight: usize = index_selection
            .current_indices()
            .filter(|(source, _)| indices::source_relation(source) == FlatInRel::Rel(rel))
            .map(|(_, index)| index.order.len())
            .sum();
        let weight = el_lookup_weight + index_weight;

        writedoc! {f, r#"
            #[allow(unused)]
            const {static_name}: usize = {weight};
        "#}
    })
}

fn display_theory_struct<'a>(
    name: &'a str,
    ctx: &'a RustGenCtx<'a>,
    index_selection: &'a IndexSelection,
    codegen: &'a stratified::Codegen<'a>,
    native_plans: &'a [NativeIndexPreparation],
) -> impl Display + 'a {
    FmtFn(move |f| {
        let index_fields = index_selection
            .current_indices()
            .map(|(rel, index)| (rel.clone(), index.clone()))
            .map(|(rel, index)| {
                FmtFn(move |f| {
                    let index_name = display_current_index_field_name(&rel, &index, ctx);
                    let index_type = indices::field_type(&rel, &index, index_selection, ctx);
                    if ctx.has_shared_indices(&rel) {
                        if index_selection.is_primary(&rel, &index) {
                            writeln!(f, "{index_name}_own: {index_type},")?;
                        }
                        writedoc! {f, "
                            {index_name}_all: {index_type},
                        "}
                    } else {
                        write!(f, "{index_name}: {index_type},")
                    }
                })
            })
            .format("\n");
        let element_index_fields = iter_flat_rels(ctx.signature())
            .map(|rel| {
                let arity: Vec<TypeId> = rel.arity(ctx.signature()).into_iter().collect();
                let arity_len = arity.len();
                let arity_set: BTreeSet<TypeId> = arity.iter().copied().collect();
                arity_set
                    .into_iter()
                    .map(move |typ| {
                        FmtFn(move |f| {
                            let field_name = display_element_index_field_name(rel, typ, ctx);
                            write!(f, "{field_name}: BTreeMap<u32, Vec<[u32; {arity_len}]>>,")
                        })
                    })
                    .format("\n")
            })
            .format("\n");

        let type_fields = ctx
            .signature()
            .iter_types()
            .map(|typ| display_type_fields(typ, ctx))
            .format("\n");

        let scheduler_fields = FmtFn(move |f| {
            write!(f, "{}", transport::fields(ctx, index_selection, false))?;
            write!(f, "{}", native_indices::fields(native_plans, ctx))?;
            write!(f, "{}", codegen.fields(ctx, index_selection))?;
            Ok(())
        });

        writedoc! {f, "
            /// A model of the `{name}` theory.
            pub struct {name} {{
                {index_fields}
                {element_index_fields}
                {type_fields}
                __allocated: bool,
                __closed: bool,
                __pending_delta: ModelDelta,
                {scheduler_fields}
            }}
            type Model = {name};
        "}
    })
}

fn display_theory_impl<'a>(
    name: &'a str,
    program: &'a RamProgram,
    ctx: &'a RustGenCtx<'a>,
    index_selection: &'a IndexSelection,
    codegen: &'a stratified::Codegen<'a>,
) -> impl Display + 'a {
    FmtFn(move |f| {
        let ram_modules = program.modules.as_slice();
        writeln!(f, "impl {} {{", name)?;
        write!(f, "{}", indices::accessors(index_selection, ctx))?;

        let new_fn = display_new_fn(ctx, index_selection, codegen, &program.native_indices);
        write!(f, "{}", new_fn)?;
        writeln!(f, "")?;

        let close_fn = display_close_fn();
        write!(f, "{}", close_fn)?;

        write!(f, "{}", codegen.methods(ram_modules, ctx, index_selection))?;
        write!(f, "{}", codegen.close(ctx, index_selection))?;

        for typ in ctx.signature().iter_types() {
            let iter_type_fn = display_iter_type_fn(typ, ctx, index_selection);
            write!(f, "{}", iter_type_fn)?;

            let root_fn = display_root_fn(typ, ctx);
            write!(f, "{}", root_fn)?;

            let are_equal_fn = display_are_equal_fn(typ, ctx);
            write!(f, "{}", are_equal_fn)?;

            writeln!(f, "")?;
        }

        for typ in ctx.signature().iter_types() {
            let new_element_fn_internal =
                display_new_element_fn_internal(typ, ctx, index_selection);
            writeln!(f, "{new_element_fn_internal}")?;

            let track_merges = codegen.tracks_owner(typ, ctx);
            let equate_elements = display_equate_elements(typ, ctx, index_selection, track_merges);
            write!(f, "{}", equate_elements)?;
        }

        for typ in ctx.signature().iter_types() {
            match ctx.signature().type_(typ).kind {
                TypeKind::Plain | TypeKind::Model | TypeKind::Mor(_) => {
                    let new_el_fn = display_new_element_fn(typ, ctx);
                    writeln!(f, "{new_el_fn}")?;
                }
                TypeKind::Enum => {
                    let enum_node = ctx
                        .signature()
                        .enum_decl_for_type(typ)
                        .expect("enum type should have an enum declaration");
                    let new_enum_el_fn = display_new_enum_element(enum_node, ctx);
                    let enum_cases_fn = display_enum_cases_fn(enum_node, ctx);
                    writedoc! {f, "
                        {new_enum_el_fn}
                        {enum_cases_fn}
                    "}?;
                }
            }
        }

        for func in ctx.signature().iter_funcs() {
            let rel = FlatRel::Func(func);
            let eval_fn = display_pub_function_eval_fn(func, ctx, index_selection);
            write!(f, "{eval_fn}")?;

            let iter_fn = display_pub_iter_fn(rel, ctx, index_selection);
            write!(f, "{}", iter_fn)?;

            let insert_relation = display_pub_insert_relation(rel, ctx, index_selection, true);
            write!(f, "{}", insert_relation)?;

            writeln!(f, "")?;
        }

        for func in ctx.signature().iter_funcs() {
            if ctx.function_can_be_made_defined(func) {
                let define_fn = display_define_fn(func, ctx, index_selection);
                write!(f, "{}", define_fn)?;
            }
        }

        for rel in ctx.pred_like_rels() {
            let arity = rel.arity(ctx.signature());
            let arity: Vec<String> = arity
                .into_iter()
                .map(|typ| display_type(typ, ctx).to_string())
                .collect();
            let arity: Vec<&str> = arity.iter().map(|s| s.as_str()).collect();

            let predicate_holds_fn = display_pub_predicate_holds_fn(rel, ctx, index_selection);
            write!(f, "{}", predicate_holds_fn)?;

            if !arity.is_empty() {
                let iter_fn = display_pub_iter_fn(rel, ctx, index_selection);
                write!(f, "{}", iter_fn)?;
            }

            let insert_relation = display_pub_insert_relation(rel, ctx, index_selection, false);
            write!(f, "{}", insert_relation)?;

            writeln!(f, "")?;
        }

        let canonicalize_fn = display_canonicalize_fn(ctx, index_selection);
        write!(f, "{canonicalize_fn}\n")?;

        match ctx.model_mode() {
            ModelMode::Native => {
                write!(
                    f,
                    "{}",
                    native_indices::methods(&program.native_indices, index_selection, ctx)
                )?;
                let recompute_model_indices_fn =
                    display_recompute_model_indices_fn(ctx, index_selection, None, "");
                write!(f, "{recompute_model_indices_fn}")?;
                for (s, preparation) in program.preparations.iter().enumerate() {
                    let scoped = program.schedule.strata[s].model.is_some();
                    let plans = std::iter::once((format!("_stratum_{s}"), &preparation.native))
                        .chain(
                            preparation
                                .stable
                                .iter()
                                .map(|plan| (format!("_stratum_stable_{s}"), plan)),
                        );
                    for (suffix, plan) in plans {
                        if scoped {
                            for &model in &plan.propagation.models {
                                if plan.descendants.iter().any(|child| {
                                    *child == model
                                        || ctx.signature().type_(model).parents.contains(child)
                                }) {
                                    write!(
                                        f,
                                        "{}",
                                        display_propagate_model_morphisms_fn(
                                            model,
                                            ctx,
                                            index_selection,
                                            Some(&plan.propagation),
                                            &suffix
                                        )
                                    )?;
                                }
                            }
                            continue;
                        }
                        if plan.propagation.relations.is_empty() {
                            continue;
                        }
                        let recompute = display_recompute_model_indices_fn(
                            ctx,
                            index_selection,
                            Some(&plan.propagation),
                            &suffix,
                        );
                        write!(f, "{recompute}")?;
                    }
                }
                for (m, plan) in program.model_preparations.values().enumerate() {
                    let suffix = format!("_model_{m}");
                    write!(
                        f,
                        "{}",
                        display_recompute_model_indices_fn(
                            ctx,
                            index_selection,
                            Some(&plan.propagation),
                            &suffix
                        )
                    )?;
                }
            }
            ModelMode::Desugared => {}
        }

        write!(f, "}}")?;
        Ok(())
    })
}

fn display_rule_modules<'a>(
    ram_modules: &'a [RamModule],
    ctx: &'a RustGenCtx<'a>,
    symbol_prefix: &'a str,
) -> impl 'a + Display {
    ram_modules
        .iter()
        .map(move |ram_module| {
            FmtFn(move |f| {
                let lib = display_ram_module(ram_module, ctx, symbol_prefix);
                let ram_module_name = ram_module.name.as_str();
                writedoc! {f, "
                    mod {ram_module_name} {{
                        {lib}
                    }}
                "}
            })
        })
        .format("\n")
}

pub fn display_module<'a>(
    name: &'a str,
    ctx: &'a RustGenCtx<'a>,
    program: &'a RamProgram,
    index_selection: &'a IndexSelection,
    symbol_prefix: &'a str,
    build_type: BuildType,
) -> impl 'a + Display {
    let ram_modules = program.modules.as_slice();
    FmtFn(move |f| {
        let imports = display_imports();
        write!(f, "{}", imports)?;
        write!(f, "\n")?;

        match build_type {
            BuildType::Component => {}
            BuildType::Module => {
                display_rule_modules(ram_modules, ctx, symbol_prefix).fmt(f)?;
            }
        }

        let module_env_structs = ram_modules
            .iter()
            .map(|ram_module| display_module_env_struct(ram_module, ctx))
            .format("\n");
        writeln!(f, "{module_env_structs}")?;

        let rule_eval_fns = ram_modules
            .iter()
            .map(|ram_module| display_module_main_fn_decl(ram_module, symbol_prefix))
            .format("\n");
        writedoc! {f, r#"
            unsafe extern "Rust" {{
                {rule_eval_fns}
            }}
        "#}?;

        for rel in iter_flat_rels(ctx.signature()) {
            let weight_static = display_weight_static(rel, index_selection, ctx);
            write!(f, "{weight_static}")?;
        }

        for typ in ctx.signature().iter_types() {
            let type_struct = display_type_struct(typ, ctx);
            write!(f, "{}", type_struct)?;
            let type_impl = display_type_impl(typ, ctx);
            write!(f, "{}", type_impl)?;
        }
        write!(f, "\n")?;

        for (enum_decl, _) in ctx.signature().iter_enum_decls() {
            writeln!(f, "{}", display_enum(enum_decl, ctx))?;
        }

        for func in ctx.signature().iter_funcs() {
            let func_args_struct = display_func_args_struct(func, ctx);
            writeln!(f, "{func_args_struct}")?;
        }

        write!(f, "\n")?;

        let outputs = program
            .modules
            .iter()
            .flat_map(module_env_out_rels)
            .collect();
        let model_delta_struct = display_model_delta_struct(&outputs, ctx);
        write!(f, "{}", model_delta_struct)?;

        let codegen = stratified::Codegen::new(&program.schedule, program);
        write!(f, "{}", codegen.loop_input_types(index_selection, ctx))?;
        let theory_struct = display_theory_struct(
            name,
            ctx,
            index_selection,
            &codegen,
            &program.native_indices,
        );
        write!(f, "{}", theory_struct)?;

        let model_delta_impl = display_model_delta_impl(&outputs, ctx);
        write!(f, "{}", model_delta_impl)?;
        write!(f, "\n")?;

        let theory_impl = display_theory_impl(name, program, ctx, index_selection, &codegen);
        write!(f, "{}", theory_impl)?;

        let dynamic_impl = dynamic::display_dynamic_impl(name, ctx, index_selection);
        write!(f, "{dynamic_impl}")?;

        Ok(())
    })
}

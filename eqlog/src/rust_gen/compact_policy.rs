use convert_case::{Case, Casing};
use indoc::writedoc;
use itertools::Itertools;
use std::fmt::Display;

use super::{display_func, display_rel, display_type, RustGenCtx};
use crate::algebra::signature::TypeId;
use crate::flat_eqlog::FlatRel;
use crate::fmt_util::FmtFn;
use crate::ram::{
    ElVar, TotalCompletionCondition, TotalCompletionInstruction, TotalCompletionIteration,
};

pub(super) fn equality_guard<'a>(typ: TypeId, ctx: &'a RustGenCtx<'a>) -> impl Display + 'a {
    FmtFn(move |f| {
        let models = ctx.compact().policy_models();
        if models.is_empty() {
            return Ok(());
        }
        for &model in models {
            let name = display_type(model, ctx).to_string().to_case(Case::Snake);
            let ids = ctx.signature().ids_for_model_type(model).unwrap();
            if typ == model {
                writeln!(f, "self.__check_total_{name}_merge(lhs.0, rhs.0);")?;
            }
            if typ == ids.mor {
                writeln!(f, "self.__check_total_{name}_morphism_merge(lhs.0, rhs.0);")?;
            }
        }
        writeln!(f, "self.__materialize_compact_members();")
    })
}

pub(super) fn insert_guard<'a>(
    rel: FlatRel,
    args: &'a [ElVar],
    ctx: &'a RustGenCtx<'a>,
) -> impl Display + 'a {
    FmtFn(move |f| {
        let func = match rel {
            FlatRel::Func(func) => func,
            FlatRel::ModelMember(_) | FlatRel::Pred(_) => return Ok(()),
        };
        for &model in ctx.compact().policy_models() {
            let ids = ctx.signature().ids_for_model_type(model).unwrap();
            if func == ids.dom || func == ids.cod {
                let name = display_type(model, ctx).to_string().to_case(Case::Snake);
                let morphism = &args[0];
                let owner = &args[1];
                let domain = func == ids.dom;
                return writeln!(
                    f,
                    "self.__guard_total_{name}_endpoint({morphism}, {owner}, {domain});"
                );
            }
        }
        if let Some(types) = ctx.signature().types_for_mor_app_func(func) {
            if ctx.supports_compact_members(types.member_type) {
                let name = display_func(func, ctx);
                let (result, arguments) = args.split_last().unwrap();
                let arguments = arguments.iter().join(", ");
                writedoc! {f, "
                    if self.__has_compact_members() {{
                        if self.{name}({arguments}) == Some({result}) {{ return; }}
                        self.__materialize_compact_members();
                    }}
                "}?;
            }
        }
        Ok(())
    })
}

pub(super) fn endpoint_notice<'a>(
    rel: FlatRel,
    args: &'a [ElVar],
    ctx: &'a RustGenCtx<'a>,
) -> impl Display + 'a {
    FmtFn(move |f| {
        match rel {
            FlatRel::Func(func) => {
                for &model in ctx.compact().policy_models() {
                    let ids = ctx.signature().ids_for_model_type(model).unwrap();
                    if func == ids.dom || func == ids.cod {
                        let name = display_type(model, ctx).to_string().to_case(Case::Snake);
                        let morphism = &args[0];
                        writeln!(f, "self.__note_total_{name}_endpoint({morphism});")?;
                    }
                }
            }
            FlatRel::ModelMember(_) | FlatRel::Pred(_) => {}
        }
        Ok(())
    })
}

fn active(types: &[TypeId], ctx: &RustGenCtx<'_>) -> String {
    types
        .iter()
        .map(|&typ| {
            let name = display_type(typ, ctx).to_string().to_case(Case::Snake);
            format!("self.__compact_members_{name}.is_some()")
        })
        .join(" || ")
}

pub(super) fn fields<'a>(ctx: &'a RustGenCtx<'a>, initialize: bool) -> impl Display + 'a {
    FmtFn(move |f| {
        for &model in ctx.compact().policy_models() {
            let name = display_type(model, ctx).to_string().to_case(Case::Snake);
            if initialize {
                writeln!(f, "__pending_total_edges_{name}: BTreeSet::new(),")?;
            } else {
                writeln!(f, "__pending_total_edges_{name}: BTreeSet<u32>,")?;
            }
        }
        Ok(())
    })
}

fn completion_body<'a>(
    body: &'a [TotalCompletionInstruction],
    model: TypeId,
    ctx: &'a RustGenCtx<'a>,
) -> impl Display + 'a {
    FmtFn(move |f| {
        let name = display_type(model, ctx).to_string().to_case(Case::Snake);
        for instruction in body {
            match instruction {
                TotalCompletionInstruction::ReturnWhenAny(conditions) => {
                    let condition = conditions
                        .iter()
                        .map(|condition| match condition {
                            TotalCompletionCondition::CompactMembers(members) => {
                                let active = active(members, ctx);
                                format!("({active})")
                            }
                            TotalCompletionCondition::EmptyPolicy => {
                                format!("self.__total_members_{name}.is_empty()")
                            }
                        })
                        .join(" || ");
                    writeln!(f, "if {condition} {{ return; }}")?;
                }
                TotalCompletionInstruction::ForEach { iteration, body } => {
                    let head = match iteration {
                        TotalCompletionIteration::Components => {
                            format!("component in self.__total_{name}_components(&[], None)")
                        }
                        TotalCompletionIteration::Outgoing => {
                            "edge in component.outgoing".to_owned()
                        }
                        TotalCompletionIteration::Members => "member in members".to_owned(),
                    };
                    let body = completion_body(body, model, ctx);
                    writeln!(f, "for {head} {{ {body} }}")?;
                }
                TotalCompletionInstruction::BindMorphism => {
                    let ids = ctx.signature().ids_for_model_type(model).unwrap();
                    let mor = display_type(ids.mor, ctx)
                        .to_string()
                        .to_case(Case::UpperCamel);
                    writeln!(f, "let morphism = {mor}(edge.morph);")?;
                }
                TotalCompletionInstruction::CollectSourceMembers(member) => {
                    let member_name = display_type(*member, ctx).to_string().to_case(Case::Snake);
                    let membership =
                        display_rel(FlatRel::ModelMember(*member), ctx).to_case(Case::Snake);
                    writedoc! {f, "
                        let members: BTreeSet<_> = self.iter_{membership}()
                            .filter(|(owner, _)| self.root_{name}(*owner).0 == edge.dom)
                            .map(|(_, member)| self.root_{member_name}(member)).collect();
                    "}?;
                }
                TotalCompletionInstruction::DefineImage(member) => {
                    let member_name = display_type(*member, ctx).to_string().to_case(Case::Snake);
                    writeln!(f, "self.define_{member_name}_mor_app(morphism, member);")?;
                }
            }
        }
        Ok(())
    })
}

pub(super) fn methods<'a>(ctx: &'a RustGenCtx<'a>) -> impl Display + 'a {
    FmtFn(move |f| {
        let models = ctx.compact().policy_models();
        if models.is_empty() {
            return Ok(());
        }
        let types = models
            .iter()
            .flat_map(|&model| ctx.compact().members(model).iter().copied())
            .collect_vec();
        let any_active = active(&types, ctx);
        let names = models
            .iter()
            .map(|&model| display_type(model, ctx).to_string().to_case(Case::Snake))
            .collect_vec();
        let capture = names
            .iter()
            .map(|name| format!("let policy_{name} = self.__total_members_{name}.clone();"))
            .join("\n");
        let restore = names
            .iter()
            .map(|name| format!("self.__total_members_{name} = policy_{name};"))
            .join("\n");
        writedoc! {f, "
            fn __has_compact_members(&self) -> bool {{ {any_active} }}

            fn __materialize_compact_members(&mut self) {{
                if !self.__has_compact_members() {{ return; }}
                {capture}
                let snapshot = <Self as eqlog_runtime::CompiledModel>::to_dynamic(self);
                let mut materialized = <Self as eqlog_runtime::CompiledModel>::from_dynamic(&snapshot)
                    .expect(\"materialized compact data preserves its signature and handles\");
                std::mem::swap(&mut materialized.__pending_delta, &mut self.__pending_delta);
                materialized.__allocated = self.__allocated;
                *self = materialized;
                {restore}
            }}
        "}?;
        for (&model, name) in models.iter().zip(&names) {
            let ids = ctx.signature().ids_for_model_type(model).unwrap();
            let camel = display_type(model, ctx)
                .to_string()
                .to_case(Case::UpperCamel);
            let mor = display_type(ids.mor, ctx)
                .to_string()
                .to_case(Case::UpperCamel);
            let mor_name = mor.to_case(Case::Snake);
            let dom = display_func(ids.dom, ctx);
            let cod = display_func(ids.cod, ctx);
            let compact = active(ctx.compact().members(model), ctx);
            let completion =
                completion_body(&ctx.transport().models[&model].completion, model, ctx);
            writedoc! {f, "
                fn __is_total_{name}_morphism(&self, morphism: u32) -> bool {{
                    let morphism = self.root_{mor_name}({mor}(morphism)).0;
                    if self.__total_members_{name}.contains(&morphism) {{ return true; }}
                    if {compact} {{ return false; }}
                    self.__total_members_{name}.iter().any(|&registered|
                        self.root_{mor_name}({mor}(registered)).0 == morphism)
                }}

                fn __total_{name}_components(&self, merges: &[(u32, u32)], additional: Option<u32>)
                    -> Vec<MorphismComponent>
                {{
                    let policy: BTreeSet<_> = self.__total_members_{name}.iter().copied()
                        .chain(additional).map(|morphism| self.root_{mor_name}({mor}(morphism)).0).collect();
                    let mut implied_merges = merges.to_vec();
                    let mut previous_domains = BTreeMap::new();
                    for (morphism, owner) in self.iter_{dom}() {{
                        let morphism = self.root_{mor_name}(morphism).0;
                        let owner = self.root_{name}(owner).0;
                        if let Some(previous) = previous_domains.insert(morphism, owner) {{
                            implied_merges.push((previous, owner));
                        }}
                    }}
                    let mut previous_codomains = BTreeMap::new();
                    for (morphism, owner) in self.iter_{cod}() {{
                        let morphism = self.root_{mor_name}(morphism).0;
                        let owner = self.root_{name}(owner).0;
                        if let Some(previous) = previous_codomains.insert(morphism, owner) {{
                            implied_merges.push((previous, owner));
                        }}
                    }}
                    let mut quotient_roots = BTreeMap::new();
                    for (mut left, mut right) in implied_merges {{
                        while let Some(&parent) = quotient_roots.get(&left) {{ left = parent; }}
                        while let Some(&parent) = quotient_roots.get(&right) {{ right = parent; }}
                        if left != right {{ quotient_roots.insert(left.max(right), left.min(right)); }}
                    }}
                    let quotient = |owner: {camel}| {{
                        let mut owner = self.root_{name}(owner).0;
                        while let Some(&parent) = quotient_roots.get(&owner) {{ owner = parent; }}
                        owner
                    }};
                    let mut domains = PrefixTree2::new();
                    let mut codomains = PrefixTree2::new();
                    let mut objects = PrefixTree1::new();
                    let mut defined_domains = BTreeSet::new();
                    let mut defined_codomains = BTreeSet::new();
                    for (morphism, owner) in self.iter_{dom}() {{
                        let morphism = self.root_{mor_name}(morphism).0;
                        if !policy.contains(&morphism) {{ continue; }}
                        let owner = quotient(owner);
                        domains.insert([owner, morphism]);
                        objects.insert([owner]);
                        defined_domains.insert(morphism);
                    }}
                    for (morphism, owner) in self.iter_{cod}() {{
                        let morphism = self.root_{mor_name}(morphism).0;
                        if !policy.contains(&morphism) {{ continue; }}
                        let owner = quotient(owner);
                        codomains.insert([morphism, owner]);
                        objects.insert([owner]);
                        defined_codomains.insert(morphism);
                    }}
                    assert!(policy.is_subset(&defined_domains) && policy.is_subset(&defined_codomains),
                        \"total member inheritance requires defined morphism endpoints\");
                    let components = morphism_components(&domains, &codomains, &objects);
                    assert!(components.iter().all(|component| component.internal.is_empty()),
                        \"total member inheritance must remain acyclic\");
                    components
                }}

                fn __check_total_{name}_merge(&self, left: u32, right: u32) {{
                    if !self.__total_members_{name}.is_empty() {{
                        self.__total_{name}_components(&[(left, right)], None);
                    }}
                }}

                fn __check_total_{name}_morphism_merge(&self, left: u32, right: u32) {{
                    if self.__total_members_{name}.is_empty() {{ return; }}
                    let domains: Vec<_> = self.iter_{dom}()
                        .filter(|(morphism, _)| {{
                            let root = self.root_{mor_name}(*morphism).0;
                            root == left || root == right
                        }})
                        .map(|(_, owner)| self.root_{name}(owner).0).collect();
                    let codomains: Vec<_> = self.iter_{cod}()
                        .filter(|(morphism, _)| {{
                            let root = self.root_{mor_name}(*morphism).0;
                            root == left || root == right
                        }})
                        .map(|(_, owner)| self.root_{name}(owner).0).collect();
                    let merges: Vec<_> = domains.windows(2).chain(codomains.windows(2))
                        .map(|pair| (pair[0], pair[1])).collect();
                    self.__total_{name}_components(&merges, None);
                }}

                fn __check_total_{name}_morphism(&self, morphism: u32) {{
                    self.__total_{name}_components(&[], Some(morphism));
                }}

                fn __guard_total_{name}_endpoint(&mut self, morphism: {mor}, owner: {camel}, domain: bool) {{
                    if !self.__is_total_{name}_morphism(morphism.0) {{ return; }}
                    let previous = if domain {{ self.{dom}(morphism) }} else {{ self.{cod}(morphism) }};
                    if let Some(previous) = previous {{
                        let previous = self.root_{name}(previous);
                        let owner = self.root_{name}(owner);
                        if previous != owner {{
                            self.__check_total_{name}_merge(previous.0, owner.0);
                            self.__materialize_compact_members();
                        }}
                    }}
                }}

                fn __note_total_{name}_endpoint(&mut self, morphism: u32) {{
                    if {compact} {{
                        self.__pending_total_edges_{name}.insert(self.root_{mor_name}({mor}(morphism)).0);
                    }}
                }}

                fn __prepare_total_{name}_edges(&mut self) {{
                    if !({compact}) {{ return; }}
                    for morphism in std::mem::take(&mut self.__pending_total_edges_{name}) {{
                        let morphism = self.root_{mor_name}({mor}(morphism));
                        if !self.__is_total_{name}_morphism(morphism.0)
                            && self.{dom}(morphism).is_some() && self.{cod}(morphism).is_some() {{
                            self.__materialize_compact_members();
                            return;
                        }}
                    }}
                }}

                fn __complete_total_{name}_members(&mut self) {{
                    {completion}
                }}
            "}?;
        }
        let prepare = names
            .iter()
            .map(|name| format!("self.__prepare_total_{name}_edges();"))
            .join("\n");
        let complete = names
            .iter()
            .map(|name| format!("self.__complete_total_{name}_members();"))
            .join("\n");
        writedoc! {f, "
            fn __prepare_total_member_policies(&mut self) {{ {prepare} }}
            fn __complete_total_members(&mut self) {{ {complete} }}
        "}
    })
}

use std::fmt::Display;

use convert_case::{Case, Casing};
use indoc::writedoc;

use super::{compact_eligibility, compact_indices, display_index_expr, RustGenCtx};
use crate::flat_eqlog::{FlatInRel, FlatRel, IndexSelection, QuerySpec};
use crate::fmt_util::FmtFn;
use crate::ram::RamProgram;

pub(super) fn methods<'a>(
    program: &'a RamProgram,
    selection: &'a IndexSelection,
    ctx: &'a RustGenCtx<'a>,
) -> impl Display + 'a {
    FmtFn(move |f| {
        for (_, ids) in ctx.signature().iter_model_decls() {
            let model = ids.type_;
            if !compact_indices::supports_model(model, ctx) {
                continue;
            }
            let name = ctx.type_name(model).to_case(Case::Snake);
            let mor_camel = ctx.type_name(ids.mor).to_case(Case::UpperCamel);
            let endpoint_ambiguity = [ids.dom, ids.cod].map(|func| {
                let rel = FlatInRel::Rel(FlatRel::Func(func));
                let query = QuerySpec::eval_func(func, ctx.signature());
                let index = selection.current_query(&rel, query);
                let tree = display_index_expr(&rel, index, ctx);
                format!("({tree}).get(morphism.0).is_some_and(|set| set.iter().take(2).count() > 1)")
            }).join(" || ");
            let eligibility =
                match compact_eligibility::rejection_reason(model, program, selection, ctx) {
                    Some(reason) => format!("assert!(false, {reason:?});"),
                    None => String::new(),
                };
            writedoc! {f, "
                /// Enables shared member storage for acyclic total inheritance.
                /// Requires a graph without assigned morphism endpoints.
                /// Existing member handles remain valid after activation.
                /// An operation requiring ordinary storage preserves existing handles.
                #[allow(dead_code)]
                pub fn enable_compact_{name}(&mut self) {{
                    if self.__compact_indices_{name}.is_some() {{ return; }}
                    {eligibility}
                    assert!(self.__total_members_{name}.is_empty(),
                        \"compact storage cannot be reenabled after total inheritance was materialized\");
                    self.close();
                    assert!(self.iter_{name}_mor_dom().next().is_none()
                        && self.iter_{name}_mor_cod().next().is_none(),
                        \"enable compact storage before assigning morphism endpoints\");
                    self.__enable_compact_{name}_indices();
                }}

                /// Inherits all current and future source members along this morphism.
                /// Total inheritance must be acyclic. Additional incoming images
                /// become available during closure, with proved overlaps shared.
                /// Registration is evaluator state and is not included in dynamic snapshots.
                /// Returns whether this registration or its inherited state changed.
                #[allow(dead_code)]
                pub fn inherit_total_{name}_members(&mut self, morphism: {mor_camel}) -> bool {{
                    let morphism = self.root_{name}_mor(morphism);
                    if self.__compact_indices_{name}.is_some() && ({endpoint_ambiguity}) {{
                        self.__check_total_{name}_morphism(morphism.0);
                        self.__materialize_compact_members();
                    }}
                    let source = self.{name}_mor_dom(morphism)
                        .expect(\"total inheritance requires a morphism source\");
                    let target = self.{name}_mor_cod(morphism)
                        .expect(\"total inheritance requires a morphism target\");
                    let refreshed = if self.__compact_indices_{name}.is_some() {{
                        if self.__total_members_{name}.contains(&morphism.0) {{
                            if self.__compact_adopted_{name}.contains(&morphism.0) {{
                                self.__compact_transport_{name}(morphism.0, source.0, target.0).unwrap_or(false)
                            }} else {{ false }}
                        }} else {{
                            self.__compact_register_{name}(morphism.0, source.0, target.0)
                        }}
                    }} else {{
                        self.__check_total_{name}_morphism(morphism.0);
                        false
                    }};
                    let registered = self.__total_members_{name}.insert(morphism.0);
                    if registered || refreshed {{ self.__closed = false; }}
                    registered || refreshed
                }}
            "}?;
        }
        Ok(())
    })
}

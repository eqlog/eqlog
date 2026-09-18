use std::iter::once;

use crate::algebra::signature::{MorphismMemberTypes, Signature};

use super::{
    iter_flat_rels, FlatIfStmt, FlatInRel, FlatOutRel, FlatRel, FlatRule, FlatThenStmt, FlatVar,
    QueryAge,
};

pub fn morphism_preservation_rules(signature: &Signature) -> Vec<FlatRule> {
    let mut rules = Vec::new();
    for (rel_index, rel) in iter_flat_rels(signature).enumerate() {
        let parents = match rel {
            FlatRel::Pred(pred) => &signature.pred(pred).parents,
            FlatRel::Func(func) => &signature.func(func).parents,
            // Allocation already assigns every image its unique parent chain.
            FlatRel::ModelMember(_) => continue,
        };
        let source: Vec<_> = rel
            .arity(signature)
            .into_iter()
            .enumerate()
            .map(|(i, typ)| FlatVar {
                name: format!("arg{i}").into(),
                typ,
            })
            .collect();

        for (depth, &model_type) in parents.iter().enumerate() {
            let ids = signature
                .ids_for_model_type(model_type)
                .expect("relation parents should be model types");
            let morphism = FlatVar {
                name: "morphism".into(),
                typ: ids.mor,
            };
            let codomain = FlatVar {
                name: "codomain".into(),
                typ: model_type,
            };
            let morphism_args: Vec<_> = source[..depth]
                .iter()
                .cloned()
                .chain(once(morphism))
                .collect();
            let mut premise = vec![FlatIfStmt {
                rel: FlatInRel::Rel(rel),
                args: source.clone(),
                age: QueryAge::All,
            }];
            for (func, value) in [
                (ids.dom, source[depth].clone()),
                (ids.cod, codomain.clone()),
            ] {
                let mut args = morphism_args.clone();
                args.push(value);
                premise.push(FlatIfStmt {
                    rel: FlatInRel::Rel(FlatRel::Func(func)),
                    args,
                    age: QueryAge::All,
                });
            }

            let mut target = source.clone();
            target[depth] = codomain;
            for (i, arg) in source.iter().enumerate().skip(depth + 1) {
                if !signature.type_(arg.typ).parents.contains(&model_type) {
                    continue;
                }
                let action = signature
                    .mor_app_func(MorphismMemberTypes {
                        morphism_type: ids.mor,
                        member_type: arg.typ,
                    })
                    .expect("morphisms should act on every descendant type");
                let image = FlatVar {
                    name: format!("image{i}").into(),
                    typ: arg.typ,
                };
                let mut args = morphism_args.clone();
                args.extend([arg.clone(), image.clone()]);
                // Requiring images in the premise keeps the action partial.
                // This also maps nested owners; ambient arguments are copied.
                premise.push(FlatIfStmt {
                    rel: FlatInRel::Rel(FlatRel::Func(action)),
                    args,
                    age: QueryAge::All,
                });
                target[i] = image;
            }
            rules.push(FlatRule {
                name: format!("__preserve_{rel_index}_{depth}"),
                premise,
                conclusion: vec![FlatThenStmt {
                    rel: FlatOutRel::Rel(rel),
                    args: target,
                }],
            });
        }
    }
    rules
}

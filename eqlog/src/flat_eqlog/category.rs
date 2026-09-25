use crate::algebra::signature::{FuncId, Signature, TypeId};

use super::{
    FlatIfStmt, FlatInRel, FlatOutRel, FlatRel, FlatRule, FlatThenStmt, FlatVar, QueryAge,
};

fn variable(name: &str, typ: TypeId) -> FlatVar {
    FlatVar {
        name: name.into(),
        typ,
    }
}

fn application(func: FuncId, parents: &[FlatVar], args: &[FlatVar]) -> FlatIfStmt {
    FlatIfStmt {
        rel: FlatInRel::Rel(FlatRel::Func(func)),
        args: parents.iter().chain(args).cloned().collect(),
        age: QueryAge::All,
    }
}

fn conclusion(stmt: FlatIfStmt) -> FlatThenStmt {
    let rel = match stmt.rel {
        FlatInRel::Rel(rel) => rel,
        FlatInRel::RelWithDiagonals { .. } | FlatInRel::Equality(_) | FlatInRel::TypeSet(_) => {
            panic!("category conclusions must be applications")
        }
    };
    FlatThenStmt {
        rel: FlatOutRel::Rel(rel),
        args: stmt.args,
    }
}

// Allocating morphisms here could make closure of a free category diverge.
pub fn category_rules(signature: &Signature) -> Vec<FlatRule> {
    let mut rules = Vec::new();
    for (_, ids) in signature.iter_model_decls() {
        let parents: Vec<_> = signature
            .type_(ids.type_)
            .parents
            .iter()
            .enumerate()
            .map(|(i, &typ)| variable(&format!("parent{i}"), typ))
            .collect();
        let a = variable("a", ids.type_);
        let i = variable("i", ids.mor);
        let f = variable("f", ids.mor);
        let g = variable("g", ids.mor);
        let h = variable("h", ids.mor);
        let fg = variable("fg", ids.mor);
        let gh = variable("gh", ids.mor);
        let composite = variable("composite", ids.mor);
        let app = |func, args: &[FlatVar]| application(func, &parents, args);
        let mut add = |premise: Vec<FlatIfStmt>, conclusions: Vec<FlatIfStmt>| {
            let index = rules.len();
            rules.push(FlatRule {
                name: format!("__category_{index}"),
                premise,
                conclusion: conclusions.into_iter().map(conclusion).collect(),
            });
        };
        add(
            vec![app(ids.id, &[a.clone(), i.clone()])],
            vec![
                app(ids.dom, &[i.clone(), a.clone()]),
                app(ids.cod, &[i.clone(), a.clone()]),
            ],
        );
        for (projection, args) in [
            (ids.dom, vec![i.clone(), f.clone(), f.clone()]),
            (ids.cod, vec![f.clone(), i.clone(), f.clone()]),
        ] {
            add(
                vec![
                    app(ids.id, &[a.clone(), i.clone()]),
                    app(projection, &[f.clone(), a.clone()]),
                ],
                vec![app(ids.comp, &args)],
            );
        }
        let comp = app(ids.comp, &[f.clone(), g.clone(), composite.clone()]);
        for ((left_func, left), (right_func, right)) in [
            ((ids.dom, f.clone()), (ids.dom, composite.clone())),
            ((ids.cod, g.clone()), (ids.cod, composite.clone())),
            ((ids.cod, f.clone()), (ids.dom, g.clone())),
        ] {
            let left = app(left_func, &[left, a.clone()]);
            let right = app(right_func, &[right, a.clone()]);
            add(vec![comp.clone(), left.clone()], vec![right.clone()]);
            add(vec![comp.clone(), right], vec![left]);
        }
        let fg_app = app(ids.comp, &[f.clone(), g.clone(), fg.clone()]);
        let gh_app = app(ids.comp, &[g.clone(), h.clone(), gh.clone()]);
        let left = app(ids.comp, &[fg, h, composite.clone()]);
        let right = app(ids.comp, &[f.clone(), gh, composite.clone()]);
        add(
            vec![fg_app.clone(), gh_app.clone(), left.clone()],
            vec![right.clone()],
        );
        add(vec![fg_app, gh_app, right], vec![left]);

        for (types, action) in signature.iter_mor_app_funcs() {
            if types.morphism_type != ids.mor {
                continue;
            }
            let x = variable("x", types.member_type);
            let y = variable("y", types.member_type);
            let z = variable("z", types.member_type);
            let mut member_parents = parents.clone();
            member_parents.push(a.clone());
            for (depth, &typ) in signature
                .type_(types.member_type)
                .parents
                .iter()
                .enumerate()
                .skip(member_parents.len())
            {
                member_parents.push(variable(&format!("member_parent{depth}"), typ));
            }
            member_parents.push(x.clone());
            add(
                vec![
                    app(ids.id, &[a.clone(), i.clone()]),
                    FlatIfStmt {
                        rel: FlatInRel::Rel(FlatRel::ModelMember(types.member_type)),
                        args: member_parents,
                        age: QueryAge::All,
                    },
                ],
                vec![app(action, &[i.clone(), x.clone(), x.clone()])],
            );
            let first = app(action, &[f.clone(), x.clone(), y.clone()]);
            let second = app(action, &[g.clone(), y, z.clone()]);
            let result = app(action, &[composite.clone(), x, z]);
            add(
                vec![comp.clone(), first.clone(), second.clone()],
                vec![result.clone()],
            );
            add(vec![comp.clone(), first, result], vec![second]);
        }
    }
    rules
}

use crate::model::*;
use crate::signature::*;
use crate::element::Element;
use std::iter::{FromIterator};


pub struct RelationInJoinPlan {
    pub relation_id: RelationId,
    pub equality_local_indices: Vec<usize>,
    pub equality_joined_indices: Vec<usize>,
    pub copied_indices: Vec<usize>,
}
pub struct JoinPlan(pub Vec<RelationInJoinPlan>);

fn visit_join_impl<V>(
    rels: &[(&[usize], &ProjectionIndex, &[usize])],
    rel_index: usize,
    projection_buffer: &mut Vec<Element>,
    current_joined_row_size: usize,
    joined_row: &mut [Element],
    visitor: &mut V
)
where
    for<'a> V: FnMut(&'a [Element])
{
    if rel_index == rels.len() {
        visitor(joined_row);
        return;
    }

    let (projection, index, copied_indices) = rels[rel_index];

    projection_buffer.resize(projection.len(), Element::default());
    project(projection, joined_row, &mut projection_buffer[..]);

    if let Some(matching_rows) = index.get(&projection_buffer[..]) {
        let next_joined_row_size = current_joined_row_size + copied_indices.len();
        for row in matching_rows {
            project(
                copied_indices,
                &row,
                &mut joined_row[current_joined_row_size .. next_joined_row_size]
            );
            visit_join_impl(
                rels,
                rel_index + 1,
                projection_buffer,
                next_joined_row_size,
                joined_row,
                visitor
            );
        }
    }
}

pub fn visit_join<V>(model: &Model, plan: &JoinPlan, mut visitor: V)
where
    for<'a> V: FnMut(&'a [Element])
{
    let JoinPlan(p) = plan;
    let rels: Vec<(&[usize], &ProjectionIndex, &[usize])> =
        Vec::from_iter(p.iter().map(|rijp| {
            let RelationId(rid) = rijp.relation_id;
            let model_indices = model.relations()[rid].projection_indices();
            let index = &model_indices[&rijp.equality_local_indices];
            (&rijp.equality_joined_indices[..], index, &rijp.copied_indices[..])
        }));

    let mut projection_buffer: Vec<Element> = Vec::with_capacity(
        p.iter().map(|rijp| rijp.copied_indices.len()).max().unwrap_or(0)
    );
    let joined_row_size = p.iter().map(|rijp| rijp.copied_indices.len()).sum();
    let mut joined_row: Vec<Element> = Vec::with_capacity(
        p.iter().map(|rijp| rijp.copied_indices.len()).sum()
    );
    joined_row.resize(joined_row_size, Element::default());

    visit_join_impl(
        &rels[..],
        0,
        &mut projection_buffer,
        0,
        &mut joined_row,
        &mut visitor
    );
}


#[cfg(test)]
mod test {
    use super::*;
    use std::collections::HashSet;

    fn compute_join(model: &Model, plan: &JoinPlan) -> HashSet<Row> {
        let mut result: HashSet<Row> = HashSet::new();
        visit_join(model, plan, |row| {
            result.insert(row.to_vec());
        });
        result
    }

    #[test]
    fn nullary_join() {
        let sig = Signature {
            sort_number: 2,
            relation_arities: vec![vec![SortId(0), SortId(1)]],
        };
        let model = Model::new(&sig);
        let plan = JoinPlan(vec![]);
        assert_eq!(compute_join(&model, &plan), hashset!{vec![]});
    }

    #[test]
    fn unary_join() {
        let sig = Signature {
            sort_number: 2,
            relation_arities: vec![vec![SortId(0), SortId(1)]],
        };

        let r = RelationId(0);

        let mut model = Model::new(&sig);

        let a0 = model.new_element(SortId(0));
        let a1 = model.new_element(SortId(0));
        let b0 = model.new_element(SortId(1));
        let b1 = model.new_element(SortId(1));

        model.extend_relation(RelationId(0), vec![
            vec![a0, b1],
            vec![a1, b0],
        ]);

        let plan = JoinPlan(vec![
            RelationInJoinPlan {
                relation_id: r,
                equality_local_indices: vec![],
                equality_joined_indices: vec![],
                copied_indices: vec![1, 0, 1],
            }
        ]);

        assert_eq!(compute_join(&model, &plan), hashset!{
            vec![b1, a0, b1],
            vec![b0, a1, b0],
        });
    }

    #[test]
    fn binary_self_join() {
        let sig = Signature {
            sort_number: 2,
            relation_arities: vec![vec![SortId(0), SortId(1)]],
        };

        let r = RelationId(0);

        let mut model = Model::new(&sig);

        let a0 = model.new_element(SortId(0));
        let a1 = model.new_element(SortId(0));
        let b0 = model.new_element(SortId(1));
        let b1 = model.new_element(SortId(1));

        model.extend_relation(RelationId(0), vec![
            vec![a0, b0],
            vec![a1, b0],
            vec![a1, b1],
        ]);

        let plan = JoinPlan(vec![
            RelationInJoinPlan {
                relation_id: r,
                equality_local_indices: vec![],
                equality_joined_indices: vec![],
                copied_indices: vec![1, 0],
            },
            RelationInJoinPlan {
                relation_id: r,
                equality_local_indices: vec![1],
                equality_joined_indices: vec![0],
                copied_indices: vec![0],
            },
        ]);

        model.add_projection_index(r, vec![1]);

        assert_eq!(compute_join(&model, &plan), hashset!{
            vec![b0, a0, a0],
            vec![b0, a0, a1],
            vec![b0, a1, a0],
            vec![b0, a1, a1],
            vec![b1, a1, a1],
        });
    }

    #[test]
    fn binary_join() {
        let sig = Signature {
            sort_number: 2,
            relation_arities: vec![
                vec![SortId(0), SortId(1)],
                vec![SortId(1), SortId(0)],
            ],
        };

        let r = RelationId(0);

        let mut model = Model::new(&sig);

        let a0 = model.new_element(SortId(0));
        let a1 = model.new_element(SortId(0));
        let b0 = model.new_element(SortId(1));
        let b1 = model.new_element(SortId(1));

        model.extend_relation(RelationId(0), vec![
            vec![a0, b0],
            vec![a1, b0],
            vec![a1, b1],
        ]);

        let plan = JoinPlan(vec![
            RelationInJoinPlan {
                relation_id: r,
                equality_local_indices: vec![],
                equality_joined_indices: vec![],
                copied_indices: vec![1, 0],
            },
            RelationInJoinPlan {
                relation_id: r,
                equality_local_indices: vec![1],
                equality_joined_indices: vec![0],
                copied_indices: vec![0],
            },
        ]);

        model.add_projection_index(r, vec![1]);

        assert_eq!(compute_join(&model, &plan), hashset!{
            vec![b0, a0, a0],
            vec![b0, a0, a1],
            vec![b0, a1, a0],
            vec![b0, a1, a1],
            vec![b1, a1, a1],
        });
    }
}

use crate::flat_eqlog::FlatInRel;

pub struct InputProjection {
    pub source: Vec<usize>,
    pub target: Vec<usize>,
    pub equalities: Vec<(usize, usize)>,
}

impl InputProjection {
    pub fn new(rel: &FlatInRel, order: &[usize], source: Vec<usize>) -> Self {
        let (target, equalities) = match rel {
            FlatInRel::RelWithDiagonals { equalities, .. } => {
                let columns: Vec<_> = equalities
                    .iter()
                    .enumerate()
                    .filter_map(|(i, &j)| (i == j).then_some(i))
                    .collect();
                let target = order.iter().map(|&i| columns[i]).collect();
                let equalities = equalities
                    .iter()
                    .enumerate()
                    .filter_map(|(i, &j)| (i != j).then_some((i, j)))
                    .collect();
                (target, equalities)
            }
            FlatInRel::Rel(_) | FlatInRel::TypeSet(_) => (order.to_vec(), Vec::new()),
            FlatInRel::Equality(_) => unreachable!("equalities have no tuple indices"),
        };
        Self {
            source,
            target,
            equalities,
        }
    }
}

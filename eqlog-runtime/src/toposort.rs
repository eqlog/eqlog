use std::collections::{BTreeMap, VecDeque};

use crate::{PrefixTree1, PrefixTree2};

#[derive(Debug, Copy, Clone)]
pub enum ToposortError {
    CycleDetected,
}

pub fn morphism_toposort(
    dom_new_order_1_0: &PrefixTree2,
    dom_old_order_1_0: &PrefixTree2,
    cod_new_order_0_1: &PrefixTree2,
    cod_old_order_0_1: &PrefixTree2,
    obj_old_order_0: &PrefixTree1,
    obj_new_order_0: &PrefixTree1,
) -> Result<Vec<u32>, ToposortError> {
    let get_cod = |mor: u32| -> Option<u32> {
        let cods: &PrefixTree1 = cod_new_order_0_1
            .get(mor)
            .or_else(|| cod_old_order_0_1.get(mor))?;
        let [cod] = cods.iter().next().unwrap();
        Some(cod)
    };

    let mut in_degree: BTreeMap<u32, u32> = obj_old_order_0
        .iter()
        .chain(obj_new_order_0.iter())
        .map(|[obj]| (obj, 0))
        .collect();

    for [_, mor] in dom_new_order_1_0.iter().chain(dom_old_order_1_0.iter()) {
        if let Some(cod) = get_cod(mor) {
            *in_degree.get_mut(&cod).unwrap() += 1;
        }
    }

    let mut queue: VecDeque<u32> = in_degree
        .iter()
        .filter_map(|(&obj, &in_deg)| if in_deg == 0 { Some(obj) } else { None })
        .collect();
    let mut ordered_mors: Vec<u32> = Vec::new();

    while let Some(obj) = queue.pop_front() {
        for dom_order_1_0 in [&dom_new_order_1_0, &dom_old_order_1_0] {
            let out_morphisms = match dom_order_1_0.get(obj) {
                Some(out_morphisms) => out_morphisms,
                None => continue,
            };

            for [out_morphism] in out_morphisms.iter() {
                let cod = match get_cod(out_morphism) {
                    Some(cod) => cod,
                    None => continue,
                };

                ordered_mors.push(out_morphism);
                let cod_in_degree = in_degree.get_mut(&cod).unwrap();
                *cod_in_degree -= 1;
                if *cod_in_degree == 0 {
                    in_degree.remove(&cod);
                    queue.push_back(cod);
                }
            }
        }
    }

    if !in_degree.is_empty() {
        return Err(ToposortError::CycleDetected);
    }

    Ok(ordered_mors)
}

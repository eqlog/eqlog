use crate::{Evaluator, Fixture, Phase, Workload};

pub fn pipeline<M: Evaluator>(scale: usize, phase: Phase) -> Box<dyn Workload> {
    let mut f = Fixture::<M>::new();
    let items = f.elements("Item", &[], 64 * scale);
    for &x in &items {
        f.insert("seed", &[x]);
    }
    for i in 0..24 {
        f.expect(&format!("step_{i}"), items.iter().map(|&x| vec![x]));
    }
    f.settle(phase);
    match phase {
        Phase::Initial | Phase::Unchanged => {}
        Phase::Incremental => {
            let added = f.elements("Item", &[], scale);
            for &x in &added {
                f.insert("seed", &[x]);
            }
            for i in 0..24 {
                f.expect(&format!("step_{i}"), added.iter().map(|&x| vec![x]));
            }
        }
    }
    Box::new(f)
}

pub fn independent<M: Evaluator>(scale: usize, phase: Phase) -> Box<dyn Workload> {
    let mut f = Fixture::<M>::new();
    for i in 0..16 {
        let items = f.elements("Item", &[], 16 * scale);
        for &x in &items {
            f.insert(&format!("seed_{i}"), &[x]);
        }
        f.expect(&format!("output_{i}"), items.iter().map(|&x| vec![x]));
    }
    f.settle(phase);
    match phase {
        Phase::Initial | Phase::Unchanged => {}
        Phase::Incremental => {
            let added = f.elements("Item", &[], scale);
            for &x in &added {
                f.insert("seed_7", &[x]);
            }
            f.expect("output_7", added.iter().map(|&x| vec![x]));
        }
    }
    Box::new(f)
}

pub fn model_chain<M: Evaluator>(scale: usize, phase: Phase) -> Box<dyn Workload> {
    graph::<M>(scale, phase, false)
}

pub fn model_cycle<M: Evaluator>(scale: usize, phase: Phase) -> Box<dyn Workload> {
    graph::<M>(scale, phase, true)
}

fn graph<M: Evaluator>(scale: usize, phase: Phase, cycle: bool) -> Box<dyn Workload> {
    let mut f = Fixture::<M>::new();
    let worlds = f.elements("World", &[], 16);
    let block = scale;
    let length = worlds.len() * block + 1;
    let initial = f.elements("Item", &[], length);
    let added = f.elements("Item", &[], length);
    for (i, &world) in worlds.iter().enumerate() {
        for lane in [&initial, &added] {
            for j in i * block..(i + 1) * block {
                f.insert("World::edge", &[world, lane[j], lane[j + 1]]);
            }
        }
        if i + 1 < worlds.len() || cycle {
            let target = worlds[(i + 1) % worlds.len()];
            let arrow = f.elements("WorldMor", &[], 1)[0];
            f.insert("world_mor_dom", &[arrow, world]);
            f.insert("world_mor_cod", &[arrow, target]);
        }
        let end = if cycle { length } else { (i + 1) * block + 1 };
        f.expect(
            "World::marked",
            initial[..end].iter().map(|&x| vec![world, x]),
        );
    }
    f.insert("World::seed", &[worlds[0], initial[0]]);
    f.settle(phase);
    match phase {
        Phase::Initial | Phase::Unchanged => {}
        Phase::Incremental => {
            let middle = worlds.len() / 2;
            f.insert("World::seed", &[worlds[middle], added[0]]);
            for (i, &world) in worlds.iter().enumerate() {
                if cycle || i >= middle {
                    let end = if cycle { length } else { (i + 1) * block + 1 };
                    f.expect(
                        "World::marked",
                        added[..end].iter().map(|&x| vec![world, x]),
                    );
                }
            }
        }
    }
    Box::new(f)
}

pub fn nested<M: Evaluator>(scale: usize, phase: Phase) -> Box<dyn Workload> {
    let mut f = Fixture::<M>::new();
    let parents = f.elements("Parent", &[], 4);
    let children: Vec<_> = parents
        .iter()
        .map(|&parent| f.elements("Parent::Child", &[parent], 4))
        .collect();
    let block = scale;
    let initial = f.elements("Item", &[], 4 * block + 1);
    let added = f.elements("Item", &[], 4 * block + 1);
    for (i, &parent) in parents.iter().enumerate() {
        for (j, &child) in children[i].iter().enumerate() {
            for lane in [&initial, &added] {
                for k in j * block..(j + 1) * block {
                    f.insert(
                        "Parent::Child::edge",
                        &[parent, child, lane[k], lane[k + 1]],
                    );
                }
            }
            if j + 1 < children[i].len() {
                let arrow = f.elements("Parent::ChildMor", &[parent], 1)[0];
                f.insert("Parent::child_mor_dom", &[parent, arrow, child]);
                f.insert(
                    "Parent::child_mor_cod",
                    &[parent, arrow, children[i][j + 1]],
                );
            }
            f.expect(
                "Parent::Child::reached",
                initial[..(j + 1) * block + 1]
                    .iter()
                    .map(|&x| vec![parent, child, x]),
            );
        }
        if i + 1 < parents.len() {
            let arrow = f.elements("ParentMor", &[], 1)[0];
            f.insert("parent_mor_dom", &[arrow, parent]);
            f.insert("parent_mor_cod", &[arrow, parents[i + 1]]);
            for j in 0..4 {
                f.insert(
                    "child_mor_app",
                    &[arrow, children[i][j], children[i + 1][j]],
                );
            }
        }
        f.expect("Parent::done", initial.iter().map(|&x| vec![parent, x]));
    }
    f.insert("Parent::seed", &[parents[0], initial[0]]);
    f.settle(phase);
    match phase {
        Phase::Initial | Phase::Unchanged => {}
        Phase::Incremental => {
            let parent = parents[3];
            f.insert("Parent::seed", &[parent, added[0]]);
            for (j, &child) in children[3].iter().enumerate() {
                f.expect(
                    "Parent::Child::reached",
                    added[..(j + 1) * block + 1]
                        .iter()
                        .map(|&x| vec![parent, child, x]),
                );
            }
            f.expect("Parent::done", added.iter().map(|&x| vec![parent, x]));
        }
    }
    Box::new(f)
}

pub fn equality<M: Evaluator>(scale: usize, phase: Phase) -> Box<dyn Workload> {
    let mut f = Fixture::<M>::new();
    let items = f.elements("Item", &[], 128 * scale);
    let left = f.elements("Value", &[], items.len());
    let right = f.elements("Value", &[], items.len());
    for (i, &item) in items.iter().enumerate() {
        f.insert("link", &[item, left[i]]);
        f.insert("wanted", &[right[i]]);
        if i % 2 == 0 {
            f.insert("merge", &[left[i], right[i]]);
            f.expect("done", [vec![item]]);
        }
    }
    f.settle(phase);
    match phase {
        Phase::Initial | Phase::Unchanged => {}
        Phase::Incremental => {
            for i in (1..items.len()).step_by(32) {
                f.insert("merge", &[left[i], right[i]]);
                f.expect("done", [vec![items[i]]]);
            }
        }
    }
    Box::new(f)
}

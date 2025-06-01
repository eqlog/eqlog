pub use crate::types::Unification;
use std::collections::BTreeMap;
use std::fmt::{self, Formatter};

#[unsafe(export_name = "eqlog_runtime_new_unification")]
pub extern "Rust" fn new_unification() -> Unification {
    Unification {
        parents: Vec::new(),
        sizes: Vec::new(),
    }
}

#[unsafe(export_name = "eqlog_runtime_root")]
pub extern "Rust" fn root(unification: &mut Unification, mut el: u32) -> u32 {
    let mut parent = unification.parents[el as usize];
    while el != parent {
        unification.parents[el as usize] = unification.parents[parent as usize];
        el = parent;
        parent = unification.parents[parent as usize];
    }
    el
}

#[unsafe(export_name = "eqlog_runtime_root_const")]
pub extern "Rust" fn root_const(unification: &Unification, mut el: u32) -> u32 {
    let mut parent = unification.parents[el as usize];
    while el != parent {
        el = parent;
        parent = unification.parents[el as usize];
    }
    el
}

#[unsafe(export_name = "eqlog_runtime_union_roots_into")]
pub extern "Rust" fn union_roots_into(unification: &mut Unification, lhs: u32, rhs: u32) {
    assert!(lhs == root(unification, lhs));
    assert!(rhs == root(unification, rhs));
    unification.parents[lhs as usize] = rhs;
}

#[unsafe(export_name = "eqlog_runtime_increase_size_to")]
pub extern "Rust" fn increase_size_to(unification: &mut Unification, new_size: usize) {
    assert!(new_size >= len(unification));
    assert!((u32::MAX as usize) > new_size);
    for i in len(unification)..new_size {
        unification.parents.push(i as u32);
    }
}

#[unsafe(export_name = "eqlog_runtime_len")]
pub extern "Rust" fn len(unification: &Unification) -> usize {
    unification.parents.len()
}

#[unsafe(export_name = "eqlog_runtime_classes")]
pub extern "Rust" fn classes(unification: &Unification) -> BTreeMap<u32, Vec<u32>> {
    let mut result = BTreeMap::new();
    for p in 0..unification.parents.len() {
        let p = p as u32;
        let root = root_const(unification, p);

        if !result.contains_key(&root) {
            result.insert(root, Vec::new());
        }
        let class_els = result.get_mut(&root).unwrap();

        if p != root {
            class_els.push(p);
        }
    }
    result
}

#[unsafe(export_name = "eqlog_runtime_clone_unification")]
pub extern "Rust" fn clone_unification(unification: &Unification) -> Unification {
    Unification {
        parents: unification.parents.clone(),
        sizes: unification.sizes.clone(),
    }
}

#[unsafe(export_name = "eqlog_runtime_fmt_unification")]
pub extern "Rust" fn fmt_unification(
    unification: &Unification,
    f: &mut Formatter<'_>,
) -> fmt::Result {
    write!(
        f,
        "Unification {{ parents: {:?}, sizes: {:?} }}",
        unification.parents, unification.sizes
    )
}

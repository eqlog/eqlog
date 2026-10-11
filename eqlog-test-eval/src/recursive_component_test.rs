use crate::recursive_component::RecursiveComponent;

#[test]
fn one_recursive_component_handles_incremental_inputs_and_equalities() {
    let mut m = RecursiveComponent::new();
    let nodes: Vec<_> = (0..16).map(|_| m.new_node()).collect();
    for pair in nodes[..8].windows(2).chain(nodes[8..].windows(2)) {
        m.insert_path(pair[0], pair[1]);
    }
    m.close();
    assert!(m.path(nodes[0], nodes[7]));
    assert!(m.path(nodes[8], nodes[15]));
    assert!(!m.path(nodes[0], nodes[15]));

    m.equate_node(nodes[7], nodes[8]);
    assert!(m.close_until(|m| m.path(nodes[0], nodes[15])));
    m.insert_path(nodes[15], nodes[0]);
    m.close();
    for &x in &nodes {
        for &y in &nodes {
            assert!(m.path(x, y));
        }
    }
}

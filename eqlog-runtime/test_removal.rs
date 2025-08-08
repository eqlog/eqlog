use std::collections::BTreeMap;
use crate::wbtree::map::WBTreeMap;

#[test]
fn test_removal_optimization() {
    let mut wb_map = WBTreeMap::new();
    let mut bt_map = BTreeMap::new();

    // Insert test data
    for i in 0..20 {
        wb_map.insert(i, i * 10);
        bt_map.insert(i, i * 10);
    }

    // Test removing existing keys
    for i in (0..20).step_by(3) {
        let wb_removed = wb_map.remove(&i);
        let bt_removed = bt_map.remove(&i);
        assert_eq!(wb_removed, bt_removed);
    }

    // Test removing non-existent keys
    for i in 100..105 {
        let wb_removed = wb_map.remove(&i);
        let bt_removed = bt_map.remove(&i);
        assert_eq!(wb_removed, bt_removed);
        assert_eq!(wb_removed, None);
    }

    // Verify final state matches
    assert_eq!(wb_map.len(), bt_map.len());
    for (k, v) in wb_map.iter() {
        assert_eq!(bt_map.get(k), Some(v));
    }
}
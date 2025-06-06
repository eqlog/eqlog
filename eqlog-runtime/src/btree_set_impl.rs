pub use crate::types::{
    BTreeSet0, BTreeSet1, BTreeSet2, BTreeSet3, BTreeSet4, BTreeSet5, BTreeSet6, BTreeSet7,
    BTreeSet8, BTreeSet9, BTreeSetIter0, BTreeSetIter1, BTreeSetIter2, BTreeSetIter3,
    BTreeSetIter4, BTreeSetIter5, BTreeSetIter6, BTreeSetIter7, BTreeSetIter8, BTreeSetIter9,
    BTreeSetRange0, BTreeSetRange1, BTreeSetRange2, BTreeSetRange3, BTreeSetRange4, BTreeSetRange5,
    BTreeSetRange6, BTreeSetRange7, BTreeSetRange8, BTreeSetRange9,
};
use std::collections::BTreeSet;
use std::ops::Bound;

#[unsafe(export_name = "eqlog_runtime_btree_set_new0")]
pub fn new0() -> BTreeSet0 {
    BTreeSet0(BTreeSet::new())
}
#[unsafe(export_name = "eqlog_runtime_btree_set_new1")]
pub fn new1() -> BTreeSet1 {
    BTreeSet1(BTreeSet::new())
}
#[unsafe(export_name = "eqlog_runtime_btree_set_new2")]
pub fn new2() -> BTreeSet2 {
    BTreeSet2(BTreeSet::new())
}
#[unsafe(export_name = "eqlog_runtime_btree_set_new3")]
pub fn new3() -> BTreeSet3 {
    BTreeSet3(BTreeSet::new())
}
#[unsafe(export_name = "eqlog_runtime_btree_set_new4")]
pub fn new4() -> BTreeSet4 {
    BTreeSet4(BTreeSet::new())
}
#[unsafe(export_name = "eqlog_runtime_btree_set_new5")]
pub fn new5() -> BTreeSet5 {
    BTreeSet5(BTreeSet::new())
}
#[unsafe(export_name = "eqlog_runtime_btree_set_new6")]
pub fn new6() -> BTreeSet6 {
    BTreeSet6(BTreeSet::new())
}
#[unsafe(export_name = "eqlog_runtime_btree_set_new7")]
pub fn new7() -> BTreeSet7 {
    BTreeSet7(BTreeSet::new())
}
#[unsafe(export_name = "eqlog_runtime_btree_set_new8")]
pub fn new8() -> BTreeSet8 {
    BTreeSet8(BTreeSet::new())
}
#[unsafe(export_name = "eqlog_runtime_btree_set_new9")]
pub fn new9() -> BTreeSet9 {
    BTreeSet9(BTreeSet::new())
}

#[unsafe(export_name = "eqlog_runtime_btree_set_contains0")]
pub fn contains0(set: &BTreeSet0, v: &[u32; 0]) -> bool {
    set.0.contains(v)
}
#[unsafe(export_name = "eqlog_runtime_btree_set_contains1")]
pub fn contains1(set: &BTreeSet1, v: &[u32; 1]) -> bool {
    set.0.contains(v)
}
#[unsafe(export_name = "eqlog_runtime_btree_set_contains2")]
pub fn contains2(set: &BTreeSet2, v: &[u32; 2]) -> bool {
    set.0.contains(v)
}
#[unsafe(export_name = "eqlog_runtime_btree_set_contains3")]
pub fn contains3(set: &BTreeSet3, v: &[u32; 3]) -> bool {
    set.0.contains(v)
}
#[unsafe(export_name = "eqlog_runtime_btree_set_contains4")]
pub fn contains4(set: &BTreeSet4, v: &[u32; 4]) -> bool {
    set.0.contains(v)
}
#[unsafe(export_name = "eqlog_runtime_btree_set_contains5")]
pub fn contains5(set: &BTreeSet5, v: &[u32; 5]) -> bool {
    set.0.contains(v)
}
#[unsafe(export_name = "eqlog_runtime_btree_set_contains6")]
pub fn contains6(set: &BTreeSet6, v: &[u32; 6]) -> bool {
    set.0.contains(v)
}
#[unsafe(export_name = "eqlog_runtime_btree_set_contains7")]
pub fn contains7(set: &BTreeSet7, v: &[u32; 7]) -> bool {
    set.0.contains(v)
}
#[unsafe(export_name = "eqlog_runtime_btree_set_contains8")]
pub fn contains8(set: &BTreeSet8, v: &[u32; 8]) -> bool {
    set.0.contains(v)
}
#[unsafe(export_name = "eqlog_runtime_btree_set_contains9")]
pub fn contains9(set: &BTreeSet9, v: &[u32; 9]) -> bool {
    set.0.contains(v)
}

#[unsafe(export_name = "eqlog_runtime_btree_set_insert0")]
pub fn insert0(set: &mut BTreeSet0, v: [u32; 0]) -> bool {
    set.0.insert(v)
}
#[unsafe(export_name = "eqlog_runtime_btree_set_insert1")]
pub fn insert1(set: &mut BTreeSet1, v: [u32; 1]) -> bool {
    set.0.insert(v)
}
#[unsafe(export_name = "eqlog_runtime_btree_set_insert2")]
pub fn insert2(set: &mut BTreeSet2, v: [u32; 2]) -> bool {
    set.0.insert(v)
}
#[unsafe(export_name = "eqlog_runtime_btree_set_insert3")]
pub fn insert3(set: &mut BTreeSet3, v: [u32; 3]) -> bool {
    set.0.insert(v)
}
#[unsafe(export_name = "eqlog_runtime_btree_set_insert4")]
pub fn insert4(set: &mut BTreeSet4, v: [u32; 4]) -> bool {
    set.0.insert(v)
}
#[unsafe(export_name = "eqlog_runtime_btree_set_insert5")]
pub fn insert5(set: &mut BTreeSet5, v: [u32; 5]) -> bool {
    set.0.insert(v)
}
#[unsafe(export_name = "eqlog_runtime_btree_set_insert6")]
pub fn insert6(set: &mut BTreeSet6, v: [u32; 6]) -> bool {
    set.0.insert(v)
}
#[unsafe(export_name = "eqlog_runtime_btree_set_insert7")]
pub fn insert7(set: &mut BTreeSet7, v: [u32; 7]) -> bool {
    set.0.insert(v)
}
#[unsafe(export_name = "eqlog_runtime_btree_set_insert8")]
pub fn insert8(set: &mut BTreeSet8, v: [u32; 8]) -> bool {
    set.0.insert(v)
}
#[unsafe(export_name = "eqlog_runtime_btree_set_insert9")]
pub fn insert9(set: &mut BTreeSet9, v: [u32; 9]) -> bool {
    set.0.insert(v)
}

#[unsafe(export_name = "eqlog_runtime_btree_set_remove0")]
pub fn remove0(set: &mut BTreeSet0, v: &[u32; 0]) -> bool {
    set.0.remove(v)
}
#[unsafe(export_name = "eqlog_runtime_btree_set_remove1")]
pub fn remove1(set: &mut BTreeSet1, v: &[u32; 1]) -> bool {
    set.0.remove(v)
}
#[unsafe(export_name = "eqlog_runtime_btree_set_remove2")]
pub fn remove2(set: &mut BTreeSet2, v: &[u32; 2]) -> bool {
    set.0.remove(v)
}
#[unsafe(export_name = "eqlog_runtime_btree_set_remove3")]
pub fn remove3(set: &mut BTreeSet3, v: &[u32; 3]) -> bool {
    set.0.remove(v)
}
#[unsafe(export_name = "eqlog_runtime_btree_set_remove4")]
pub fn remove4(set: &mut BTreeSet4, v: &[u32; 4]) -> bool {
    set.0.remove(v)
}
#[unsafe(export_name = "eqlog_runtime_btree_set_remove5")]
pub fn remove5(set: &mut BTreeSet5, v: &[u32; 5]) -> bool {
    set.0.remove(v)
}
#[unsafe(export_name = "eqlog_runtime_btree_set_remove6")]
pub fn remove6(set: &mut BTreeSet6, v: &[u32; 6]) -> bool {
    set.0.remove(v)
}
#[unsafe(export_name = "eqlog_runtime_btree_set_remove7")]
pub fn remove7(set: &mut BTreeSet7, v: &[u32; 7]) -> bool {
    set.0.remove(v)
}
#[unsafe(export_name = "eqlog_runtime_btree_set_remove8")]
pub fn remove8(set: &mut BTreeSet8, v: &[u32; 8]) -> bool {
    set.0.remove(v)
}
#[unsafe(export_name = "eqlog_runtime_btree_set_remove9")]
pub fn remove9(set: &mut BTreeSet9, v: &[u32; 9]) -> bool {
    set.0.remove(v)
}

#[unsafe(export_name = "eqlog_runtime_btree_set_clear0")]
pub fn clear0(set: &mut BTreeSet0) {
    set.0.clear()
}
#[unsafe(export_name = "eqlog_runtime_btree_set_clear1")]
pub fn clear1(set: &mut BTreeSet1) {
    set.0.clear()
}
#[unsafe(export_name = "eqlog_runtime_btree_set_clear2")]
pub fn clear2(set: &mut BTreeSet2) {
    set.0.clear()
}
#[unsafe(export_name = "eqlog_runtime_btree_set_clear3")]
pub fn clear3(set: &mut BTreeSet3) {
    set.0.clear()
}
#[unsafe(export_name = "eqlog_runtime_btree_set_clear4")]
pub fn clear4(set: &mut BTreeSet4) {
    set.0.clear()
}
#[unsafe(export_name = "eqlog_runtime_btree_set_clear5")]
pub fn clear5(set: &mut BTreeSet5) {
    set.0.clear()
}
#[unsafe(export_name = "eqlog_runtime_btree_set_clear6")]
pub fn clear6(set: &mut BTreeSet6) {
    set.0.clear()
}
#[unsafe(export_name = "eqlog_runtime_btree_set_clear7")]
pub fn clear7(set: &mut BTreeSet7) {
    set.0.clear()
}
#[unsafe(export_name = "eqlog_runtime_btree_set_clear8")]
pub fn clear8(set: &mut BTreeSet8) {
    set.0.clear()
}
#[unsafe(export_name = "eqlog_runtime_btree_set_clear9")]
pub fn clear9(set: &mut BTreeSet9) {
    set.0.clear()
}

#[unsafe(export_name = "eqlog_runtime_btree_set_is_empty0")]
pub fn is_empty0(set: &BTreeSet0) -> bool {
    set.0.is_empty()
}
#[unsafe(export_name = "eqlog_runtime_btree_set_is_empty1")]
pub fn is_empty1(set: &BTreeSet1) -> bool {
    set.0.is_empty()
}
#[unsafe(export_name = "eqlog_runtime_btree_set_is_empty2")]
pub fn is_empty2(set: &BTreeSet2) -> bool {
    set.0.is_empty()
}
#[unsafe(export_name = "eqlog_runtime_btree_set_is_empty3")]
pub fn is_empty3(set: &BTreeSet3) -> bool {
    set.0.is_empty()
}
#[unsafe(export_name = "eqlog_runtime_btree_set_is_empty4")]
pub fn is_empty4(set: &BTreeSet4) -> bool {
    set.0.is_empty()
}
#[unsafe(export_name = "eqlog_runtime_btree_set_is_empty5")]
pub fn is_empty5(set: &BTreeSet5) -> bool {
    set.0.is_empty()
}
#[unsafe(export_name = "eqlog_runtime_btree_set_is_empty6")]
pub fn is_empty6(set: &BTreeSet6) -> bool {
    set.0.is_empty()
}
#[unsafe(export_name = "eqlog_runtime_btree_set_is_empty7")]
pub fn is_empty7(set: &BTreeSet7) -> bool {
    set.0.is_empty()
}
#[unsafe(export_name = "eqlog_runtime_btree_set_is_empty8")]
pub fn is_empty8(set: &BTreeSet8) -> bool {
    set.0.is_empty()
}
#[unsafe(export_name = "eqlog_runtime_btree_set_is_empty9")]
pub fn is_empty9(set: &BTreeSet9) -> bool {
    set.0.is_empty()
}

#[unsafe(export_name = "eqlog_runtime_btree_set_iter0")]
pub fn iter0<'a>(set: &'a BTreeSet0) -> BTreeSetIter0<'a> {
    BTreeSetIter0(set.0.iter())
}
#[unsafe(export_name = "eqlog_runtime_btree_set_iter1")]
pub fn iter1<'a>(set: &'a BTreeSet1) -> BTreeSetIter1<'a> {
    BTreeSetIter1(set.0.iter())
}
#[unsafe(export_name = "eqlog_runtime_btree_set_iter2")]
pub fn iter2<'a>(set: &'a BTreeSet2) -> BTreeSetIter2<'a> {
    BTreeSetIter2(set.0.iter())
}
#[unsafe(export_name = "eqlog_runtime_btree_set_iter3")]
pub fn iter3<'a>(set: &'a BTreeSet3) -> BTreeSetIter3<'a> {
    BTreeSetIter3(set.0.iter())
}
#[unsafe(export_name = "eqlog_runtime_btree_set_iter4")]
pub fn iter4<'a>(set: &'a BTreeSet4) -> BTreeSetIter4<'a> {
    BTreeSetIter4(set.0.iter())
}
#[unsafe(export_name = "eqlog_runtime_btree_set_iter5")]
pub fn iter5<'a>(set: &'a BTreeSet5) -> BTreeSetIter5<'a> {
    BTreeSetIter5(set.0.iter())
}
#[unsafe(export_name = "eqlog_runtime_btree_set_iter6")]
pub fn iter6<'a>(set: &'a BTreeSet6) -> BTreeSetIter6<'a> {
    BTreeSetIter6(set.0.iter())
}
#[unsafe(export_name = "eqlog_runtime_btree_set_iter7")]
pub fn iter7<'a>(set: &'a BTreeSet7) -> BTreeSetIter7<'a> {
    BTreeSetIter7(set.0.iter())
}
#[unsafe(export_name = "eqlog_runtime_btree_set_iter8")]
pub fn iter8<'a>(set: &'a BTreeSet8) -> BTreeSetIter8<'a> {
    BTreeSetIter8(set.0.iter())
}
#[unsafe(export_name = "eqlog_runtime_btree_set_iter9")]
pub fn iter9<'a>(set: &'a BTreeSet9) -> BTreeSetIter9<'a> {
    BTreeSetIter9(set.0.iter())
}

#[unsafe(export_name = "eqlog_runtime_btree_set_iter_next0")]
pub fn iter_next0<'a>(iter: &mut BTreeSetIter0<'a>) -> Option<&'a [u32; 0]> {
    iter.0.next()
}
#[unsafe(export_name = "eqlog_runtime_btree_set_iter_next1")]
pub fn iter_next1<'a>(iter: &mut BTreeSetIter1<'a>) -> Option<&'a [u32; 1]> {
    iter.0.next()
}
#[unsafe(export_name = "eqlog_runtime_btree_set_iter_next2")]
pub fn iter_next2<'a>(iter: &mut BTreeSetIter2<'a>) -> Option<&'a [u32; 2]> {
    iter.0.next()
}
#[unsafe(export_name = "eqlog_runtime_btree_set_iter_next3")]
pub fn iter_next3<'a>(iter: &mut BTreeSetIter3<'a>) -> Option<&'a [u32; 3]> {
    iter.0.next()
}
#[unsafe(export_name = "eqlog_runtime_btree_set_iter_next4")]
pub fn iter_next4<'a>(iter: &mut BTreeSetIter4<'a>) -> Option<&'a [u32; 4]> {
    iter.0.next()
}
#[unsafe(export_name = "eqlog_runtime_btree_set_iter_next5")]
pub fn iter_next5<'a>(iter: &mut BTreeSetIter5<'a>) -> Option<&'a [u32; 5]> {
    iter.0.next()
}
#[unsafe(export_name = "eqlog_runtime_btree_set_iter_next6")]
pub fn iter_next6<'a>(iter: &mut BTreeSetIter6<'a>) -> Option<&'a [u32; 6]> {
    iter.0.next()
}
#[unsafe(export_name = "eqlog_runtime_btree_set_iter_next7")]
pub fn iter_next7<'a>(iter: &mut BTreeSetIter7<'a>) -> Option<&'a [u32; 7]> {
    iter.0.next()
}
#[unsafe(export_name = "eqlog_runtime_btree_set_iter_next8")]
pub fn iter_next8<'a>(iter: &mut BTreeSetIter8<'a>) -> Option<&'a [u32; 8]> {
    iter.0.next()
}
#[unsafe(export_name = "eqlog_runtime_btree_set_iter_next9")]
pub fn iter_next9<'a>(iter: &mut BTreeSetIter9<'a>) -> Option<&'a [u32; 9]> {
    iter.0.next()
}

#[unsafe(export_name = "eqlog_runtime_btree_set_range0")]
pub fn range0<'a>(
    set: &'a BTreeSet0,
    lower: Bound<[u32; 0]>,
    upper: Bound<[u32; 0]>,
) -> BTreeSetRange0<'a> {
    BTreeSetRange0(set.0.range((lower, upper)))
}
#[unsafe(export_name = "eqlog_runtime_btree_set_range1")]
pub fn range1<'a>(
    set: &'a BTreeSet1,
    lower: Bound<[u32; 1]>,
    upper: Bound<[u32; 1]>,
) -> BTreeSetRange1<'a> {
    BTreeSetRange1(set.0.range((lower, upper)))
}
#[unsafe(export_name = "eqlog_runtime_btree_set_range2")]
pub fn range2<'a>(
    set: &'a BTreeSet2,
    lower: Bound<[u32; 2]>,
    upper: Bound<[u32; 2]>,
) -> BTreeSetRange2<'a> {
    BTreeSetRange2(set.0.range((lower, upper)))
}
#[unsafe(export_name = "eqlog_runtime_btree_set_range3")]
pub fn range3<'a>(
    set: &'a BTreeSet3,
    lower: Bound<[u32; 3]>,
    upper: Bound<[u32; 3]>,
) -> BTreeSetRange3<'a> {
    BTreeSetRange3(set.0.range((lower, upper)))
}
#[unsafe(export_name = "eqlog_runtime_btree_set_range4")]
pub fn range4<'a>(
    set: &'a BTreeSet4,
    lower: Bound<[u32; 4]>,
    upper: Bound<[u32; 4]>,
) -> BTreeSetRange4<'a> {
    BTreeSetRange4(set.0.range((lower, upper)))
}
#[unsafe(export_name = "eqlog_runtime_btree_set_range5")]
pub fn range5<'a>(
    set: &'a BTreeSet5,
    lower: Bound<[u32; 5]>,
    upper: Bound<[u32; 5]>,
) -> BTreeSetRange5<'a> {
    BTreeSetRange5(set.0.range((lower, upper)))
}
#[unsafe(export_name = "eqlog_runtime_btree_set_range6")]
pub fn range6<'a>(
    set: &'a BTreeSet6,
    lower: Bound<[u32; 6]>,
    upper: Bound<[u32; 6]>,
) -> BTreeSetRange6<'a> {
    BTreeSetRange6(set.0.range((lower, upper)))
}
#[unsafe(export_name = "eqlog_runtime_btree_set_range7")]
pub fn range7<'a>(
    set: &'a BTreeSet7,
    lower: Bound<[u32; 7]>,
    upper: Bound<[u32; 7]>,
) -> BTreeSetRange7<'a> {
    BTreeSetRange7(set.0.range((lower, upper)))
}
#[unsafe(export_name = "eqlog_runtime_btree_set_range8")]
pub fn range8<'a>(
    set: &'a BTreeSet8,
    lower: Bound<[u32; 8]>,
    upper: Bound<[u32; 8]>,
) -> BTreeSetRange8<'a> {
    BTreeSetRange8(set.0.range((lower, upper)))
}
#[unsafe(export_name = "eqlog_runtime_btree_set_range9")]
pub fn range9<'a>(
    set: &'a BTreeSet9,
    lower: Bound<[u32; 9]>,
    upper: Bound<[u32; 9]>,
) -> BTreeSetRange9<'a> {
    BTreeSetRange9(set.0.range((lower, upper)))
}

#[unsafe(export_name = "eqlog_runtime_btree_set_range_next0")]
pub fn range_next0<'a>(range: &mut BTreeSetRange0<'a>) -> Option<&'a [u32; 0]> {
    range.0.next()
}
#[unsafe(export_name = "eqlog_runtime_btree_set_range_next1")]
pub fn range_next1<'a>(range: &mut BTreeSetRange1<'a>) -> Option<&'a [u32; 1]> {
    range.0.next()
}
#[unsafe(export_name = "eqlog_runtime_btree_set_range_next2")]
pub fn range_next2<'a>(range: &mut BTreeSetRange2<'a>) -> Option<&'a [u32; 2]> {
    range.0.next()
}
#[unsafe(export_name = "eqlog_runtime_btree_set_range_next3")]
pub fn range_next3<'a>(range: &mut BTreeSetRange3<'a>) -> Option<&'a [u32; 3]> {
    range.0.next()
}
#[unsafe(export_name = "eqlog_runtime_btree_set_range_next4")]
pub fn range_next4<'a>(range: &mut BTreeSetRange4<'a>) -> Option<&'a [u32; 4]> {
    range.0.next()
}
#[unsafe(export_name = "eqlog_runtime_btree_set_range_next5")]
pub fn range_next5<'a>(range: &mut BTreeSetRange5<'a>) -> Option<&'a [u32; 5]> {
    range.0.next()
}
#[unsafe(export_name = "eqlog_runtime_btree_set_range_next6")]
pub fn range_next6<'a>(range: &mut BTreeSetRange6<'a>) -> Option<&'a [u32; 6]> {
    range.0.next()
}
#[unsafe(export_name = "eqlog_runtime_btree_set_range_next7")]
pub fn range_next7<'a>(range: &mut BTreeSetRange7<'a>) -> Option<&'a [u32; 7]> {
    range.0.next()
}
#[unsafe(export_name = "eqlog_runtime_btree_set_range_next8")]
pub fn range_next8<'a>(range: &mut BTreeSetRange8<'a>) -> Option<&'a [u32; 8]> {
    range.0.next()
}
#[unsafe(export_name = "eqlog_runtime_btree_set_range_next9")]
pub fn range_next9<'a>(range: &mut BTreeSetRange9<'a>) -> Option<&'a [u32; 9]> {
    range.0.next()
}

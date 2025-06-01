pub use crate::types::{
    BTreeSet0, BTreeSet1, BTreeSet2, BTreeSet3, BTreeSet4, BTreeSet5, BTreeSet6, BTreeSet7,
    BTreeSet8, BTreeSet9, BTreeSetIter0, BTreeSetIter1, BTreeSetIter2, BTreeSetIter3,
    BTreeSetIter4, BTreeSetIter5, BTreeSetIter6, BTreeSetIter7, BTreeSetIter8, BTreeSetIter9,
    BTreeSetRange0, BTreeSetRange1, BTreeSetRange2, BTreeSetRange3, BTreeSetRange4, BTreeSetRange5,
    BTreeSetRange6, BTreeSetRange7, BTreeSetRange8, BTreeSetRange9,
};

unsafe extern "Rust" {
    #[link_name = "eqlog_runtime_btree_set_new0"]
    pub safe fn new0() -> BTreeSet0;

    #[link_name = "eqlog_runtime_btree_set_new1"]
    pub safe fn new1() -> BTreeSet1;

    #[link_name = "eqlog_runtime_btree_set_new2"]
    pub safe fn new2() -> BTreeSet2;

    #[link_name = "eqlog_runtime_btree_set_new3"]
    pub safe fn new3() -> BTreeSet3;

    #[link_name = "eqlog_runtime_btree_set_new4"]
    pub safe fn new4() -> BTreeSet4;

    #[link_name = "eqlog_runtime_btree_set_new5"]
    pub safe fn new5() -> BTreeSet5;

    #[link_name = "eqlog_runtime_btree_set_new6"]
    pub safe fn new6() -> BTreeSet6;

    #[link_name = "eqlog_runtime_btree_set_new7"]
    pub safe fn new7() -> BTreeSet7;

    #[link_name = "eqlog_runtime_btree_set_new8"]
    pub safe fn new8() -> BTreeSet8;

    #[link_name = "eqlog_runtime_btree_set_new9"]
    pub safe fn new9() -> BTreeSet9;

    #[link_name = "eqlog_runtime_btree_set_contains0"]
    pub safe fn contains0(set: &BTreeSet0, v: &[u32; 0]) -> bool;

    #[link_name = "eqlog_runtime_btree_set_contains1"]
    pub safe fn contains1(set: &BTreeSet1, v: &[u32; 1]) -> bool;

    #[link_name = "eqlog_runtime_btree_set_contains2"]
    pub safe fn contains2(set: &BTreeSet2, v: &[u32; 2]) -> bool;

    #[link_name = "eqlog_runtime_btree_set_contains3"]
    pub safe fn contains3(set: &BTreeSet3, v: &[u32; 3]) -> bool;

    #[link_name = "eqlog_runtime_btree_set_contains4"]
    pub safe fn contains4(set: &BTreeSet4, v: &[u32; 4]) -> bool;

    #[link_name = "eqlog_runtime_btree_set_contains5"]
    pub safe fn contains5(set: &BTreeSet5, v: &[u32; 5]) -> bool;

    #[link_name = "eqlog_runtime_btree_set_contains6"]
    pub safe fn contains6(set: &BTreeSet6, v: &[u32; 6]) -> bool;

    #[link_name = "eqlog_runtime_btree_set_contains7"]
    pub safe fn contains7(set: &BTreeSet7, v: &[u32; 7]) -> bool;

    #[link_name = "eqlog_runtime_btree_set_contains8"]
    pub safe fn contains8(set: &BTreeSet8, v: &[u32; 8]) -> bool;

    #[link_name = "eqlog_runtime_btree_set_contains9"]
    pub safe fn contains9(set: &BTreeSet9, v: &[u32; 9]) -> bool;

    #[link_name = "eqlog_runtime_btree_set_insert0"]
    pub safe fn insert0(set: &mut BTreeSet0, v: [u32; 0]) -> bool;

    #[link_name = "eqlog_runtime_btree_set_insert1"]
    pub safe fn insert1(set: &mut BTreeSet1, v: [u32; 1]) -> bool;

    #[link_name = "eqlog_runtime_btree_set_insert2"]
    pub safe fn insert2(set: &mut BTreeSet2, v: [u32; 2]) -> bool;

    #[link_name = "eqlog_runtime_btree_set_insert3"]
    pub safe fn insert3(set: &mut BTreeSet3, v: [u32; 3]) -> bool;

    #[link_name = "eqlog_runtime_btree_set_insert4"]
    pub safe fn insert4(set: &mut BTreeSet4, v: [u32; 4]) -> bool;

    #[link_name = "eqlog_runtime_btree_set_insert5"]
    pub safe fn insert5(set: &mut BTreeSet5, v: [u32; 5]) -> bool;

    #[link_name = "eqlog_runtime_btree_set_insert6"]
    pub safe fn insert6(set: &mut BTreeSet6, v: [u32; 6]) -> bool;

    #[link_name = "eqlog_runtime_btree_set_insert7"]
    pub safe fn insert7(set: &mut BTreeSet7, v: [u32; 7]) -> bool;

    #[link_name = "eqlog_runtime_btree_set_insert8"]
    pub safe fn insert8(set: &mut BTreeSet8, v: [u32; 8]) -> bool;

    #[link_name = "eqlog_runtime_btree_set_insert9"]
    pub safe fn insert9(set: &mut BTreeSet9, v: [u32; 9]) -> bool;

    #[link_name = "eqlog_runtime_btree_set_remove0"]
    pub safe fn remove0(set: &mut BTreeSet0, v: &[u32; 0]) -> bool;

    #[link_name = "eqlog_runtime_btree_set_remove1"]
    pub safe fn remove1(set: &mut BTreeSet1, v: &[u32; 1]) -> bool;

    #[link_name = "eqlog_runtime_btree_set_remove2"]
    pub safe fn remove2(set: &mut BTreeSet2, v: &[u32; 2]) -> bool;

    #[link_name = "eqlog_runtime_btree_set_remove3"]
    pub safe fn remove3(set: &mut BTreeSet3, v: &[u32; 3]) -> bool;

    #[link_name = "eqlog_runtime_btree_set_remove4"]
    pub safe fn remove4(set: &mut BTreeSet4, v: &[u32; 4]) -> bool;

    #[link_name = "eqlog_runtime_btree_set_remove5"]
    pub safe fn remove5(set: &mut BTreeSet5, v: &[u32; 5]) -> bool;

    #[link_name = "eqlog_runtime_btree_set_remove6"]
    pub safe fn remove6(set: &mut BTreeSet6, v: &[u32; 6]) -> bool;

    #[link_name = "eqlog_runtime_btree_set_remove7"]
    pub safe fn remove7(set: &mut BTreeSet7, v: &[u32; 7]) -> bool;

    #[link_name = "eqlog_runtime_btree_set_remove8"]
    pub safe fn remove8(set: &mut BTreeSet8, v: &[u32; 8]) -> bool;

    #[link_name = "eqlog_runtime_btree_set_remove9"]
    pub safe fn remove9(set: &mut BTreeSet9, v: &[u32; 9]) -> bool;

    #[link_name = "eqlog_runtime_btree_set_clear0"]
    pub safe fn clear0(set: &mut BTreeSet0);

    #[link_name = "eqlog_runtime_btree_set_clear1"]
    pub safe fn clear1(set: &mut BTreeSet1);

    #[link_name = "eqlog_runtime_btree_set_clear2"]
    pub safe fn clear2(set: &mut BTreeSet2);

    #[link_name = "eqlog_runtime_btree_set_clear3"]
    pub safe fn clear3(set: &mut BTreeSet3);

    #[link_name = "eqlog_runtime_btree_set_clear4"]
    pub safe fn clear4(set: &mut BTreeSet4);

    #[link_name = "eqlog_runtime_btree_set_clear5"]
    pub safe fn clear5(set: &mut BTreeSet5);

    #[link_name = "eqlog_runtime_btree_set_clear6"]
    pub safe fn clear6(set: &mut BTreeSet6);

    #[link_name = "eqlog_runtime_btree_set_clear7"]
    pub safe fn clear7(set: &mut BTreeSet7);

    #[link_name = "eqlog_runtime_btree_set_clear8"]
    pub safe fn clear8(set: &mut BTreeSet8);

    #[link_name = "eqlog_runtime_btree_set_clear9"]
    pub safe fn clear9(set: &mut BTreeSet9);

    #[link_name = "eqlog_runtime_btree_set_is_empty0"]
    pub safe fn is_empty0(set: &BTreeSet0) -> bool;

    #[link_name = "eqlog_runtime_btree_set_is_empty1"]
    pub safe fn is_empty1(set: &BTreeSet1) -> bool;

    #[link_name = "eqlog_runtime_btree_set_is_empty2"]
    pub safe fn is_empty2(set: &BTreeSet2) -> bool;

    #[link_name = "eqlog_runtime_btree_set_is_empty3"]
    pub safe fn is_empty3(set: &BTreeSet3) -> bool;

    #[link_name = "eqlog_runtime_btree_set_is_empty4"]
    pub safe fn is_empty4(set: &BTreeSet4) -> bool;

    #[link_name = "eqlog_runtime_btree_set_is_empty5"]
    pub safe fn is_empty5(set: &BTreeSet5) -> bool;

    #[link_name = "eqlog_runtime_btree_set_is_empty6"]
    pub safe fn is_empty6(set: &BTreeSet6) -> bool;

    #[link_name = "eqlog_runtime_btree_set_is_empty7"]
    pub safe fn is_empty7(set: &BTreeSet7) -> bool;

    #[link_name = "eqlog_runtime_btree_set_is_empty8"]
    pub safe fn is_empty8(set: &BTreeSet8) -> bool;

    #[link_name = "eqlog_runtime_btree_set_is_empty9"]
    pub safe fn is_empty9(set: &BTreeSet9) -> bool;

    #[link_name = "eqlog_runtime_btree_set_iter0"]
    pub safe fn iter0<'a>(set: &'a BTreeSet0) -> BTreeSetIter0<'a>;

    #[link_name = "eqlog_runtime_btree_set_iter1"]
    pub safe fn iter1<'a>(set: &'a BTreeSet1) -> BTreeSetIter1<'a>;

    #[link_name = "eqlog_runtime_btree_set_iter2"]
    pub safe fn iter2<'a>(set: &'a BTreeSet2) -> BTreeSetIter2<'a>;

    #[link_name = "eqlog_runtime_btree_set_iter3"]
    pub safe fn iter3<'a>(set: &'a BTreeSet3) -> BTreeSetIter3<'a>;

    #[link_name = "eqlog_runtime_btree_set_iter4"]
    pub safe fn iter4<'a>(set: &'a BTreeSet4) -> BTreeSetIter4<'a>;

    #[link_name = "eqlog_runtime_btree_set_iter5"]
    pub safe fn iter5<'a>(set: &'a BTreeSet5) -> BTreeSetIter5<'a>;

    #[link_name = "eqlog_runtime_btree_set_iter6"]
    pub safe fn iter6<'a>(set: &'a BTreeSet6) -> BTreeSetIter6<'a>;

    #[link_name = "eqlog_runtime_btree_set_iter7"]
    pub safe fn iter7<'a>(set: &'a BTreeSet7) -> BTreeSetIter7<'a>;

    #[link_name = "eqlog_runtime_btree_set_iter8"]
    pub safe fn iter8<'a>(set: &'a BTreeSet8) -> BTreeSetIter8<'a>;

    #[link_name = "eqlog_runtime_btree_set_iter9"]
    pub safe fn iter9<'a>(set: &'a BTreeSet9) -> BTreeSetIter9<'a>;

    #[link_name = "eqlog_runtime_btree_set_iter_next0"]
    pub safe fn iter_next0<'a>(iter: &mut BTreeSetIter0<'a>) -> Option<&'a [u32; 0]>;

    #[link_name = "eqlog_runtime_btree_set_iter_next1"]
    pub safe fn iter_next1<'a>(iter: &mut BTreeSetIter1<'a>) -> Option<&'a [u32; 1]>;

    #[link_name = "eqlog_runtime_btree_set_iter_next2"]
    pub safe fn iter_next2<'a>(iter: &mut BTreeSetIter2<'a>) -> Option<&'a [u32; 2]>;

    #[link_name = "eqlog_runtime_btree_set_iter_next3"]
    pub safe fn iter_next3<'a>(iter: &mut BTreeSetIter3<'a>) -> Option<&'a [u32; 3]>;

    #[link_name = "eqlog_runtime_btree_set_iter_next4"]
    pub safe fn iter_next4<'a>(iter: &mut BTreeSetIter4<'a>) -> Option<&'a [u32; 4]>;

    #[link_name = "eqlog_runtime_btree_set_iter_next5"]
    pub safe fn iter_next5<'a>(iter: &mut BTreeSetIter5<'a>) -> Option<&'a [u32; 5]>;

    #[link_name = "eqlog_runtime_btree_set_iter_next6"]
    pub safe fn iter_next6<'a>(iter: &mut BTreeSetIter6<'a>) -> Option<&'a [u32; 6]>;

    #[link_name = "eqlog_runtime_btree_set_iter_next7"]
    pub safe fn iter_next7<'a>(iter: &mut BTreeSetIter7<'a>) -> Option<&'a [u32; 7]>;

    #[link_name = "eqlog_runtime_btree_set_iter_next8"]
    pub safe fn iter_next8<'a>(iter: &mut BTreeSetIter8<'a>) -> Option<&'a [u32; 8]>;

    #[link_name = "eqlog_runtime_btree_set_iter_next9"]
    pub safe fn iter_next9<'a>(iter: &mut BTreeSetIter9<'a>) -> Option<&'a [u32; 9]>;

    #[link_name = "eqlog_runtime_btree_set_range0"]
    pub safe fn range0<'a>(
        set: &'a BTreeSet0,
        lower: std::ops::Bound<[u32; 0]>,
        upper: std::ops::Bound<[u32; 0]>,
    ) -> BTreeSetRange0<'a>;

    #[link_name = "eqlog_runtime_btree_set_range1"]
    pub safe fn range1<'a>(
        set: &'a BTreeSet1,
        lower: std::ops::Bound<[u32; 1]>,
        upper: std::ops::Bound<[u32; 1]>,
    ) -> BTreeSetRange1<'a>;

    #[link_name = "eqlog_runtime_btree_set_range2"]
    pub safe fn range2<'a>(
        set: &'a BTreeSet2,
        lower: std::ops::Bound<[u32; 2]>,
        upper: std::ops::Bound<[u32; 2]>,
    ) -> BTreeSetRange2<'a>;

    #[link_name = "eqlog_runtime_btree_set_range3"]
    pub safe fn range3<'a>(
        set: &'a BTreeSet3,
        lower: std::ops::Bound<[u32; 3]>,
        upper: std::ops::Bound<[u32; 3]>,
    ) -> BTreeSetRange3<'a>;

    #[link_name = "eqlog_runtime_btree_set_range4"]
    pub safe fn range4<'a>(
        set: &'a BTreeSet4,
        lower: std::ops::Bound<[u32; 4]>,
        upper: std::ops::Bound<[u32; 4]>,
    ) -> BTreeSetRange4<'a>;

    #[link_name = "eqlog_runtime_btree_set_range5"]
    pub safe fn range5<'a>(
        set: &'a BTreeSet5,
        lower: std::ops::Bound<[u32; 5]>,
        upper: std::ops::Bound<[u32; 5]>,
    ) -> BTreeSetRange5<'a>;

    #[link_name = "eqlog_runtime_btree_set_range6"]
    pub safe fn range6<'a>(
        set: &'a BTreeSet6,
        lower: std::ops::Bound<[u32; 6]>,
        upper: std::ops::Bound<[u32; 6]>,
    ) -> BTreeSetRange6<'a>;

    #[link_name = "eqlog_runtime_btree_set_range7"]
    pub safe fn range7<'a>(
        set: &'a BTreeSet7,
        lower: std::ops::Bound<[u32; 7]>,
        upper: std::ops::Bound<[u32; 7]>,
    ) -> BTreeSetRange7<'a>;

    #[link_name = "eqlog_runtime_btree_set_range8"]
    pub safe fn range8<'a>(
        set: &'a BTreeSet8,
        lower: std::ops::Bound<[u32; 8]>,
        upper: std::ops::Bound<[u32; 8]>,
    ) -> BTreeSetRange8<'a>;

    #[link_name = "eqlog_runtime_btree_set_range9"]
    pub safe fn range9<'a>(
        set: &'a BTreeSet9,
        lower: std::ops::Bound<[u32; 9]>,
        upper: std::ops::Bound<[u32; 9]>,
    ) -> BTreeSetRange9<'a>;

    #[link_name = "eqlog_runtime_btree_set_range_next0"]
    pub safe fn range_next0<'a>(range: &mut BTreeSetRange0<'a>) -> Option<&'a [u32; 0]>;

    #[link_name = "eqlog_runtime_btree_set_range_next1"]
    pub safe fn range_next1<'a>(range: &mut BTreeSetRange1<'a>) -> Option<&'a [u32; 1]>;

    #[link_name = "eqlog_runtime_btree_set_range_next2"]
    pub safe fn range_next2<'a>(range: &mut BTreeSetRange2<'a>) -> Option<&'a [u32; 2]>;

    #[link_name = "eqlog_runtime_btree_set_range_next3"]
    pub safe fn range_next3<'a>(range: &mut BTreeSetRange3<'a>) -> Option<&'a [u32; 3]>;

    #[link_name = "eqlog_runtime_btree_set_range_next4"]
    pub safe fn range_next4<'a>(range: &mut BTreeSetRange4<'a>) -> Option<&'a [u32; 4]>;

    #[link_name = "eqlog_runtime_btree_set_range_next5"]
    pub safe fn range_next5<'a>(range: &mut BTreeSetRange5<'a>) -> Option<&'a [u32; 5]>;

    #[link_name = "eqlog_runtime_btree_set_range_next6"]
    pub safe fn range_next6<'a>(range: &mut BTreeSetRange6<'a>) -> Option<&'a [u32; 6]>;

    #[link_name = "eqlog_runtime_btree_set_range_next7"]
    pub safe fn range_next7<'a>(range: &mut BTreeSetRange7<'a>) -> Option<&'a [u32; 7]>;

    #[link_name = "eqlog_runtime_btree_set_range_next8"]
    pub safe fn range_next8<'a>(range: &mut BTreeSetRange8<'a>) -> Option<&'a [u32; 8]>;

    #[link_name = "eqlog_runtime_btree_set_range_next9"]
    pub safe fn range_next9<'a>(range: &mut BTreeSetRange9<'a>) -> Option<&'a [u32; 9]>;
}

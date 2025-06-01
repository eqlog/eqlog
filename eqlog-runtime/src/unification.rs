pub use crate::types::Unification;
use std::fmt::{self, Formatter};

unsafe extern "Rust" {
    #[link_name = "eqlog_runtime_new_unification"]
    pub safe fn new_unification() -> Unification;
    #[link_name = "eqlog_runtime_root"]
    pub safe fn root(unification: &mut Unification, el: u32) -> u32;
    #[link_name = "eqlog_runtime_root_const"]
    pub safe fn root_const(unification: &Unification, el: u32) -> u32;
    #[link_name = "eqlog_runtime_union_roots_into"]
    pub safe fn union_roots_into(unification: &mut Unification, lhs: u32, rhs: u32);
    #[link_name = "eqlog_runtime_increase_size_to"]
    pub safe fn increase_size_to(unification: &mut Unification, new_size: usize);
    #[link_name = "eqlog_runtime_len"]
    pub safe fn len(unification: &Unification) -> usize;
    #[link_name = "eqlog_runtime_clone_unification"]
    pub safe fn clone_unification(unification: &Unification) -> Unification;
    #[link_name = "eqlog_runtime_fmt_unification"]
    pub safe fn fmt_unification(unification: &Unification, f: &mut Formatter<'_>) -> fmt::Result;
}

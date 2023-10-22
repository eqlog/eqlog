mod eqlog_util;
mod grammar_util;
mod semantics;
use lalrpop_util::lalrpop_mod;
lalrpop_mod!(grammar);
mod build;
mod error;
mod flat_ast;
mod flat_to_llam;
mod flatten;
mod index_selection;
mod llam;
mod rust_gen;
mod source_display;

#[cfg(all(feature = "tree-rebuild", feature = "tree-prebuilt"))]
std::compile_error!(
    "Features \"tree-rebuild\", \"tree-prebuilt\" and \"crates-prebuilt\" are mutually exclusive"
);
#[cfg(all(feature = "tree-rebuild", feature = "crates-prebuilt"))]
std::compile_error!(
    "Features \"tree-rebuild\", \"tree-prebuilt\" and \"crates-prebuilt\" are mutually exclusive"
);
#[cfg(all(feature = "tree-prebuilt", feature = "crates-prebuilt"))]
std::compile_error!(
    "Features \"tree-rebuild\", \"tree-prebuilt\" and \"crates-prebuilt\" are mutually exclusive"
);

#[cfg(not(any(
    feature = "tree-rebuild",
    feature = "tree-prebuilt",
    feature = "crates-prebuilt"
)))]
std::compile_error!(
    "One of features \"tree-rebuild\", \"tree-prebuilt\" and \"crates-prebuilt\" must be enabled"
);

#[cfg(feature = "crates-prebuilt")]
extern crate eqlog_eqlog_crates_prebuilt as eqlog_eqlog;
#[cfg(feature = "tree-prebuilt")]
extern crate eqlog_eqlog_tree_prebuilt as eqlog_eqlog;
#[cfg(feature = "tree-rebuild")]
extern crate eqlog_eqlog_tree_rebuild as eqlog_eqlog;

pub use crate::build::{process, process_root, Config};

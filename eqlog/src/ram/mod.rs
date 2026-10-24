//! Execution choices belong here so backends do not have to rediscover the
//! conditions that make an optimization sound. Query plans are temporary;
//! final functions contain explicit control flow and input/output interfaces.
//!
//! Blocks preserve lexical lifetimes as well as evaluation order. In
//! particular, reads must release their borrows before outputs are applied,
//! and proof restrictions must retain only the snapshots their scope needs.

mod adaptive;
mod ast;
mod compact;
mod evaluation;
mod functions;
mod indexed;
mod prepare;
mod sort;
mod strictness;
mod transport;

pub use adaptive::*;
pub use ast::*;
pub use compact::*;
pub use evaluation::*;
pub use functions::*;
pub use indexed::*;
pub use prepare::*;
pub use sort::*;
pub use strictness::*;
pub use transport::*;

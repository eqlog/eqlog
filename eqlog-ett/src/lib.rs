use eqlog_runtime::eqlog_mod;

eqlog_mod!(pub kernel);

mod checker;
mod syntax;

pub use checker::{check, Checked};
pub use syntax::Error;

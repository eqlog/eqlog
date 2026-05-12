use std::collections::BTreeMap;

use crate::error::*;
use crate::grammar_util::*;
use eqlog_eqlog::*;

pub fn check_eqlog(
    _eqlog: &Eqlog,
    _identifiers: &BTreeMap<Ident, String>,
    _locations: &BTreeMap<Loc, Location>,
) -> Result<(), CompileError> {
    Ok(())
}

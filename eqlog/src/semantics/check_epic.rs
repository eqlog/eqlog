use std::collections::BTreeMap;
use std::collections::BTreeSet;
use std::iter::once;

use crate::error::*;
use crate::grammar_util::*;
use eqlog_eqlog::*;

pub fn iter_surjectivity_errors<'a>(
    eqlog: &'a Eqlog,
    locations: &'a BTreeMap<Loc, Location>,
) -> impl 'a + Iterator<Item = CompileError> {
    let should_be_ok: BTreeSet<El> = eqlog.iter_el_should_be_surjective_ok().collect();
    let is_ok: BTreeSet<El> = eqlog.iter_el_is_surjective_ok().collect();
    should_be_ok
        .into_iter()
        .filter(move |el| !is_ok.contains(el))
        .flat_map(move |el| {
            let mut tms = eqlog.iter_semantic_el().filter_map(move |(tm, _, tm_el)| {
                if eqlog.are_equal_el(tm_el, el) {
                    Some(tm)
                } else {
                    None
                }
            });

            // The semantics are set up such that every new element (and only those need to be
            // surjective-ok) must be the semantics of at least one term. To make sure that we
            // don't accidentally suppress an error here, we take on term from the iterator (making
            // sure that there is one!) and put it back afterwards.
            let first_tm = tms
                .next()
                .expect("every new element should correspond to a term");
            let tms = once(first_tm).chain(tms);

            tms.map(|tm| {
                let loc = eqlog.term_node_loc(tm).unwrap();
                let location = *locations.get(&loc).unwrap();
                CompileError::SurjectivityViolation { location }
            })
        })
}

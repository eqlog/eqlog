use std::rc::Rc;

use crate::table::Table;
use crate::PrefixTree1;

/// A proof must cover every atom with the same source snapshot. Keeping the
/// surviving sources together preserves joins between different parents.
#[derive(Clone)]
pub struct MatchProofState {
    current: Vec<Table>,
    proofs: Vec<Vec<Table>>,
    columns: Rc<Vec<Vec<usize>>>,
    offsets: Vec<usize>,
    bindings: Vec<Option<u32>>,
    relevant: Rc<Vec<bool>>,
    covered: Option<bool>,
}

impl MatchProofState {
    pub fn new(
        current: Vec<Table>,
        mut proofs: Vec<Vec<Table>>,
        columns: Vec<Vec<usize>>,
    ) -> Option<Self> {
        assert_eq!(current.len(), columns.len());
        for (rows, columns) in current.iter().zip(&columns) {
            assert_eq!(rows.arity(), columns.len());
        }
        for proof in &proofs {
            assert_eq!(proof.len(), current.len());
            for (rows, current) in proof.iter().zip(&current) {
                assert_eq!(rows.arity(), current.arity());
            }
        }
        proofs.retain(|proof| proof.iter().all(|rows| !rows.is_empty()));
        if proofs.is_empty() {
            return None;
        }
        let offsets = vec![0; current.len()];
        let variables = columns.iter().flatten().copied().max().map_or(0, |n| n + 1);
        Some(Self {
            current,
            proofs,
            columns: Rc::new(columns),
            offsets,
            bindings: vec![None; variables],
            relevant: Rc::new(vec![true; variables]),
            covered: None,
        })
    }

    pub fn with_relevant_variables(mut self, variables: &[usize]) -> Self {
        let mut relevant = vec![false; self.bindings.len()];
        for &variable in variables {
            if let Some(value) = relevant.get_mut(variable) {
                *value = true;
            }
        }
        self.relevant = Rc::new(relevant);
        self.covered = None;
        self
    }

    pub fn restrict(&self, variable: usize, value: u32) -> Option<Self> {
        let mut result = Self {
            current: self.current.clone(),
            proofs: Vec::new(),
            columns: self.columns.clone(),
            offsets: self.offsets.clone(),
            bindings: self.bindings.clone(),
            relevant: self.relevant.clone(),
            covered: Some(false),
        };
        if let Some(binding) = result.bindings.get_mut(variable) {
            if let Some(previous) = binding {
                assert_eq!(*previous, value, "a matching variable has one binding");
            }
            *binding = Some(value);
        }
        for atom in 0..result.current.len() {
            let columns = &result.columns[atom];
            let offset = &mut result.offsets[atom];
            while let Some(value) = columns
                .get(*offset)
                .and_then(|&variable| result.bindings[variable])
            {
                result.current[atom] = restrict_rows(&result.current[atom], value);
                *offset += 1;
            }
        }
        let empty = result.current.iter().any(Table::is_empty);
        for source in &self.proofs {
            let mut proof = Vec::with_capacity(source.len());
            let mut covered = true;
            for (atom, rows) in source.iter().enumerate() {
                let mut rows = rows.clone();
                for &variable in &result.columns[atom][self.offsets[atom]..result.offsets[atom]] {
                    rows = restrict_rows(&rows, result.bindings[variable].unwrap());
                }
                if rows.is_empty() {
                    break;
                }
                if covered && !empty {
                    covered = projected_subset(
                        &result.current[atom],
                        &rows,
                        &result.columns[atom][result.offsets[atom]..],
                        &result.bindings,
                        &result.relevant,
                    );
                }
                proof.push(rows);
            }
            if proof.len() != source.len() {
                continue;
            }
            if covered {
                // One complete certificate proves the entire remaining branch.
                // Later parents cannot create work inside that branch.
                result.proofs.clear();
                result.proofs.push(proof);
                result.covered = Some(true);
                return Some(result);
            }
            result.proofs.push(proof);
        }
        (!result.proofs.is_empty()).then_some(result)
    }

    pub fn is_covered(&self) -> bool {
        if let Some(covered) = self.covered {
            return covered;
        }
        self.current.iter().any(Table::is_empty)
            || self.proofs.iter().any(|proof| {
                self.current
                    .iter()
                    .zip(proof)
                    .enumerate()
                    .all(|(atom, (current, proved))| {
                        projected_subset(
                            current,
                            proved,
                            &self.columns[atom][self.offsets[atom]..],
                            &self.bindings,
                            &self.relevant,
                        )
                    })
            })
    }

    /// Subtract before iterating the final variable, so already proved products
    /// are never expanded into complete matches. Sources may overlap.
    pub fn uncovered_keys(&self, variable: usize) -> Option<PrefixTree1> {
        let mut current: Option<PrefixTree1> = None;
        for (atom, rows) in self.current.iter().enumerate() {
            let remaining = &self.columns[atom][self.offsets[atom]..];
            if !remaining
                .iter()
                .any(|&v| self.relevant[v] && self.bindings[v].is_none())
            {
                if !has_match(rows, remaining, &self.bindings, None) {
                    return Some(PrefixTree1::new());
                }
                continue;
            }
            if remaining
                .iter()
                .any(|&v| self.relevant[v] && self.bindings[v].is_none() && v != variable)
            {
                return None;
            }
            let rows = projected_keys(rows, remaining, &self.bindings, variable);
            current = Some(match current {
                Some(current) => current.intersection(&rows),
                None => rows,
            });
        }
        let mut current = current?;
        for proof in &self.proofs {
            let mut covered: Option<PrefixTree1> = None;
            for (atom, rows) in proof.iter().enumerate() {
                let remaining = &self.columns[atom][self.offsets[atom]..];
                if !remaining
                    .iter()
                    .any(|&v| self.relevant[v] && self.bindings[v].is_none())
                {
                    if !has_match(rows, remaining, &self.bindings, None) {
                        covered = Some(PrefixTree1::new());
                        break;
                    }
                    continue;
                }
                let rows = projected_keys(rows, remaining, &self.bindings, variable);
                covered = Some(match covered {
                    Some(covered) => covered.intersection(&rows),
                    None => rows,
                });
            }
            current = current.difference(&covered.expect("a variable has a remaining atom"));
            if current.is_empty() {
                break;
            }
        }
        Some(current)
    }
}

fn restrict_rows(rows: &Table, value: u32) -> Table {
    rows.first_column(value)
        .unwrap_or_else(|| Table::new(rows.arity().checked_sub(1).unwrap()))
}

fn has_match(
    rows: &Table,
    columns: &[usize],
    bindings: &[Option<u32>],
    extra: Option<(usize, u32)>,
) -> bool {
    if rows.is_empty() {
        return false;
    }
    let constrained = |variable| {
        extra
            .filter(|&(v, _)| v == variable)
            .map(|(_, value)| value)
            .or(bindings[variable])
    };
    if !columns.iter().any(|&v| constrained(v).is_some()) {
        return true;
    }
    let (&variable, rest) = columns.split_first().unwrap();
    if let Some(value) = constrained(variable) {
        return rows
            .first_column(value)
            .is_some_and(|rows| has_match(&rows, rest, bindings, extra));
    }
    rows.first_columns()
        .any(|(_, rows)| has_match(&rows, rest, bindings, extra))
}

fn projected_keys(
    rows: &Table,
    columns: &[usize],
    bindings: &[Option<u32>],
    variable: usize,
) -> PrefixTree1 {
    if rows.is_empty() {
        return PrefixTree1::new();
    }
    let (&first, rest) = columns
        .split_first()
        .expect("a remaining matching variable");
    if let Some(value) = bindings[first] {
        return projected_keys(&restrict_rows(rows, value), rest, bindings, variable);
    }
    if first == variable {
        if rest.is_empty() {
            return PrefixTree1::try_from(rows).expect("one remaining column");
        }
        let mut result = PrefixTree1::new();
        for (key, suffix) in rows.first_columns() {
            if has_match(&suffix, rest, bindings, Some((variable, key))) {
                result.insert([key]);
            }
        }
        return result;
    }
    let mut result = PrefixTree1::new();
    for (_, suffix) in rows.first_columns() {
        result = result.union(&projected_keys(&suffix, rest, bindings, variable));
    }
    result
}

fn projected_subset(
    current: &Table,
    proved: &Table,
    columns: &[usize],
    bindings: &[Option<u32>],
    relevant: &[bool],
) -> bool {
    if current.is_subset(proved) {
        return true;
    }
    if columns
        .iter()
        .all(|&v| relevant[v] && bindings[v].is_none())
    {
        return false;
    }
    if !columns
        .iter()
        .any(|&v| relevant[v] && bindings[v].is_none())
    {
        return !has_match(current, columns, bindings, None)
            || has_match(proved, columns, bindings, None);
    }
    let (&variable, rest) = columns.split_first().unwrap();
    if let Some(value) = bindings[variable] {
        return projected_subset(
            &restrict_rows(current, value),
            &restrict_rows(proved, value),
            rest,
            bindings,
            relevant,
        );
    }
    if !relevant[variable] {
        let mut current_union = Table::new(current.arity() - 1);
        let mut proved_union = Table::new(proved.arity() - 1);
        for (_, rows) in current.first_columns() {
            current_union = current_union.union(&rows);
        }
        for (_, rows) in proved.first_columns() {
            proved_union = proved_union.union(&rows);
        }
        return projected_subset(&current_union, &proved_union, rest, bindings, relevant);
    }
    current.difference(proved).first_columns().all(|(key, _)| {
        projected_subset(
            &restrict_rows(current, key),
            &restrict_rows(proved, key),
            rest,
            bindings,
            relevant,
        )
    })
}

use crate::indirect_ast::*;
use std::collections::HashMap;
use std::ops::{Index, IndexMut};
use std::marker::PhantomData;

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct IdValMap<Id, Val>
where
    Id : From<usize> + Into<usize> + Copy,
{
    table: Vec<Val>,
    phantom: PhantomData<Id>,
}

impl<Id, Val> IdValMap<Id, Val>
where
    Id: From<usize> + Into<usize> + Copy,
    Val: Clone,
{
    pub fn new(size: usize, initial_value: Val) -> Self {
        let mut table = Vec::new();
        table.resize(size, initial_value);
        IdValMap {
            table,
            phantom: PhantomData,
        }
    }
}
impl<Id, Val> IdValMap<Id, Val>
where
    Id: From<usize> + Into<usize> + Copy,
{
    pub fn from_table(table: Vec<Val>) -> Self {
        IdValMap{
            table,
            phantom: PhantomData,
        }
    }
    pub fn iter(&self) -> impl Iterator<Item=(Id, &Val)> {
        self.table.iter().enumerate().map(|(i, v)| (Id::from(i), v))
    }
}

impl<Id, Val> Index<Id> for IdValMap<Id, Val>
where
    Id: From<usize> + Into<usize> + Copy,
{
    type Output = Val;
    fn index(&self, i: Id) -> &Val {
        &self.table[i.into()]
    }
}

impl<Id, Val> IndexMut<Id> for IdValMap<Id, Val>
where
    Id : From<usize> + Into<usize> + Copy
{
    fn index_mut(&mut self, i: Id) -> &mut Val {
        &mut self.table[i.into()]
    }
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct IdIdMap<FromId, ToId>
where
    FromId: From<usize> + Into<usize> + Copy,
    ToId: From<usize> + Into<usize> + Copy,
{
    table: Vec<ToId>,
    range_end: usize,
    phantom: PhantomData<FromId>,
}

impl<FromId, ToId> IdIdMap<FromId, ToId>
where
    FromId: From<usize> + Into<usize> + Copy,
    ToId: From<usize> + Into<usize> + Copy,
{
    pub fn new(map: IdValMap<FromId, ToId>) -> Self {
        let range_max: Option<usize> = map.table.iter().copied().map(|id| id.into()).max();
        let range_end: usize = range_max.map(|max| max + 1).unwrap_or(0);
        IdIdMap {
            table: map.table,
            phantom: PhantomData,
            range_end
        }
    }
    pub fn len(&self) -> usize {
        self.table.len()
    }
    pub fn range_end(&self) -> usize {
        self.range_end
    }
    pub fn iter<'a>(&'a self) -> impl 'a + Iterator<Item=(FromId, ToId)> {
        self.table.iter().copied().enumerate().map(|(i, j)| (FromId::from(i), j))
    }
}

impl<FromId, ToId> Index<FromId> for IdIdMap<FromId, ToId>
where
    FromId: From<usize> + Into<usize> + Copy,
    ToId: From<usize> + Into<usize> + Copy,
{
    type Output = ToId;
    fn index(&self, i: FromId) -> &ToId {
        &self.table[i.into()]
    }
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct TermUnification<'a> {
    universe: &'a TermUniverse,
    parents: Vec<usize>,
}

impl<'a> TermUnification<'a> {
    pub fn new(universe: &'a TermUniverse) -> TermUnification<'a> {
        TermUnification {
            universe: universe,
            parents: (0 .. universe.len()).collect(),
        }
    }
    pub fn union(&mut self, lhs: Term, rhs: Term) {
        let lhs_root = self.root(lhs);
        let rhs_root = self.root(rhs);
        self.parents[lhs_root.0] = rhs_root.0;
    }
    pub fn root(&mut self, tm: Term) -> Term {
        let mut i = tm.0;
        while i != self.parents[i] {
            i = self.parents[i];
        }
        let root = i;
        i = tm.0;
        while i != self.parents[i] {
            let j = self.parents[i];
            self.parents[i] = root;
            i = j;
        }
        Term(root)
    }
    pub fn congruence_closure(&mut self) {
        let mut vars: HashMap<&str, Term> = HashMap::new();
        for (tm, data) in self.universe.iter_terms() {
            if let TermData::Variable(s) = data {
                let prev_tm = vars.insert(s, tm);
                if let Some(prev_tm) = prev_tm {
                    self.union(prev_tm, tm);
                }
            }
        }

        let mut dirty = true;
        while dirty {
            dirty = false;
            let mut apps: HashMap<(&str, Vec<Term>), Term> = HashMap::new();
            for (tm, data) in self.universe.iter_terms() {
                if let TermData::Application(f, args) = data {
                    let arg_roots = args.iter().map(|arg| self.root(*arg)).collect();
                    let prev_tm = apps.insert((f, arg_roots), tm);
                    if let Some(prev_tm) = prev_tm {
                        let tm_root = self.root(tm);
                        let prev_tm_root = self.root(prev_tm);
                        if tm_root != prev_tm_root {
                            self.union(tm_root, prev_tm_root);
                            dirty = true;
                        }
                    }
                }
            }
        }
    }
    pub fn tabulate<Id>(&mut self) -> IdIdMap<Term, Id>
    where
        Id: From<usize> + Into<usize> + Copy,
    {
        let mut table: IdValMap<Term, Id> = IdValMap::new(self.parents.len(), Id::from(usize::MAX));

        let mut next_id = 0;
        for (tm, _) in self.universe.iter_terms() {
            if tm == self.root(tm) {
                table[tm] = Id::from(next_id);
                next_id += 1;
            }
        }
        for (tm, _) in self.universe.iter_terms() {
            table[tm] = table[self.root(tm)];
        }
        IdIdMap::new(table)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_initial_state() {
        use TermData::*;
        let mut univ = TermUniverse::new();
        let t0 = univ.new_term(Wildcard);
        let t1 = univ.new_term(Variable("123".to_string()));
        let t2 = univ.new_term(Application("f".to_string(), vec![t0, t1]));
        let t3 = univ.new_term(Wildcard);
        let t4 = univ.new_term(Wildcard);
        let t5 = univ.new_term(Wildcard);
        let mut unif = TermUnification::new(&univ);
        assert_eq!(unif.root(t0), t0);
        assert_eq!(unif.root(t1), t1);
        assert_eq!(unif.root(t2), t2);
        assert_eq!(unif.root(t3), t3);
        assert_eq!(unif.root(t4), t4);
        assert_eq!(unif.root(t5), t5);
    }

    #[test]
    fn test_union_root() {
        use TermData::*;
        let mut univ = TermUniverse::new();
        let t0 = univ.new_term(Wildcard);
        let t1 = univ.new_term(Variable("123".to_string()));
        let t2 = univ.new_term(Application("f".to_string(), vec![t0, t1]));
        let t3 = univ.new_term(Wildcard);
        let t4 = univ.new_term(Wildcard);
        let t5 = univ.new_term(Wildcard);

        let mut unif = TermUnification::new(&univ);
        unif.union(t0, t1);
        assert_eq!(unif.root(t0), unif.root(t1));
        assert!(unif.root(t0) == t0 || unif.root(t0) == t1);

        unif = TermUnification::new(&univ);
        unif.union(t0, t1);
        unif.union(t1, t2);
        assert_eq!(unif.root(t0), unif.root(t2));
        assert_eq!(unif.root(t1), unif.root(t2));

        unif = TermUnification::new(&univ);
        unif.union(t0, t1);
        unif.union(t2, t1);
        assert_eq!(unif.root(t2), unif.root(t0));
        assert_eq!(unif.root(t0), unif.root(t1));

        unif = TermUnification::new(&univ);
        unif.union(t0, t1);
        unif.union(t1, t2);
        unif.union(t3, t4);
        unif.union(t4, t5);
        unif.union(t1, t4);
        assert_eq!(unif.root(t2), unif.root(t3));
    }

    #[test]
    fn test_variable_congruence() {
        use TermData::*;
        let mut univ = TermUniverse::new();
        let t0 = univ.new_term(Wildcard);
        let t1 = univ.new_term(Wildcard);
        let t2 = univ.new_term(Variable("123".to_string()));
        let t3 = univ.new_term(Variable("abc".to_string()));
        let t4 = univ.new_term(Variable("123".to_string()));
        let t5 = univ.new_term(Application("123".to_string(), vec![t0, t2]));

        let mut unif = TermUnification::new(&univ);
        unif.union(t0, t1);
        unif.congruence_closure();
        assert_eq!(unif.root(t0), unif.root(t1));
        assert_eq!(unif.root(t3), t3);
        assert_eq!(unif.root(t2), unif.root(t4));
        assert_eq!(unif.root(t5), t5);
    }

    #[test]
    fn test_application_congruence() {
        use TermData::*;
        let mut univ = TermUniverse::new();
        let t0 = univ.new_term(Wildcard);
        let t1 = univ.new_term(Wildcard);
        let t2 = univ.new_term(Variable("123".to_string()));
        let _ = univ.new_term(Variable("abc".to_string()));
        let t4 = univ.new_term(Variable("123".to_string()));
        let t5 = univ.new_term(Application("123".to_string(), vec![t0, t2]));
        let t6 = univ.new_term(Application("abc".to_string(), vec![t0, t2]));
        let t7 = univ.new_term(Application("123".to_string(), vec![t0, t4]));
        let t8 = univ.new_term(Application("abc".to_string(), vec![t1, t2]));
        let t9 = univ.new_term(Application("xyz".to_string(), vec![t1, t6]));
        let t10 = univ.new_term(Application("xyz".to_string(), vec![t1, t8]));

        let mut unif = TermUnification::new(&univ);
        unif.union(t0, t1);
        unif.congruence_closure();
        assert_eq!(unif.root(t0), unif.root(t1));
        assert!(unif.root(t0) == t0 || unif.root(t0) == t1);
        assert_eq!(unif.root(t2), unif.root(t4));
        assert!(unif.root(t2) == t2 || unif.root(t2) == t4);
        assert_eq!(unif.root(t5), unif.root(t7));
        assert!(unif.root(t5) == t5 || unif.root(t5) == t7);
        assert_eq!(unif.root(t6), unif.root(t8));
        assert!(unif.root(t6) == t6 || unif.root(t6) == t8);
        assert_eq!(unif.root(t9), unif.root(t10));
        assert!(unif.root(t9) == t9 || unif.root(t9) == t10);
    }

    #[test]
    fn test_tabulate() {
        use TermData::*;
        let mut univ = TermUniverse::new();
        let t0 = univ.new_term(Wildcard);
        let t1 = univ.new_term(Variable("123".to_string()));
        let t2 = univ.new_term(Application("f".to_string(), vec![t0, t1]));
        let t3 = univ.new_term(Wildcard);
        let t4 = univ.new_term(Wildcard);
        let t5 = univ.new_term(Wildcard);
        let _ = univ.new_term(Application("g".to_string(), vec![t0, t2]));

        let mut unif = TermUnification::new(&univ);
        unif.union(t0, t1);

        unif.union(t3, t4);
        unif.union(t4, t5);

        assert_eq!(unif.tabulate(), IdIdMap::new(IdValMap::from_table(vec![0, 0, 1, 2, 2, 2, 3])));
    }
}

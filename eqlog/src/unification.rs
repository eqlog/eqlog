use crate::indirect_ast::*;
use std::collections::HashMap;
use std::mem::swap;
use std::ops::{Index, IndexMut};

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct TermMap<Value> {
    ids: Vec<usize>,
    values: Vec<Value>,
}

impl<Value> Index<Term> for TermMap<Value> {
    type Output = Value;
    fn index(&self, tm: Term) -> &Value {
        let id = self.ids[tm.0];
        &self.values[id]
    }
}

impl<Value> IndexMut<Term> for TermMap<Value> {
    fn index_mut(&mut self, tm: Term) -> &mut Value {
        let id = self.ids[tm.0];
        &mut self.values[id]
    }
}

impl<Value> TermMap<Value> {
    #[cfg(test)]
    pub fn new(values: Vec<Value>) -> TermMap<Value> {
        TermMap {
            ids: (0..values.len()).collect(),
            values,
        }
    }
    pub fn map<U>(self, f: impl FnMut(Value) -> U) -> TermMap<U> {
        let TermMap { ids, values } = self;
        let values = values.into_iter().map(f).collect();
        TermMap { ids, values }
    }
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct TermUnification<'a, Payload, UnionFunction> {
    universe: &'a TermUniverse,
    parents: Vec<usize>,
    payloads: Vec<Option<Payload>>,
    union: UnionFunction,
}

impl<'a, Payload, UnionFunction> TermUnification<'a, Payload, UnionFunction>
where
    UnionFunction: Fn(Payload, Payload) -> Payload,
{
    pub fn new(universe: &'a TermUniverse, payloads: Vec<Payload>, union: UnionFunction) -> Self {
        assert_eq!(universe.len(), payloads.len());
        TermUnification {
            universe: universe,
            parents: (0..universe.len()).collect(),
            payloads: payloads.into_iter().map(Some).collect(),
            union,
        }
    }

    // TODO: Find a way to get rid of this by making `root` take &self.
    pub fn root_const(&self, tm: Term) -> Term {
        let mut i = tm.0;
        while i != self.parents[i] {
            i = self.parents[i];
        }
        let root = i;
        Term(root)
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

    pub fn union(&mut self, lhs: Term, rhs: Term) -> &Payload {
        let lhs_root = self.root(lhs);
        let rhs_root = self.root(rhs);

        if lhs_root == rhs_root {
            return self.payloads[rhs_root.0].as_ref().unwrap();
        }

        let mut lhs_payload = None;
        swap(&mut self.payloads[lhs_root.0], &mut lhs_payload);

        let mut rhs_payload = None;
        swap(&mut self.payloads[rhs_root.0], &mut rhs_payload);

        let new_payload = (self.union)(lhs_payload.unwrap(), rhs_payload.unwrap());

        self.parents[lhs_root.0] = rhs_root.0;
        self.payloads[rhs_root.0] = Some(new_payload);

        self.payloads[rhs_root.0].as_ref().unwrap()
    }

    pub fn congruence_closure(&mut self) {
        let mut vars: HashMap<&str, Term> = HashMap::new();
        for tm in self.universe.iter_terms() {
            if let TermData::Variable(s) = self.universe.data(tm) {
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
            for tm in self.universe.iter_terms() {
                if let TermData::Application(f, args) = self.universe.data(tm) {
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

    pub fn freeze(mut self) -> TermMap<Payload> {
        let mut ids = vec![usize::MAX; self.universe.len()];
        let mut values = Vec::new();
        let mut next_id = 0;

        for tm in 0..self.universe.len() {
            if self.parents[tm] == tm {
                let mut val = None;
                swap(&mut val, &mut self.payloads[tm]);

                debug_assert_eq!(next_id, values.len());
                ids[tm] = next_id;
                values.push(val.unwrap());
                next_id += 1;
            }
        }

        for tm in 0..self.universe.len() {
            ids[tm] = ids[self.root(Term(tm)).0];
        }

        TermMap { ids, values }
    }
}

impl<'a, Payload, UnionFunction> Index<Term> for TermUnification<'a, Payload, UnionFunction>
where
    UnionFunction: Fn(Payload, Payload) -> Payload,
{
    type Output = Payload;
    fn index(&self, tm: Term) -> &Payload {
        let root = self.root_const(tm);
        self.payloads[root.0].as_ref().unwrap()
    }
}

impl<'a, Payload, UnionFunction> IndexMut<Term> for TermUnification<'a, Payload, UnionFunction>
where
    UnionFunction: Fn(Payload, Payload) -> Payload,
{
    fn index_mut(&mut self, tm: Term) -> &mut Payload {
        let root = self.root(tm);
        self.payloads[root.0].as_mut().unwrap()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_initial_state() {
        use TermData::*;
        let mut univ = TermUniverse::new();
        let t0 = univ.new_term(Wildcard, None);
        let t1 = univ.new_term(Variable("123".to_string()), None);
        let t2 = univ.new_term(Application("f".to_string(), vec![t0, t1]), None);
        let t3 = univ.new_term(Wildcard, None);
        let t4 = univ.new_term(Wildcard, None);
        let t5 = univ.new_term(Wildcard, None);

        let mut unif = TermUnification::new(
            &univ,
            vec![true, false, true, false, true, false],
            |lhs, rhs| !(lhs && rhs),
        );
        assert_eq!(unif.root(t0), t0);
        assert_eq!(unif[t0], true);
        assert_eq!(unif.root(t1), t1);
        assert_eq!(unif[t1], false);
        assert_eq!(unif.root(t2), t2);
        assert_eq!(unif[t2], true);
        assert_eq!(unif.root(t3), t3);
        assert_eq!(unif[t3], false);
        assert_eq!(unif.root(t4), t4);
        assert_eq!(unif[t4], true);
        assert_eq!(unif.root(t5), t5);
        assert_eq!(unif[t5], false);
    }

    fn new_unification<'a>(
        universe: &'a TermUniverse,
    ) -> TermUnification<'a, bool, impl Fn(bool, bool) -> bool> {
        TermUnification::new(
            &universe,
            (0..universe.len()).map(|i| i % 2 == 0).collect(),
            |lhs, rhs| !(lhs && rhs),
        )
    }

    #[test]
    fn test_union_root() {
        use TermData::*;
        let mut univ = TermUniverse::new();
        let t0 = univ.new_term(Wildcard, None);
        let t1 = univ.new_term(Variable("123".to_string()), None);
        let t2 = univ.new_term(Application("f".to_string(), vec![t0, t1]), None);
        let t3 = univ.new_term(Wildcard, None);
        let t4 = univ.new_term(Wildcard, None);
        let t5 = univ.new_term(Wildcard, None);

        let mut unif = new_unification(&univ);
        unif.union(t0, t1);
        assert_eq!(unif.root(t0), unif.root(t1));
        assert!(unif.root(t0) == t0 || unif.root(t0) == t1);
        assert_eq!(unif[t0], true);
        assert_eq!(unif[t1], true);

        let mut unif = new_unification(&univ);
        unif.union(t0, t1);
        unif.union(t1, t2);
        assert_eq!(unif.root(t0), unif.root(t2));
        assert_eq!(unif.root(t1), unif.root(t2));
        assert_eq!(unif[t0], false);
        assert_eq!(unif[t1], false);

        let mut unif = new_unification(&univ);
        unif.union(t0, t1);
        unif.union(t2, t1);
        assert_eq!(unif.root(t2), unif.root(t0));
        assert_eq!(unif.root(t0), unif.root(t1));
        assert_eq!(unif[t0], false);
        assert_eq!(unif[t1], false);
        assert_eq!(unif[t2], false);

        let mut unif = new_unification(&univ);
        unif.union(t0, t1);
        unif.union(t1, t2);
        unif.union(t3, t4);
        unif.union(t4, t5);
        unif.union(t1, t4);
        assert_eq!(unif.root(t2), unif.root(t3));
        assert_eq!(unif[t0], true);
        assert_eq!(unif[t1], true);
        assert_eq!(unif[t2], true);
        assert_eq!(unif[t3], true);
        assert_eq!(unif[t4], true);
        assert_eq!(unif[t5], true);
    }

    #[test]
    fn test_variable_congruence() {
        use TermData::*;
        let mut univ = TermUniverse::new();
        let t0 = univ.new_term(Wildcard, None);
        let t1 = univ.new_term(Wildcard, None);
        let t2 = univ.new_term(Variable("123".to_string()), None);
        let t3 = univ.new_term(Variable("abc".to_string()), None);
        let t4 = univ.new_term(Variable("123".to_string()), None);
        let t5 = univ.new_term(Application("123".to_string(), vec![t0, t2]), None);

        let mut unif = new_unification(&univ);
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
        let t0 = univ.new_term(Wildcard, None);
        let t1 = univ.new_term(Wildcard, None);
        let t2 = univ.new_term(Variable("123".to_string()), None);
        let _ = univ.new_term(Variable("abc".to_string()), None);
        let t4 = univ.new_term(Variable("123".to_string()), None);
        let t5 = univ.new_term(Application("123".to_string(), vec![t0, t2]), None);
        let t6 = univ.new_term(Application("abc".to_string(), vec![t0, t2]), None);
        let t7 = univ.new_term(Application("123".to_string(), vec![t0, t4]), None);
        let t8 = univ.new_term(Application("abc".to_string(), vec![t1, t2]), None);
        let t9 = univ.new_term(Application("xyz".to_string(), vec![t1, t6]), None);
        let t10 = univ.new_term(Application("xyz".to_string(), vec![t1, t8]), None);

        let mut unif = new_unification(&univ);
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
    fn test_freeze() {
        use TermData::*;
        let mut univ = TermUniverse::new();
        let t0 = univ.new_term(Wildcard, None);
        let t1 = univ.new_term(Variable("123".to_string()), None);
        let t2 = univ.new_term(Application("f".to_string(), vec![t0, t1]), None);
        let t3 = univ.new_term(Wildcard, None);
        let t4 = univ.new_term(Wildcard, None);
        let t5 = univ.new_term(Wildcard, None);
        let _ = univ.new_term(Application("g".to_string(), vec![t0, t2]), None);

        let mut unif = TermUnification::new(&univ, vec![1; univ.len()], |x, y| x + y);
        unif.union(t0, t1);

        unif.union(t3, t4);
        unif.union(t4, t5);

        let map = unif.freeze();
        assert_eq!(map[t0], 2);
        assert_eq!(map[t1], 2);
        assert_eq!(map[t2], 1);
        assert_eq!(map[t3], 3);
        assert_eq!(map[t4], 3);
        assert_eq!(map[t5], 3);
    }
}

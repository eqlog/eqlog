use crate::indirect_ast::*;
use std::collections::HashMap;

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
    pub fn tabulate<T: From<usize> + Clone>(&mut self) -> (T, Vec<T>) {
        let mut table = Vec::new();
        table.resize(self.parents.len(), T::from(0));

        let mut next_id = 0;
        for (tm, _) in self.universe.iter_terms() {
            if tm == self.root(tm) {
                table[tm.0] = T::from(next_id);
                next_id += 1;
            }
        }
        for (tm, _) in self.universe.iter_terms() {
            table[tm.0] = table[self.root(tm).0].clone();
        }
        (T::from(next_id), table)
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

        assert_eq!(unif.tabulate(), (4, vec![0, 0, 1, 2, 2, 2, 3]));
    }
}

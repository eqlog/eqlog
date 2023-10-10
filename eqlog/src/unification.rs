use crate::ast::*;
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
    pub fn map<U>(self, f: impl FnMut(Value) -> U) -> TermMap<U> {
        let TermMap { ids, values } = self;
        let values = values.into_iter().map(f).collect();
        TermMap { ids, values }
    }
}

pub trait MergeFn<Payload> {
    fn merge(&mut self, lhs: Payload, rhs: Payload) -> Payload;
}

impl<Payload, F> MergeFn<Payload> for F
where
    F: FnMut(Payload, Payload) -> Payload,
{
    fn merge(&mut self, lhs: Payload, rhs: Payload) -> Payload {
        (*self)(lhs, rhs)
    }
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct TermUnification<'a, Payload, Merge>
where
    Merge: MergeFn<Payload>,
{
    context: &'a TermContext,
    parents: Vec<usize>,
    payloads: Vec<Option<Payload>>,
    merge: Merge,
}

impl<'a, Payload, Merge: MergeFn<Payload>> TermUnification<'a, Payload, Merge> {
    pub fn new(context: &'a TermContext, payloads: Vec<Payload>, merge: Merge) -> Self {
        assert_eq!(context.len(), payloads.len());
        TermUnification {
            context: context,
            parents: (0..context.len()).collect(),
            payloads: payloads.into_iter().map(Some).collect(),
            merge,
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

        let new_payload = self.merge.merge(lhs_payload.unwrap(), rhs_payload.unwrap());

        self.parents[lhs_root.0] = rhs_root.0;
        self.payloads[rhs_root.0] = Some(new_payload);

        self.payloads[rhs_root.0].as_ref().unwrap()
    }

    pub fn congruence_closure(&mut self) {
        let mut vars: HashMap<&str, Term> = HashMap::new();
        for tm in self.context.iter_terms() {
            if let TermData::Variable(s) = self.context.data(tm) {
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
            for tm in self.context.iter_terms() {
                if let TermData::Application { func, args } = self.context.data(tm) {
                    let arg_roots = args.iter().map(|arg| self.root(*arg)).collect();
                    let prev_tm = apps.insert((func, arg_roots), tm);
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
        let mut ids = vec![usize::MAX; self.context.len()];
        let mut values = Vec::new();
        let mut next_id = 0;

        for tm in 0..self.context.len() {
            if self.parents[tm] == tm {
                let mut val = None;
                swap(&mut val, &mut self.payloads[tm]);

                debug_assert_eq!(next_id, values.len());
                ids[tm] = next_id;
                values.push(val.unwrap());
                next_id += 1;
            }
        }

        for tm in 0..self.context.len() {
            ids[tm] = ids[self.root(Term(tm)).0];
        }

        TermMap { ids, values }
    }
}

impl<'a, Payload, Merge> Index<Term> for TermUnification<'a, Payload, Merge>
where
    Merge: MergeFn<Payload>,
{
    type Output = Payload;
    fn index(&self, tm: Term) -> &Payload {
        let root = self.root_const(tm);
        self.payloads[root.0].as_ref().unwrap()
    }
}

impl<'a, Payload, Merge> IndexMut<Term> for TermUnification<'a, Payload, Merge>
where
    Merge: MergeFn<Payload>,
{
    fn index_mut(&mut self, tm: Term) -> &mut Payload {
        let root = self.root(tm);
        self.payloads[root.0].as_mut().unwrap()
    }
}

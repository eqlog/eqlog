use std::collections::HashMap;
use std::fmt::Debug;
use ena::unify::{UnifyKey, UnifyValue, InPlaceUnificationTable};
use std::hash::Hash;
use std::marker::PhantomData;

struct Id<Value>(u32, PhantomData<Value>);

impl<Value> Clone for Id<Value> {
    fn clone(&self) -> Self { Id(self.0, PhantomData) }
}
impl<Value> Copy for Id<Value> {}
impl<Value> PartialEq for Id<Value> {
    fn eq(&self, other: &Self) -> bool { self.0 == other.0 }
}
impl<Value> Eq for Id<Value> {}
impl<Value> Debug for Id<Value> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_fmt(format_args!("Id({}, PhantomData)", self.0))
    }
}

impl<V: UnifyValue> UnifyKey for Id<V> {
    type Value = V;

    fn index(&self) -> u32 {
        self.0
    }

    fn from_index(index: u32) -> Self {
        Id(index, PhantomData)
    }

    fn tag() -> &'static str {
        ""
    }
}

pub struct UnionMap<Key, Value: UnifyValue> {
    key_ids: HashMap<Key, Id<Value>>,
    id_keys: Vec<Key>,
    unify_table: InPlaceUnificationTable<Id<Value>>,
}

// TODO: A Copy or Clone constrained on Key shouldn't really be necessary.
impl<Key: Eq + Hash + Copy, Value: UnifyValue + Default> UnionMap<Key, Value> {
    pub fn new() -> Self {
        UnionMap {
            key_ids: HashMap::new(),
            id_keys: Vec::new(),
            unify_table: InPlaceUnificationTable::new(),
        }
    }

    pub fn insert_key(&mut self, key: Key) {
        // unify with default value may never fail.
        match self.update(key, Value::default()) {
            Ok(_) => (),
            Err(_) => panic!("UnifyKey::unify_values failed with default() value"),
        }
    }

    pub fn update(&mut self, key: Key, val: Value) -> Result<(), Value::Error> {
        match self.key_ids.get(&key) {
            None => {
                let key_id = self.unify_table.new_key(val);
                debug_assert_eq!(self.id_keys.len(), key_id.index() as usize);

                self.key_ids.insert(key, key_id);
                self.id_keys.push(key);
                Ok(())
            },
            Some(&id) => {
                self.unify_table.unify_var_value(id, val)
            },
        }
    }

    // TODO: Return by reference instead?
    pub fn get(&mut self, key: Key) -> Option<Value> {
        match self.key_ids.get(&key) {
            None => None,
            Some(&id) => Some(self.unify_table.probe_value(id)),
        }
    }

    // TODO: Get rid of all the copying going on here.
    pub fn iter<'a>(&'a mut self) -> impl Iterator<Item=(Key, Value)> {
        let keys: Vec<(Key, Id<Value>)> = self.key_ids.iter().map(|(&key, &id)| (key, id)).collect();
        let values: Vec<Value> = keys.iter().map(|&(_, id)| self.unify_table.probe_value(id)).collect();
        keys.into_iter().map(|(key, _)| key).zip(values.into_iter())
    }

    pub fn unify(&mut self, key1: Key, key2: Key) -> Result<(), Value::Error> {
        self.insert_key(key1);
        self.insert_key(key2);
        let key1_id = *self.key_ids.get(&key1).unwrap();
        let key2_id = *self.key_ids.get(&key2).unwrap();
        self.unify_table.unify_var_var(key1_id, key2_id)
    }

    pub fn len(&self) -> usize {
        self.id_keys.len()
    }
}

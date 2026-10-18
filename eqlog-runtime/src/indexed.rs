//! Mutable relation storage for evaluators that materialize every fact.
//!
//! Each row is stamped with the position at which it was appended to its
//! table's log. A consumer remembers the log length it last read: rows it has
//! not seen yet are exactly the live rows stamped at or after that position,
//! so semi-naive evaluation needs neither snapshots nor set differences.

use std::collections::hash_map::Entry;
use std::collections::HashMap;
use std::hash::{BuildHasherDefault, Hasher};

use crate::parallel::Task;

const SEED: u64 = 0xf135_7aea_2e62_a9c5;

/// A fast, deterministic hasher for small integer keys.
#[derive(Clone, Copy, Default)]
pub struct FxHasher {
    hash: u64,
}

impl FxHasher {
    #[inline]
    fn add(&mut self, word: u64) {
        self.hash = self.hash.wrapping_add(word).wrapping_mul(SEED);
    }
}

impl Hasher for FxHasher {
    #[inline]
    fn write(&mut self, bytes: &[u8]) {
        let mut chunks = bytes.chunks_exact(8);
        for chunk in &mut chunks {
            self.add(u64::from_le_bytes(chunk.try_into().unwrap()));
        }
        let rest = chunks.remainder();
        if !rest.is_empty() {
            let mut word = [0; 8];
            word[..rest.len()].copy_from_slice(rest);
            self.add(u64::from_le_bytes(word));
        }
    }

    #[inline]
    fn write_u32(&mut self, word: u32) {
        self.add(u64::from(word));
    }

    #[inline]
    fn write_u64(&mut self, word: u64) {
        self.add(word);
    }

    #[inline]
    fn write_usize(&mut self, word: usize) {
        self.add(word as u64);
    }

    #[inline]
    fn finish(&self) -> u64 {
        // Hash tables take bucket indices from the low bits; the multiply
        // above mixes entropy into the high bits.
        self.hash.rotate_left(26)
    }
}

pub type FxBuildHasher = BuildHasherDefault<FxHasher>;
pub type FxHashMap<K, V> = HashMap<K, V, FxBuildHasher>;

const NONE: u32 = u32::MAX;
const MAX_ARITY: usize = 16;
// Nodes with more entries than this are found through the level's hash table
// instead of a linear scan.
const SCAN_LIMIT: usize = 8;

#[derive(Clone)]
enum Entries {
    Inline(u32, [(u32, u32); 2]),
    Heap(Vec<(u32, u32)>),
}

impl Entries {
    #[inline(always)]
    fn as_slice(&self) -> &[(u32, u32)] {
        match self {
            Entries::Inline(len, entries) => &entries[..*len as usize],
            Entries::Heap(entries) => entries,
        }
    }

    #[inline(always)]
    fn len(&self) -> usize {
        match self {
            Entries::Inline(len, _) => *len as usize,
            Entries::Heap(entries) => entries.len(),
        }
    }

    #[inline]
    fn push(&mut self, entry: (u32, u32)) {
        match self {
            Entries::Inline(len, entries) => {
                if (*len as usize) < entries.len() {
                    entries[*len as usize] = entry;
                    *len += 1;
                } else {
                    let mut heap = Vec::with_capacity(SCAN_LIMIT);
                    heap.extend_from_slice(entries);
                    heap.push(entry);
                    *self = Entries::Heap(heap);
                }
            }
            Entries::Heap(entries) => entries.push(entry),
        }
    }

    /// Removes the entry at `pos`; returns the key moved into `pos`, if any.
    #[inline]
    fn swap_remove(&mut self, pos: usize) -> Option<u32> {
        match self {
            Entries::Inline(len, entries) => {
                let last = *len as usize - 1;
                entries[pos] = entries[last];
                *len -= 1;
                (pos < last).then(|| entries[pos].0)
            }
            Entries::Heap(entries) => {
                entries.swap_remove(pos);
                entries.get(pos).map(|entry| entry.0)
            }
        }
    }
}

#[derive(Clone)]
struct Node {
    entries: Entries,
    // The smallest stamp of the rows below this node. Removals leave it
    // unchanged, so it can only make a view visit an empty subtree.
    min: u32,
    indexed: bool,
}

impl Node {
    fn empty() -> Self {
        Node {
            entries: Entries::Inline(0, [(0, 0); 2]),
            min: u32::MAX,
            indexed: false,
        }
    }
}

#[derive(Clone)]
enum Lookup {
    // Positions and values of entries of indexed nodes, keyed by node and key.
    Hashed(FxHashMap<u64, (u32, u32)>),
    // Positions and values of the entries of the root, the only node of its
    // level, indexed by key. Element IDs are dense, and absent keys have
    // `NONE` positions.
    Direct(Vec<(u32, u32)>),
}

#[derive(Clone)]
struct Level {
    nodes: Vec<Node>,
    free: Vec<u32>,
    lookup: Lookup,
}

#[inline]
fn lookup_key(node: u32, key: u32) -> u64 {
    (u64::from(node) << 32) | u64::from(key)
}

impl Level {
    fn inner() -> Self {
        Level {
            nodes: Vec::new(),
            free: Vec::new(),
            lookup: Lookup::Hashed(FxHashMap::default()),
        }
    }

    fn root() -> Self {
        let mut level = Level {
            nodes: Vec::new(),
            free: Vec::new(),
            lookup: Lookup::Direct(Vec::new()),
        };
        let root = level.alloc();
        level.nodes[root as usize].indexed = true;
        level
    }

    /// Returns the position and value of `key` in `node`.
    #[inline(always)]
    fn find(&self, node: u32, key: u32) -> Option<(u32, u32)> {
        let entries = &self.nodes[node as usize];
        if entries.indexed {
            match &self.lookup {
                Lookup::Hashed(lookup) => lookup.get(&lookup_key(node, key)).copied(),
                Lookup::Direct(slots) => slots
                    .get(key as usize)
                    .copied()
                    .filter(|&(pos, _)| pos != NONE),
            }
        } else {
            entries
                .entries
                .as_slice()
                .iter()
                .position(|entry| entry.0 == key)
                .map(|pos| (pos as u32, entries.entries.as_slice()[pos].1))
        }
    }

    fn alloc(&mut self) -> u32 {
        match self.free.pop() {
            Some(node) => node,
            None => {
                self.nodes.push(Node::empty());
                u32::try_from(self.nodes.len() - 1).expect("trie node limit")
            }
        }
    }

    fn release(&mut self, node: u32) {
        let entry = &mut self.nodes[node as usize];
        debug_assert_eq!(entry.entries.len(), 0);
        *entry = Node::empty();
        self.free.push(node);
    }

    #[inline(always)]
    fn push(&mut self, node: u32, key: u32, value: u32) {
        let entry = &mut self.nodes[node as usize];
        entry.entries.push((key, value));
        let pos = (entry.entries.len() - 1) as u32;
        if entry.indexed {
            match &mut self.lookup {
                Lookup::Hashed(lookup) => {
                    lookup.insert(lookup_key(node, key), (pos, value));
                }
                Lookup::Direct(slots) => {
                    let key = key as usize;
                    if slots.len() <= key {
                        slots.resize((key + 1).max(2 * slots.len()), (NONE, 0));
                    }
                    slots[key] = (pos, value);
                }
            }
        } else if entry.entries.len() > SCAN_LIMIT {
            entry.indexed = true;
            match &mut self.lookup {
                Lookup::Hashed(lookup) => {
                    for (pos, &(key, value)) in entry.entries.as_slice().iter().enumerate() {
                        lookup.insert(lookup_key(node, key), (pos as u32, value));
                    }
                }
                Lookup::Direct(_) => {
                    unreachable!("only roots are directly addressed and they start indexed")
                }
            }
        }
    }

    /// Removes `key` from `node` and returns whether it was present.
    fn remove(&mut self, node: u32, key: u32) -> bool {
        let Some((pos, _)) = self.find(node, key) else {
            return false;
        };
        let entry = &mut self.nodes[node as usize];
        let moved = entry.entries.swap_remove(pos as usize);
        if entry.indexed {
            match &mut self.lookup {
                Lookup::Hashed(lookup) => {
                    lookup.remove(&lookup_key(node, key));
                    if let Some(moved) = moved {
                        let slot = lookup
                            .get_mut(&lookup_key(node, moved))
                            .expect("indexed entries are in the lookup table");
                        slot.0 = pos;
                    }
                }
                Lookup::Direct(slots) => {
                    slots[key as usize] = (NONE, 0);
                    if let Some(moved) = moved {
                        slots[moved as usize].0 = pos;
                    }
                }
            }
        }
        true
    }
}

/// A mutable prefix tree whose leaves record the stamp of their row.
#[derive(Clone)]
pub struct Trie {
    levels: Vec<Level>,
    // Stamp of the empty row of a nullary trie.
    unit: Option<u32>,
}

impl Trie {
    pub fn new(arity: usize) -> Self {
        assert!(arity <= MAX_ARITY, "relation arity exceeds {MAX_ARITY}");
        let levels = (0..arity)
            .map(|column| match column {
                0 => Level::root(),
                _ => Level::inner(),
            })
            .collect();
        Trie { levels, unit: None }
    }

    /// Inserts a row that must not be present yet.
    pub fn insert(&mut self, row: &[u32], stamp: u32) {
        debug_assert_eq!(row.len(), self.levels.len());
        let Some(last) = row.len().checked_sub(1) else {
            debug_assert!(self.unit.is_none());
            self.unit = Some(stamp);
            return;
        };
        let mut node = 0;
        for (column, &key) in row.iter().enumerate() {
            let entry = &mut self.levels[column].nodes[node as usize];
            entry.min = entry.min.min(stamp);
            if column == last {
                debug_assert!(self.levels[column].find(node, key).is_none());
                self.levels[column].push(node, key, stamp);
                break;
            }
            node = match self.levels[column].find(node, key) {
                Some((_, child)) => child,
                None => {
                    let child = self.levels[column + 1].alloc();
                    self.levels[column].push(node, key, child);
                    child
                }
            };
        }
    }

    /// Removes a row and returns whether it was present.
    pub fn remove(&mut self, row: &[u32]) -> bool {
        debug_assert_eq!(row.len(), self.levels.len());
        let Some(last) = row.len().checked_sub(1) else {
            return self.unit.take().is_some();
        };
        let mut path = [0u32; MAX_ARITY];
        let mut node = 0;
        for column in 0..last {
            path[column] = node;
            match self.levels[column].find(node, row[column]) {
                Some((_, child)) => node = child,
                None => return false,
            }
        }
        path[last] = node;
        if !self.levels[last].remove(node, row[last]) {
            return false;
        }
        let mut column = last;
        while column > 0
            && self.levels[column].nodes[path[column] as usize]
                .entries
                .len()
                == 0
        {
            self.levels[column].release(path[column]);
            let removed = self.levels[column - 1].remove(path[column - 1], row[column - 1]);
            debug_assert!(removed);
            column -= 1;
        }
        true
    }

    #[inline]
    fn root<const BOUNDED: bool>(&self, before: u32) -> TrieView<'_, BOUNDED> {
        match self.levels.first() {
            Some(_) => TrieView {
                levels: &self.levels,
                node: 0,
                before,
            },
            None => match self.unit {
                Some(stamp) if !BOUNDED || stamp < before => TrieView::unit(before),
                Some(_) | None => TrieView::empty(),
            },
        }
    }

    /// A view of all rows.
    #[inline]
    pub fn view(&self) -> TrieView<'_, false> {
        self.root(u32::MAX)
    }

    /// A view of the rows stamped before `before`.
    #[inline]
    pub fn view_before(&self, before: u32) -> TrieView<'_, true> {
        self.root(before)
    }
}

/// A read-only window onto the rows of a trie below some fixed prefix. A
/// `BOUNDED` view only contains rows stamped before `before`.
///
/// Stamp bounds of inner nodes are conservative, so a bounded view's
/// `is_empty` and `get` can report a nonempty subtree that contains no row
/// in range. Iteration and the last column check stamps exactly.
#[derive(Clone, Copy)]
pub struct TrieView<'a, const BOUNDED: bool> {
    // The levels below the fixed prefix; empty for rows of a nullary suffix.
    levels: &'a [Level],
    // `NONE` marks the empty view when `levels` is empty.
    node: u32,
    before: u32,
}

impl<const BOUNDED: bool> Default for TrieView<'_, BOUNDED> {
    #[inline]
    fn default() -> Self {
        TrieView::empty()
    }
}

impl<'a, const BOUNDED: bool> TrieView<'a, BOUNDED> {
    #[inline]
    pub fn empty() -> Self {
        TrieView {
            levels: &[],
            node: NONE,
            before: 0,
        }
    }

    #[inline]
    fn unit(before: u32) -> Self {
        TrieView {
            levels: &[],
            node: 0,
            before,
        }
    }

    #[inline(always)]
    fn child(&self, rest: &'a [Level], value: u32) -> Option<TrieView<'a, BOUNDED>> {
        match rest.first() {
            None => (!BOUNDED || value < self.before).then(|| TrieView::unit(self.before)),
            Some(level) => {
                if BOUNDED && level.nodes[value as usize].min >= self.before {
                    return None;
                }
                Some(TrieView {
                    levels: rest,
                    node: value,
                    before: self.before,
                })
            }
        }
    }

    /// Restricts the first remaining column to `key`.
    #[inline(always)]
    pub fn get(&self, key: u32) -> Option<TrieView<'a, BOUNDED>> {
        let (level, rest) = self.levels.split_first()?;
        let (_, value) = level.find(self.node, key)?;
        self.child(rest, value)
    }

    #[inline(always)]
    pub fn is_empty(&self) -> bool {
        match self.levels.first() {
            None => self.node == NONE,
            Some(level) => {
                let node = &level.nodes[self.node as usize];
                node.entries.len() == 0 || (BOUNDED && node.min >= self.before)
            }
        }
    }

    /// An upper bound on the number of distinct keys in the first column.
    #[inline]
    pub fn len_upper_bound(&self) -> usize {
        match self.levels.first() {
            None => 0,
            Some(level) => level.nodes[self.node as usize].entries.len(),
        }
    }

    /// On the last column, the restriction holding the oldest row, which
    /// prefers rows a consumer has already seen. On other columns, the first
    /// restriction, which removals may have reordered.
    #[inline]
    pub fn oldest_restriction(&self) -> Option<(u32, TrieView<'a, BOUNDED>)> {
        let (level, rest) = self.levels.split_first()?;
        if !rest.is_empty() {
            return self.iter_restrictions().next();
        }
        level.nodes[self.node as usize]
            .entries
            .as_slice()
            .iter()
            .filter(|&&(_, stamp)| !BOUNDED || stamp < self.before)
            .min_by_key(|&&(_, stamp)| stamp)
            .map(|&(key, _)| (key, TrieView::unit(self.before)))
    }

    /// Iterates over the distinct keys of the first column together with
    /// their restrictions.
    #[inline(always)]
    pub fn iter_restrictions(&self) -> Restrictions<'a, BOUNDED> {
        match self.levels.split_first() {
            None => Restrictions {
                entries: [].iter(),
                rest: &[],
                view: *self,
            },
            Some((level, rest)) => Restrictions {
                entries: level.nodes[self.node as usize].entries.as_slice().iter(),
                rest,
                view: *self,
            },
        }
    }
}

pub struct Restrictions<'a, const BOUNDED: bool> {
    entries: std::slice::Iter<'a, (u32, u32)>,
    rest: &'a [Level],
    view: TrieView<'a, BOUNDED>,
}

impl<'a, const BOUNDED: bool> Iterator for Restrictions<'a, BOUNDED> {
    type Item = (u32, TrieView<'a, BOUNDED>);

    #[inline(always)]
    fn next(&mut self) -> Option<Self::Item> {
        loop {
            let &(key, value) = self.entries.next()?;
            if let Some(child) = self.view.child(self.rest, value) {
                return Some((key, child));
            }
        }
    }
}

/// A window onto rows sorted in index order that share a fixed prefix.
#[derive(Clone, Copy)]
pub struct RowsView<'a, const W: usize> {
    rows: &'a [[u32; W]],
    depth: usize,
}

impl<const W: usize> Default for RowsView<'_, W> {
    #[inline]
    fn default() -> Self {
        RowsView::empty()
    }
}

impl<'a, const W: usize> RowsView<'a, W> {
    /// Views sorted rows; see [`Table::delta`].
    #[inline]
    pub fn new(rows: &'a [[u32; W]]) -> Self {
        debug_assert!(rows.windows(2).all(|pair| pair[0] < pair[1]));
        RowsView { rows, depth: 0 }
    }

    #[inline]
    pub fn empty() -> Self {
        RowsView {
            rows: &[],
            depth: W,
        }
    }

    /// Restricts the first remaining column to `key`.
    #[inline]
    pub fn get(&self, key: u32) -> Option<RowsView<'a, W>> {
        let depth = self.depth;
        if depth >= W {
            return None;
        }
        let start = self.rows.partition_point(|row| row[depth] < key);
        let len = self.rows[start..].partition_point(|row| row[depth] == key);
        (len > 0).then(|| RowsView {
            rows: &self.rows[start..start + len],
            depth: depth + 1,
        })
    }

    #[inline]
    pub fn is_empty(&self) -> bool {
        self.rows.is_empty()
    }

    /// An upper bound on the number of distinct keys in the first column.
    #[inline]
    pub fn len_upper_bound(&self) -> usize {
        self.rows.len()
    }

    #[inline]
    pub fn iter_restrictions(&self) -> RowsRestrictions<'a, W> {
        RowsRestrictions {
            rows: if self.depth < W { self.rows } else { &[] },
            depth: self.depth,
        }
    }

    /// Every row is new, so any restriction is as old as another.
    #[inline]
    pub fn oldest_restriction(&self) -> Option<(u32, RowsView<'a, W>)> {
        self.iter_restrictions().next()
    }
}

pub struct RowsRestrictions<'a, const W: usize> {
    rows: &'a [[u32; W]],
    depth: usize,
}

impl<'a, const W: usize> Iterator for RowsRestrictions<'a, W> {
    type Item = (u32, RowsView<'a, W>);

    #[inline(always)]
    fn next(&mut self) -> Option<Self::Item> {
        let depth = self.depth;
        let key = self.rows.first()?[depth];
        let len = self.rows[1..]
            .iter()
            .position(|row| row[depth] != key)
            .map_or(self.rows.len(), |pos| pos + 1);
        let (group, rest) = self.rows.split_at(len);
        self.rows = rest;
        Some((
            key,
            RowsView {
                rows: group,
                depth: depth + 1,
            },
        ))
    }
}

/// One of two iterators over the same items, chosen at run time.
pub enum Either<L, R> {
    Left(L),
    Right(R),
}

impl<L: Iterator, R: Iterator<Item = L::Item>> Iterator for Either<L, R> {
    type Item = L::Item;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        match self {
            Either::Left(left) => left.next(),
            Either::Right(right) => right.next(),
        }
    }
}

struct Index {
    // Source columns in the index's key order.
    columns: Box<[usize]>,
    // Pairs of source columns that rows of the index must agree on.
    equal: Box<[(usize, usize)]>,
    // Absent for indices that are only read through deltas.
    trie: Option<Trie>,
}

impl Index {
    fn insert<const N: usize>(&mut self, row: &[u32; N], stamp: u32) {
        let Index {
            columns,
            equal,
            trie,
        } = self;
        let mut key = [0u32; MAX_ARITY];
        if let Some(trie) = trie {
            if project(columns, equal, row, &mut key) {
                trie.insert(&key[..columns.len()], stamp);
            }
        }
    }

    fn remove<const N: usize>(&mut self, row: &[u32; N]) {
        let Index {
            columns,
            equal,
            trie,
        } = self;
        let mut key = [0u32; MAX_ARITY];
        if let Some(trie) = trie {
            if project(columns, equal, row, &mut key) {
                let removed = trie.remove(&key[..columns.len()]);
                debug_assert!(removed);
            }
        }
    }
}

/// Writes the key of `row` in an index with these columns and equalities,
/// unless the row is not in the index.
#[inline]
fn project<const N: usize>(
    columns: &[usize],
    equal: &[(usize, usize)],
    row: &[u32; N],
    out: &mut [u32; MAX_ARITY],
) -> bool {
    if equal.iter().any(|&(i, j)| row[i] != row[j]) {
        return false;
    }
    for (key, &column) in out.iter_mut().zip(columns) {
        *key = row[column];
    }
    true
}

/// For each element of a type, the entries of the rows it occurs in, most
/// recent first. The lists share one arena, so recording an occurrence
/// never allocates per element.
pub struct Occurrences {
    // The first node of each element's list.
    heads: Vec<u32>,
    // An entry and the next node of its list.
    nodes: Vec<(u64, u32)>,
    // Nodes of taken lists, linked through their next nodes.
    free: u32,
}

impl Default for Occurrences {
    fn default() -> Self {
        Occurrences::with_elements(0)
    }
}

impl Occurrences {
    pub fn with_elements(count: usize) -> Self {
        Occurrences {
            heads: vec![NONE; count],
            nodes: Vec::new(),
            free: NONE,
        }
    }

    pub fn add_element(&mut self) {
        self.heads.push(NONE);
    }

    #[inline(always)]
    pub fn push(&mut self, element: u32, entry: u64) {
        let head = &mut self.heads[element as usize];
        let next = *head;
        if self.free == NONE {
            *head = u32::try_from(self.nodes.len()).expect("occurrence limit");
            self.nodes.push((entry, next));
        } else {
            *head = self.free;
            let node = &mut self.nodes[self.free as usize];
            self.free = node.1;
            *node = (entry, next);
        }
    }

    /// Detaches the list of an element, to be consumed by
    /// [`Occurrences::pop`].
    #[inline]
    pub fn take(&mut self, element: u32) -> u32 {
        std::mem::replace(&mut self.heads[element as usize], NONE)
    }

    /// Removes the first entry of a detached list.
    #[inline]
    pub fn pop(&mut self, list: &mut u32) -> Option<u64> {
        if *list == NONE {
            return None;
        }
        let index = *list;
        let (entry, next) = self.nodes[index as usize];
        self.nodes[index as usize].1 = self.free;
        self.free = index;
        *list = next;
        Some(entry)
    }

    pub fn iter(&self, element: u32) -> impl Iterator<Item = u64> + '_ {
        let mut node = self.heads[element as usize];
        std::iter::from_fn(move || {
            (node != NONE).then(|| {
                let (entry, next) = self.nodes[node as usize];
                node = next;
                entry
            })
        })
    }
}

/// The rows of one relation together with the indices that rules query.
pub struct Table<const N: usize> {
    // Every inserted row, in insertion order; a row's stamp is its position.
    log: Vec<[u32; N]>,
    live: FxHashMap<[u32; N], u32>,
    // Whether the row with this stamp has been removed.
    removed: Vec<bool>,
    indices: Vec<Index>,
    // While deferred, insertions and removals reach the tries only when they
    // are synchronized, in one batch per trie.
    deferred: bool,
    // The tries hold the live rows stamped before this position, except for
    // the stale rows.
    synced: u32,
    stale: Vec<u32>,
    // For the graph of a function, the first result inserted for each
    // argument tuple, keyed by rows whose result column is zero. Entries
    // outlive their rows: a row only disappears when one of its elements
    // stops being canonical, and then an equal result remains or its
    // arguments are never inserted again.
    results: Option<FxHashMap<[u32; N], u32>>,
}

/// The outcome of inserting a row into the graph of a function.
pub enum FunctionInsert {
    /// The row was already present.
    Present,
    /// The row was inserted, and no other result is known for its arguments.
    Inserted,
    /// The row was inserted, but its arguments already have this result.
    Conflict(u32),
}

impl<const N: usize> Table<N> {
    /// Creates a table maintaining one index per specification. An index
    /// specification lists source columns in key order, pairs of columns that
    /// must be equal for a row to appear in that index, and whether views of
    /// the index are needed; otherwise only deltas read it.
    pub fn new(indices: &[(&[usize], &[(usize, usize)], bool)]) -> Self {
        let indices = indices
            .iter()
            .map(|&(columns, equal, viewed)| {
                assert!(columns.iter().all(|&column| column < N));
                Index {
                    columns: columns.into(),
                    equal: equal.into(),
                    trie: viewed.then(|| Trie::new(columns.len())),
                }
            })
            .collect();
        Table {
            log: Vec::new(),
            live: FxHashMap::default(),
            removed: Vec::new(),
            indices,
            deferred: false,
            synced: 0,
            stale: Vec::new(),
            results: None,
        }
    }

    /// Creates a table for the graph of a function, whose last column holds
    /// results; see [`Table::new`] for index specifications.
    pub fn function(indices: &[(&[usize], &[(usize, usize)], bool)]) -> Self {
        assert!(N > 0, "a function graph has a result column");
        Table {
            results: Some(FxHashMap::default()),
            ..Table::new(indices)
        }
    }

    /// Inserts a row of a function graph and reports whether its arguments
    /// had another result.
    #[inline(never)]
    pub fn insert_function(&mut self, row: [u32; N]) -> FunctionInsert {
        if !self.insert(row) {
            return FunctionInsert::Present;
        }
        let result = row[N - 1];
        let mut key = row;
        key[N - 1] = 0;
        let results = self
            .results
            .as_mut()
            .expect("function tables record results");
        match results.entry(key) {
            Entry::Vacant(entry) => {
                entry.insert(result);
                FunctionInsert::Inserted
            }
            Entry::Occupied(entry) => {
                let other = *entry.get();
                if other == result {
                    FunctionInsert::Inserted
                } else {
                    FunctionInsert::Conflict(other)
                }
            }
        }
    }

    #[inline]
    pub fn len(&self) -> usize {
        self.live.len()
    }

    #[inline]
    pub fn is_empty(&self) -> bool {
        self.live.is_empty()
    }

    #[inline]
    pub fn contains(&self, row: [u32; N]) -> bool {
        self.live.contains_key(&row)
    }

    /// Inserts a row and returns whether it was absent.
    #[inline(never)]
    pub fn insert(&mut self, row: [u32; N]) -> bool {
        let stamp = u32::try_from(self.log.len()).expect("relation log exceeds u32 stamps");
        let absent = match self.live.entry(row) {
            Entry::Occupied(_) => false,
            Entry::Vacant(entry) => {
                entry.insert(stamp);
                true
            }
        };
        if !absent {
            return false;
        }
        self.log.push(row);
        self.removed.push(false);
        if !self.deferred {
            for index in &mut self.indices {
                index.insert(&row, stamp);
            }
            self.synced = self.log_len();
        }
        true
    }

    /// Removes a row and returns whether it was present.
    #[inline(never)]
    pub fn remove(&mut self, row: [u32; N]) -> bool {
        let Some(stamp) = self.live.remove(&row) else {
            return false;
        };
        self.removed[stamp as usize] = true;
        if self.deferred {
            if stamp < self.synced {
                self.stale.push(stamp);
            }
        } else {
            for index in &mut self.indices {
                index.remove(&row);
            }
        }
        true
    }

    /// The row stamped with `stamp`, whether or not it is still present.
    #[inline]
    pub fn row_at(&self, stamp: u32) -> [u32; N] {
        self.log[stamp as usize]
    }

    /// Removes the row stamped with `stamp` unless it was removed since.
    #[inline(never)]
    pub fn remove_stamped(&mut self, stamp: u32) -> Option<[u32; N]> {
        let row = self.log[stamp as usize];
        if self.removed[stamp as usize] {
            return None;
        }
        self.remove(row);
        Some(row)
    }

    /// Defers updating the tries until the next synchronization, or updates
    /// them right away again after synchronizing them.
    pub fn set_deferred(&mut self, deferred: bool) {
        if !deferred {
            let mut tasks = Vec::new();
            self.sync_tasks(&mut tasks);
            for task in tasks {
                task();
            }
            self.finish_sync();
        }
        self.deferred = deferred;
    }

    /// Adds a task per trie that applies the deferred insertions and
    /// removals to it, and returns how many rows they apply. The tasks must
    /// run before [`Table::finish_sync`].
    pub fn sync_tasks<'a>(&'a mut self, tasks: &mut Vec<Task<'a>>) -> usize {
        let start = self.synced as usize;
        if start == self.log.len() && self.stale.is_empty() {
            return 0;
        }
        let Table {
            log,
            removed,
            indices,
            stale,
            ..
        } = self;
        let (log, removed, stale) = (&*log, &*removed, &*stale);
        let mut work = 0;
        for index in indices.iter_mut().filter(|index| index.trie.is_some()) {
            work += log.len() - start + stale.len();
            tasks.push(Box::new(move || {
                for &stamp in stale {
                    index.remove(&log[stamp as usize]);
                }
                for (row, stamp) in log[start..].iter().zip(start as u32..) {
                    if !removed[stamp as usize] {
                        index.insert(row, stamp);
                    }
                }
            }));
        }
        work
    }

    /// Records that the tasks of [`Table::sync_tasks`] have run.
    pub fn finish_sync(&mut self) {
        self.synced = self.log_len();
        self.stale.clear();
    }

    /// The position the next inserted row will be stamped with.
    #[inline]
    pub fn log_len(&self) -> u32 {
        self.log.len() as u32
    }

    /// Whether a row stamped at or after `since` is still present.
    #[inline(never)]
    pub fn changed_since(&self, since: u32) -> bool {
        self.removed[since as usize..]
            .iter()
            .any(|&removed| !removed)
    }

    #[inline]
    fn trie(&self, index: usize) -> &Trie {
        debug_assert!(
            self.synced == self.log_len() && self.stale.is_empty(),
            "views need synchronized tries"
        );
        self.indices[index]
            .trie
            .as_ref()
            .expect("viewed indices maintain a trie")
    }

    /// All rows through the given index.
    #[inline]
    pub fn view(&self, index: usize) -> TrieView<'_, false> {
        self.trie(index).view()
    }

    /// The rows stamped before `before` through the given index.
    #[inline]
    pub fn view_before(&self, index: usize, before: u32) -> TrieView<'_, true> {
        self.trie(index).view_before(before)
    }

    /// The rows stamped at or after `since`, through the given index of
    /// width `W`, sorted for reading with a [`RowsView`].
    #[inline(never)]
    pub fn delta<const W: usize>(&self, index: usize, since: u32) -> Vec<[u32; W]> {
        let index = &self.indices[index];
        assert_eq!(index.columns.len(), W, "delta width must match the index");
        let mut rows = Vec::with_capacity(self.log.len() - since as usize);
        let mut key = [0u32; MAX_ARITY];
        for (row, stamp) in self.log[since as usize..].iter().zip(since..) {
            if !self.removed[stamp as usize] && project(&index.columns, &index.equal, row, &mut key)
            {
                rows.push(key[..W].try_into().unwrap());
            }
        }
        sort_rows(&mut rows);
        rows
    }

    /// All rows, sorted, for deterministic public iteration.
    pub fn sorted_rows(&self) -> Vec<[u32; N]> {
        let mut rows: Vec<[u32; N]> = self.rows().collect();
        rows.sort_unstable();
        rows
    }

    fn rows(&self) -> impl Iterator<Item = [u32; N]> + '_ {
        self.log
            .iter()
            .zip(&self.removed)
            .filter(|(_, &removed)| !removed)
            .map(|(&row, _)| row)
    }

    /// Iterates over all rows in sorted order.
    pub fn iter(&self) -> std::vec::IntoIter<[u32; N]> {
        self.sorted_rows().into_iter()
    }
}

macro_rules! prefix_tree_from_table {
    ($($tree:ident($arity:literal)),* $(,)?) => {
        $(impl From<&Table<$arity>> for crate::$tree {
            #[inline(never)]
            fn from(table: &Table<$arity>) -> Self {
                let mut tree = crate::$tree::new();
                for row in table.rows() {
                    tree.insert(row);
                }
                tree
            }
        })*
    };
}

prefix_tree_from_table! {
    PrefixTree0(0), PrefixTree1(1), PrefixTree2(2), PrefixTree3(3), PrefixTree4(4),
    PrefixTree5(5), PrefixTree6(6), PrefixTree7(7), PrefixTree8(8), PrefixTree9(9),
}

/// Sorts rows lexicographically, comparing packed integer keys when the
/// elements are small enough for all columns to fit into one.
fn sort_rows<const W: usize>(rows: &mut [[u32; W]]) {
    let max = rows.iter().flatten().copied().max().unwrap_or(0);
    let bits = (u32::BITS - max.leading_zeros()) as usize;
    if bits * W <= 64 {
        let mut keys: Vec<u64> = rows
            .iter()
            .map(|row| row.iter().fold(0, |key, &el| (key << bits) | u64::from(el)))
            .collect();
        keys.sort_unstable();
        let mask = (1u64 << bits) - 1;
        for (row, mut key) in rows.iter_mut().zip(keys) {
            for el in row.iter_mut().rev() {
                *el = (key & mask) as u32;
                key >>= bits;
            }
        }
    } else if bits * W <= 128 {
        let mut keys: Vec<u128> = rows
            .iter()
            .map(|row| {
                row.iter()
                    .fold(0, |key, &el| (key << bits) | u128::from(el))
            })
            .collect();
        keys.sort_unstable();
        let mask = (1u128 << bits) - 1;
        for (row, mut key) in rows.iter_mut().zip(keys) {
            for el in row.iter_mut().rev() {
                *el = (key & mask) as u32;
                key >>= bits;
            }
        }
    } else {
        rows.sort_unstable();
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::BTreeSet;

    fn rows<const BOUNDED: bool>(view: TrieView<'_, BOUNDED>, arity: usize) -> BTreeSet<Vec<u32>> {
        if arity == 0 {
            return if view.is_empty() {
                BTreeSet::new()
            } else {
                BTreeSet::from([Vec::new()])
            };
        }
        let mut result = BTreeSet::new();
        for (key, rest) in view.iter_restrictions() {
            for mut suffix in rows(rest, arity - 1) {
                suffix.insert(0, key);
                result.insert(suffix);
            }
        }
        result
    }

    #[test]
    fn views_respect_stamps_after_removals() {
        let mut table: Table<3> =
            Table::new(&[(&[0, 1, 2], &[], true), (&[2, 0], &[(0, 1)], true)]);
        assert!(table.insert([1, 2, 3]));
        assert!(table.insert([1, 1, 4]));
        assert!(!table.insert([1, 2, 3]));
        let seen = table.log_len();
        assert!(table.insert([2, 2, 5]));
        assert!(table.insert([1, 2, 6]));
        assert!(table.remove([1, 1, 4]));
        assert_eq!(
            rows(table.view_before(0, seen), 3),
            BTreeSet::from([vec![1, 2, 3]])
        );
        assert_eq!(
            rows(table.view(0), 3),
            BTreeSet::from([vec![1, 2, 3], vec![2, 2, 5], vec![1, 2, 6]])
        );
        assert_eq!(rows(table.view(1), 2), BTreeSet::from([vec![5, 2]]));
        assert!(table.changed_since(seen));
        assert!(!table.changed_since(table.log_len()));
        assert_eq!(table.delta::<3>(0, seen), vec![[1, 2, 6], [2, 2, 5]]);
        assert_eq!(table.delta::<2>(1, seen), vec![[5, 2]]);
        let delta = table.delta::<3>(0, 0);
        let view = RowsView::new(&delta);
        let keys: Vec<u32> = view.iter_restrictions().map(|(key, _)| key).collect();
        assert_eq!(keys, vec![1, 2]);
        let restricted = view.get(1).and_then(|view| view.get(2)).unwrap();
        let keys: Vec<u32> = restricted.iter_restrictions().map(|(key, _)| key).collect();
        assert_eq!(keys, vec![3, 6]);
        assert!(view.get(3).is_none());
    }

    #[test]
    fn deferred_tries_catch_up_with_removals_and_reinsertions() {
        let mut table: Table<2> = Table::new(&[(&[0, 1], &[], true), (&[1, 0], &[], true)]);
        assert!(table.insert([1, 2]));
        assert!(table.insert([3, 4]));
        table.set_deferred(true);
        let seen = table.log_len();
        // Removed while its stamp is synchronized, then inserted again.
        assert!(table.remove([1, 2]));
        assert!(table.insert([1, 2]));
        // Inserted and removed between two synchronizations.
        assert!(table.insert([5, 6]));
        assert!(table.remove([5, 6]));
        assert!(table.insert([7, 8]));
        assert!(table.remove([3, 4]));
        let mut tasks = Vec::new();
        assert!(table.sync_tasks(&mut tasks) > 0);
        assert_eq!(tasks.len(), 2);
        for task in tasks {
            task();
        }
        table.finish_sync();
        let expected = BTreeSet::from([vec![1, 2], vec![7, 8]]);
        assert_eq!(rows(table.view(0), 2), expected);
        assert_eq!(
            rows(table.view(1), 2),
            BTreeSet::from([vec![2, 1], vec![8, 7]])
        );
        assert!(rows(table.view_before(0, seen), 2).is_empty());
        table.set_deferred(false);
        assert!(table.insert([9, 9]));
        assert!(rows(table.view(0), 2).contains(&vec![9, 9]));
    }

    #[test]
    fn occurrence_lists_reuse_taken_nodes() {
        let mut occurrences = Occurrences::with_elements(2);
        occurrences.push(0, 10);
        occurrences.push(1, 20);
        occurrences.push(0, 11);
        assert_eq!(occurrences.iter(0).collect::<Vec<_>>(), vec![11, 10]);
        let mut list = occurrences.take(0);
        assert_eq!(occurrences.iter(0).count(), 0);
        assert_eq!(occurrences.pop(&mut list), Some(11));
        // Recording while a taken list is consumed reuses its nodes.
        occurrences.push(1, 21);
        assert_eq!(occurrences.pop(&mut list), Some(10));
        assert_eq!(occurrences.pop(&mut list), None);
        occurrences.add_element();
        occurrences.push(2, 30);
        occurrences.push(2, 31);
        // Four live entries; without reuse there would be six nodes.
        assert_eq!(occurrences.nodes.len(), 4);
        assert_eq!(occurrences.iter(1).collect::<Vec<_>>(), vec![21, 20]);
        assert_eq!(occurrences.iter(2).collect::<Vec<_>>(), vec![31, 30]);
    }

    #[test]
    fn large_nodes_survive_removal_and_reinsertion() {
        let mut trie = Trie::new(2);
        let mut expected = BTreeSet::new();
        for i in 0..100u32 {
            trie.insert(&[i % 3, i], i);
            expected.insert(vec![i % 3, i]);
        }
        for i in (0..100u32).step_by(7) {
            assert!(trie.remove(&[i % 3, i]));
            expected.remove(&vec![i % 3, i]);
        }
        assert!(!trie.remove(&[0, 7]));
        for i in (0..100u32).step_by(14) {
            trie.insert(&[i % 3, i], 100 + i);
            expected.insert(vec![i % 3, i]);
        }
        assert_eq!(rows(trie.view(), 2), expected);
        assert_eq!(
            trie.view_before(100).get(0).map(|view| rows(view, 1)),
            Some(
                (0..100u32)
                    .filter(|i| i % 3 == 0 && i % 7 != 0)
                    .map(|i| vec![i])
                    .collect()
            )
        );
    }

    #[test]
    fn oldest_restrictions_survive_reordering_removals() {
        let mut trie = Trie::new(1);
        trie.insert(&[5], 0);
        trie.insert(&[6], 1);
        trie.insert(&[7], 2);
        assert!(trie.remove(&[5]));
        // Removal moved the newest key in front of the older one.
        assert_eq!(trie.view().iter_restrictions().next().unwrap().0, 7);
        assert_eq!(trie.view().oldest_restriction().unwrap().0, 6);
        assert_eq!(trie.view_before(2).oldest_restriction().unwrap().0, 6);
        assert!(trie.view_before(1).oldest_restriction().is_none());
    }

    // `None` for a present row, otherwise the conflicting result, if any.
    fn outcome(insert: FunctionInsert) -> Option<Option<u32>> {
        match insert {
            FunctionInsert::Present => None,
            FunctionInsert::Inserted => Some(None),
            FunctionInsert::Conflict(other) => Some(Some(other)),
        }
    }

    #[test]
    fn function_tables_report_other_results() {
        let mut table: Table<3> = Table::function(&[(&[0, 1, 2], &[], true)]);
        assert_eq!(outcome(table.insert_function([1, 2, 3])), Some(None));
        assert_eq!(outcome(table.insert_function([1, 2, 3])), None);
        assert_eq!(outcome(table.insert_function([1, 2, 4])), Some(Some(3)));
        assert_eq!(outcome(table.insert_function([1, 5, 4])), Some(None));
        assert_eq!(table.len(), 3);
    }

    #[test]
    fn packed_sorting_matches_lexicographic_order() {
        for max in [0u32, 1, 7, 1 << 20, u32::MAX] {
            let mut rows: Vec<[u32; 3]> = (0..200u32)
                .map(|i| {
                    [
                        i.wrapping_mul(7) % 3,
                        (i * 13) % 11,
                        i.wrapping_mul(2654435761) % (max / 2 + 1),
                    ]
                })
                .map(|row| row.map(|el| el.min(max)))
                .collect();
            rows.sort_unstable();
            rows.dedup();
            let mut shuffled = rows.clone();
            shuffled.reverse();
            sort_rows(&mut shuffled);
            assert_eq!(shuffled, rows);
        }
    }

    #[test]
    fn nullary_tables_hold_one_row() {
        let mut table: Table<0> = Table::new(&[(&[], &[], true)]);
        assert!(table.view(0).is_empty());
        assert!(table.insert([]));
        assert!(!table.insert([]));
        assert!(!table.view(0).is_empty());
        assert!(table.view_before(0, 0).is_empty());
        assert!(table.remove([]));
        assert!(table.view(0).is_empty());
    }
}

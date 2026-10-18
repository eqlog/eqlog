//! Mutable relation storage for evaluators that materialize every fact.
//!
//! Each row is stamped with the position at which it was appended to its
//! table's log. A consumer remembers the log length it last read: rows it has
//! not seen yet are exactly the live rows stamped at or after that position,
//! so semi-naive evaluation needs neither snapshots nor set differences.

use std::collections::HashMap;
use std::hash::{BuildHasherDefault, Hasher};

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
                    let mut heap = Vec::with_capacity(4);
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
    // Conservative stamp bounds of the rows below this node. Removals leave
    // them unchanged, so they can only make a view visit an empty subtree.
    min: u32,
    max: u32,
    indexed: bool,
}

impl Node {
    fn empty() -> Self {
        Node {
            entries: Entries::Inline(0, [(0, 0); 2]),
            min: u32::MAX,
            max: 0,
            indexed: false,
        }
    }
}

#[derive(Clone, Default)]
struct Level {
    nodes: Vec<Node>,
    free: Vec<u32>,
    // Positions and values of entries of indexed nodes, keyed by node and key.
    lookup: FxHashMap<u64, (u32, u32)>,
}

#[inline]
fn lookup_key(node: u32, key: u32) -> u64 {
    (u64::from(node) << 32) | u64::from(key)
}

impl Level {
    /// Returns the position and value of `key` in `node`.
    #[inline(always)]
    fn find(&self, node: u32, key: u32) -> Option<(u32, u32)> {
        let entries = &self.nodes[node as usize];
        if entries.indexed {
            self.lookup.get(&lookup_key(node, key)).copied()
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

    #[inline]
    fn push(&mut self, node: u32, key: u32, value: u32) {
        let entry = &mut self.nodes[node as usize];
        entry.entries.push((key, value));
        let len = entry.entries.len();
        if entry.indexed {
            self.lookup
                .insert(lookup_key(node, key), ((len - 1) as u32, value));
        } else if len > SCAN_LIMIT {
            entry.indexed = true;
            for (pos, &(key, value)) in entry.entries.as_slice().iter().enumerate() {
                self.lookup
                    .insert(lookup_key(node, key), (pos as u32, value));
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
            self.lookup.remove(&lookup_key(node, key));
            if let Some(moved) = moved {
                let slot = self
                    .lookup
                    .get_mut(&lookup_key(node, moved))
                    .expect("indexed entries are in the lookup table");
                slot.0 = pos;
            }
        }
        true
    }

    fn clear(&mut self) {
        self.nodes.clear();
        self.free.clear();
        self.lookup.clear();
    }
}

/// A mutable prefix tree whose leaves record the stamp of their row.
#[derive(Clone)]
pub struct Trie {
    levels: Vec<Level>,
    // Stamp of the empty row of a nullary trie.
    unit: Option<u32>,
    len: usize,
}

impl Trie {
    pub fn new(arity: usize) -> Self {
        assert!(arity <= MAX_ARITY, "relation arity exceeds {MAX_ARITY}");
        let mut levels: Vec<Level> = (0..arity).map(|_| Level::default()).collect();
        if let Some(root) = levels.first_mut() {
            root.alloc();
        }
        Trie {
            levels,
            unit: None,
            len: 0,
        }
    }

    pub fn arity(&self) -> usize {
        self.levels.len()
    }

    pub fn len(&self) -> usize {
        self.len
    }

    pub fn is_empty(&self) -> bool {
        self.len == 0
    }

    /// Removes all rows and changes the arity, keeping allocated capacity.
    pub fn reset(&mut self, arity: usize) {
        assert!(arity <= MAX_ARITY, "relation arity exceeds {MAX_ARITY}");
        self.levels.resize_with(arity, Level::default);
        for level in &mut self.levels {
            level.clear();
        }
        if let Some(root) = self.levels.first_mut() {
            root.alloc();
        }
        self.unit = None;
        self.len = 0;
    }

    /// Inserts a row that must not be present yet.
    pub fn insert(&mut self, row: &[u32], stamp: u32) {
        debug_assert_eq!(row.len(), self.levels.len());
        let Some(last) = row.len().checked_sub(1) else {
            debug_assert!(self.unit.is_none());
            self.unit = Some(stamp);
            self.len += 1;
            return;
        };
        let mut node = 0;
        for (column, &key) in row.iter().enumerate() {
            let entry = &mut self.levels[column].nodes[node as usize];
            entry.min = entry.min.min(stamp);
            entry.max = entry.max.max(stamp);
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
        self.len += 1;
    }

    /// Removes a row and returns whether it was present.
    pub fn remove(&mut self, row: &[u32]) -> bool {
        debug_assert_eq!(row.len(), self.levels.len());
        let Some(last) = row.len().checked_sub(1) else {
            let present = self.unit.take().is_some();
            self.len -= usize::from(present);
            return present;
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
        self.len -= 1;
        true
    }

    /// Returns the stamp of a row, if present.
    pub fn stamp(&self, row: &[u32]) -> Option<u32> {
        debug_assert_eq!(row.len(), self.levels.len());
        let Some(last) = row.len().checked_sub(1) else {
            return self.unit;
        };
        let mut node = 0;
        for (column, &key) in row.iter().enumerate() {
            let (_, value) = self.levels[column].find(node, key)?;
            if column == last {
                return Some(value);
            }
            node = value;
        }
        unreachable!("the loop returns at the last column")
    }

    /// A view of the rows whose stamps lie in `lo..hi`.
    #[inline]
    pub fn view(&self, lo: u32, hi: u32) -> TrieView<'_> {
        if lo >= hi {
            return TrieView::empty();
        }
        match self.levels.first() {
            Some(_) => TrieView {
                levels: &self.levels,
                node: 0,
                lo,
                hi,
            },
            None => match self.unit {
                Some(stamp) if lo <= stamp && stamp < hi => TrieView::unit(lo, hi),
                Some(_) | None => TrieView::empty(),
            },
        }
    }

    /// A view of all rows.
    #[inline]
    pub fn view_all(&self) -> TrieView<'_> {
        self.view(0, u32::MAX)
    }

    /// Visits all rows in an arbitrary but deterministic order.
    pub fn for_each(&self, mut visit: impl FnMut(&[u32])) {
        let mut row = [0u32; MAX_ARITY];
        if self.levels.is_empty() {
            if self.unit.is_some() {
                visit(&[]);
            }
            return;
        }
        self.for_each_below(0, 0, &mut row, &mut visit);
    }

    fn for_each_below(
        &self,
        column: usize,
        node: u32,
        row: &mut [u32; MAX_ARITY],
        visit: &mut impl FnMut(&[u32]),
    ) {
        let arity = self.levels.len();
        for &(key, value) in self.levels[column].nodes[node as usize].entries.as_slice() {
            row[column] = key;
            if column + 1 == arity {
                visit(&row[..arity]);
            } else {
                self.for_each_below(column + 1, value, row, visit);
            }
        }
    }
}

/// A read-only window onto the rows of a trie below some fixed prefix, limited
/// to rows whose stamps lie in `lo..hi`.
///
/// Stamp bounds of inner nodes are conservative, so `is_empty` and `get` can
/// report a nonempty subtree that contains no row in range. Iteration and the
/// last column check stamps exactly.
#[derive(Clone, Copy)]
pub struct TrieView<'a> {
    // The levels below the fixed prefix; empty for rows of a nullary suffix.
    levels: &'a [Level],
    // `NONE` marks the empty view when `levels` is empty.
    node: u32,
    lo: u32,
    hi: u32,
}

impl Default for TrieView<'_> {
    #[inline]
    fn default() -> Self {
        TrieView::empty()
    }
}

impl<'a> TrieView<'a> {
    #[inline]
    pub fn empty() -> Self {
        TrieView {
            levels: &[],
            node: NONE,
            lo: 0,
            hi: 0,
        }
    }

    #[inline]
    fn unit(lo: u32, hi: u32) -> Self {
        TrieView {
            levels: &[],
            node: 0,
            lo,
            hi,
        }
    }

    #[inline(always)]
    fn child(&self, rest: &'a [Level], value: u32) -> Option<TrieView<'a>> {
        match rest.first() {
            None => (self.lo <= value && value < self.hi).then(|| TrieView::unit(self.lo, self.hi)),
            Some(level) => {
                if self.lo > 0 || self.hi < u32::MAX {
                    let node = &level.nodes[value as usize];
                    if node.max < self.lo || node.min >= self.hi {
                        return None;
                    }
                }
                Some(TrieView {
                    levels: rest,
                    node: value,
                    lo: self.lo,
                    hi: self.hi,
                })
            }
        }
    }

    /// Restricts the first remaining column to `key`.
    #[inline(always)]
    pub fn get(&self, key: u32) -> Option<TrieView<'a>> {
        let (level, rest) = self.levels.split_first()?;
        let (_, value) = level.find(self.node, key)?;
        self.child(rest, value)
    }

    #[inline]
    pub fn contains(&self, key: u32) -> bool {
        self.get(key).is_some()
    }

    #[inline(always)]
    pub fn is_empty(&self) -> bool {
        match self.levels.first() {
            None => self.node == NONE,
            Some(level) => {
                let node = &level.nodes[self.node as usize];
                node.entries.len() == 0 || node.max < self.lo || node.min >= self.hi
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

    /// The restriction holding the oldest row, which on the last column
    /// prefers rows a consumer has already seen.
    #[inline]
    pub fn oldest_restriction(&self) -> Option<(u32, TrieView<'a>)> {
        let (level, rest) = self.levels.split_first()?;
        if !rest.is_empty() {
            return self.iter_restrictions().next();
        }
        level.nodes[self.node as usize]
            .entries
            .as_slice()
            .iter()
            .filter(|&&(_, stamp)| self.lo <= stamp && stamp < self.hi)
            .min_by_key(|&&(_, stamp)| stamp)
            .map(|&(key, _)| (key, TrieView::unit(self.lo, self.hi)))
    }

    /// Iterates over the distinct keys of the first column together with
    /// their restrictions.
    #[inline]
    pub fn iter_restrictions(&self) -> Restrictions<'a> {
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

pub struct Restrictions<'a> {
    entries: std::slice::Iter<'a, (u32, u32)>,
    rest: &'a [Level],
    view: TrieView<'a>,
}

impl<'a> Iterator for Restrictions<'a> {
    type Item = (u32, TrieView<'a>);

    #[inline]
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
    pub fn contains(&self, key: u32) -> bool {
        self.get(key).is_some()
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

    #[inline]
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
    trie: Trie,
}

impl Index {
    #[inline]
    fn project<const N: usize>(&self, row: &[u32; N], out: &mut [u32; MAX_ARITY]) -> bool {
        if self.equal.iter().any(|&(i, j)| row[i] != row[j]) {
            return false;
        }
        for (key, &column) in out.iter_mut().zip(self.columns.iter()) {
            *key = row[column];
        }
        true
    }
}

/// The rows of one relation together with the indices that rules query.
pub struct Table<const N: usize> {
    // Every inserted row, in insertion order; a row's stamp is its position.
    log: Vec<[u32; N]>,
    live: FxHashMap<[u32; N], u32>,
    indices: Vec<Index>,
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
    /// specification lists source columns in key order and pairs of columns
    /// that must be equal for a row to appear in that index.
    pub fn new(indices: &[(&[usize], &[(usize, usize)])]) -> Self {
        let indices = indices
            .iter()
            .map(|&(columns, equal)| {
                assert!(columns.iter().all(|&column| column < N));
                Index {
                    columns: columns.into(),
                    equal: equal.into(),
                    trie: Trie::new(columns.len()),
                }
            })
            .collect();
        Table {
            log: Vec::new(),
            live: FxHashMap::default(),
            indices,
            results: None,
        }
    }

    /// Creates a table for the graph of a function, whose last column holds
    /// results; see [`Table::new`] for index specifications.
    pub fn function(indices: &[(&[usize], &[(usize, usize)])]) -> Self {
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
            std::collections::hash_map::Entry::Vacant(entry) => {
                entry.insert(result);
                FunctionInsert::Inserted
            }
            std::collections::hash_map::Entry::Occupied(entry) => {
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
        if self.live.try_insert_stamp(row, stamp) {
            self.log.push(row);
            let mut key = [0u32; MAX_ARITY];
            for index in &mut self.indices {
                if index.project(&row, &mut key) {
                    index.trie.insert(&key[..index.columns.len()], stamp);
                }
            }
            true
        } else {
            false
        }
    }

    /// Removes a row and returns whether it was present.
    #[inline(never)]
    pub fn remove(&mut self, row: [u32; N]) -> bool {
        if self.live.remove(&row).is_none() {
            return false;
        }
        let mut key = [0u32; MAX_ARITY];
        for index in &mut self.indices {
            if index.project(&row, &mut key) {
                let removed = index.trie.remove(&key[..index.columns.len()]);
                debug_assert!(removed);
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
        if self.live.get(&row) != Some(&stamp) {
            return None;
        }
        self.remove(row);
        Some(row)
    }

    /// The position the next inserted row will be stamped with.
    #[inline]
    pub fn log_len(&self) -> u32 {
        self.log.len() as u32
    }

    /// Whether a row stamped at or after `since` is still present.
    #[inline(never)]
    pub fn changed_since(&self, since: u32) -> bool {
        self.log[since as usize..]
            .iter()
            .zip(since..)
            .any(|(row, stamp)| self.live.get(row) == Some(&stamp))
    }

    /// Rows stamped in `lo..hi` through the given index.
    #[inline]
    pub fn view(&self, index: usize, lo: u32, hi: u32) -> TrieView<'_> {
        self.indices[index].trie.view(lo, hi)
    }

    /// The rows stamped at or after `since`, through the given index of
    /// width `W`, sorted for reading with a [`RowsView`].
    #[inline(never)]
    pub fn delta<const W: usize>(&self, index: usize, since: u32) -> Vec<[u32; W]> {
        let index = &self.indices[index];
        assert_eq!(index.columns.len(), W, "delta width must match the index");
        let mut rows = Vec::new();
        let mut key = [0u32; MAX_ARITY];
        for (row, stamp) in self.log[since as usize..].iter().zip(since..) {
            if self.live.get(row) == Some(&stamp) && index.project(row, &mut key) {
                rows.push(key[..W].try_into().unwrap());
            }
        }
        sort_rows(&mut rows);
        rows
    }

    /// All rows, sorted, for deterministic public iteration.
    pub fn sorted_rows(&self) -> Vec<[u32; N]> {
        let mut rows: Vec<[u32; N]> = self.live.keys().copied().collect();
        rows.sort_unstable();
        rows
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
                for row in table.live.keys() {
                    tree.insert(*row);
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

trait TryInsertStamp<const N: usize> {
    fn try_insert_stamp(&mut self, row: [u32; N], stamp: u32) -> bool;
}

impl<const N: usize> TryInsertStamp<N> for FxHashMap<[u32; N], u32> {
    #[inline]
    fn try_insert_stamp(&mut self, row: [u32; N], stamp: u32) -> bool {
        match self.entry(row) {
            std::collections::hash_map::Entry::Occupied(_) => false,
            std::collections::hash_map::Entry::Vacant(entry) => {
                entry.insert(stamp);
                true
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::BTreeSet;

    fn rows(view: TrieView<'_>, arity: usize) -> BTreeSet<Vec<u32>> {
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
        let mut table: Table<3> = Table::new(&[(&[0, 1, 2], &[]), (&[2, 0], &[(0, 1)])]);
        assert!(table.insert([1, 2, 3]));
        assert!(table.insert([1, 1, 4]));
        assert!(!table.insert([1, 2, 3]));
        let seen = table.log_len();
        assert!(table.insert([2, 2, 5]));
        assert!(table.insert([1, 2, 6]));
        assert!(table.remove([1, 1, 4]));
        assert_eq!(
            rows(table.view(0, 0, seen), 3),
            BTreeSet::from([vec![1, 2, 3]])
        );
        assert_eq!(
            rows(table.view(0, seen, u32::MAX), 3),
            BTreeSet::from([vec![2, 2, 5], vec![1, 2, 6]])
        );
        assert_eq!(
            rows(table.view(1, 0, u32::MAX), 2),
            BTreeSet::from([vec![5, 2]])
        );
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
        assert_eq!(rows(trie.view_all(), 2), expected);
        assert_eq!(trie.len(), expected.len());
        for row in &expected {
            assert!(trie.stamp(row).is_some());
        }
        assert_eq!(
            trie.view(100, u32::MAX).get(0).map(|view| rows(view, 1)),
            Some(
                (0..100u32)
                    .step_by(14)
                    .filter(|i| i % 3 == 0)
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
        assert_eq!(trie.view_all().iter_restrictions().next().unwrap().0, 7);
        assert_eq!(trie.view_all().oldest_restriction().unwrap().0, 6);
        assert_eq!(trie.view(2, u32::MAX).oldest_restriction().unwrap().0, 7);
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
        let mut table: Table<3> = Table::function(&[(&[0, 1, 2], &[])]);
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
        let mut table: Table<0> = Table::new(&[(&[], &[])]);
        assert!(table.view(0, 0, u32::MAX).is_empty());
        assert!(table.insert([]));
        assert!(!table.insert([]));
        assert!(!table.view(0, 0, u32::MAX).is_empty());
        assert!(table.view(0, 1, u32::MAX).is_empty());
        assert!(table.remove([]));
        assert!(table.view(0, 0, u32::MAX).is_empty());
    }
}

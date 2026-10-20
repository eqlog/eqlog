use super::map::*;
use super::mapping::MonotoneMap;
use crate::{Error, Fuel};
use std::fmt;
use std::mem;
use std::rc::Rc;

#[derive(Clone)]
pub struct WBTreeSet {
    storage: Storage,
}

#[derive(Clone)]
enum Storage {
    Empty,
    Singleton(u32),
    Ranges(Rc<Ranges>),
    Tree(WBTreeMap<()>),
}

impl WBTreeSet {
    pub(crate) fn shares_root(&self, other: &Self) -> bool {
        match (&self.storage, &other.storage) {
            (Storage::Empty, Storage::Empty) => true,
            (Storage::Singleton(left), Storage::Singleton(right)) => left == right,
            (Storage::Ranges(left), Storage::Ranges(right)) => Rc::ptr_eq(left, right),
            (Storage::Tree(left), Storage::Tree(right)) => left.shares_root(right),
            (Storage::Empty, Storage::Singleton(_) | Storage::Ranges(_) | Storage::Tree(_))
            | (Storage::Singleton(_), Storage::Empty | Storage::Ranges(_) | Storage::Tree(_))
            | (Storage::Ranges(_), Storage::Empty | Storage::Singleton(_) | Storage::Tree(_))
            | (Storage::Tree(_), Storage::Empty | Storage::Singleton(_) | Storage::Ranges(_)) => {
                false
            }
        }
    }

    pub(crate) fn root_identity(&self) -> usize {
        match &self.storage {
            Storage::Empty => 0,
            Storage::Singleton(value) => usize::try_from(u64::from(*value) * 2 + 1)
                .expect("inline keys must fit tagged identities"),
            Storage::Ranges(ranges) => Rc::as_ptr(ranges) as usize,
            Storage::Tree(map) => map.root_identity(),
        }
    }

    pub const fn new() -> Self {
        Self {
            storage: Storage::Empty,
        }
    }

    fn singleton(value: u32) -> Self {
        // Odd identities cannot collide with aligned tree pointers. Large keys
        // stay allocated on platforms without room for the extra tag bit.
        let storage = if usize::try_from(u64::from(value) * 2 + 1).is_ok() {
            Storage::Singleton(value)
        } else {
            let mut map = WBTreeMap::new();
            map.insert(value, ());
            Storage::Tree(map)
        };
        Self { storage }
    }

    fn from_map(map: WBTreeMap<()>) -> Self {
        match map.len_up_to(2) {
            0 => Self::new(),
            1 => Self::singleton(map.iter().next().expect("singleton has one key").0),
            _ => Self {
                storage: Storage::Tree(map),
            },
        }
    }

    fn from_ranges(mut ranges: Ranges) -> Self {
        ranges.promote();
        match ranges.len {
            0 => Self::new(),
            1 => Self::singleton(ranges.runs.iter().next().expect("singleton has one run").0),
            _ => Self {
                storage: Storage::Ranges(Rc::new(ranges)),
            },
        }
    }

    pub fn insert(&mut self, value: u32) -> bool {
        match &mut self.storage {
            Storage::Empty => {
                *self = Self::singleton(value);
                true
            }
            Storage::Singleton(existing) => {
                if *existing == value {
                    return false;
                }
                if existing.abs_diff(value) == 1 {
                    let mut ranges = Ranges::default();
                    ranges.push((*existing).min(value), (*existing).max(value));
                    self.storage = Storage::Ranges(Rc::new(ranges));
                } else {
                    let mut map = WBTreeMap::new();
                    map.insert(*existing, ());
                    map.insert(value, ());
                    self.storage = Storage::Tree(map);
                }
                true
            }
            Storage::Ranges(ranges) => {
                if ranges.contains(value) {
                    return false;
                }
                let ranges = Rc::make_mut(ranges);
                ranges.insert(value);
                ranges.promote();
                true
            }
            Storage::Tree(map) => map.insert(value, ()).is_none(),
        }
    }

    #[inline]
    pub fn contains(&self, value: &u32) -> bool {
        match &self.storage {
            Storage::Empty => false,
            Storage::Singleton(existing) => existing == value,
            Storage::Ranges(ranges) => ranges.contains(*value),
            Storage::Tree(map) => map.contains_key(value),
        }
    }

    pub fn remove(&mut self, value: &u32) -> bool {
        match &mut self.storage {
            Storage::Empty => false,
            Storage::Singleton(existing) => {
                if existing != value {
                    return false;
                }
                self.storage = Storage::Empty;
                true
            }
            Storage::Ranges(ranges) => {
                if !ranges.contains(*value) {
                    return false;
                }
                if ranges.len == 2 {
                    let remaining = ranges
                        .runs
                        .iter()
                        .flat_map(|(first, last)| [first, last])
                        .find(|key| key != value)
                        .expect("two-element set retains one key");
                    *self = Self::singleton(remaining);
                    return true;
                }
                let ranges = Rc::make_mut(ranges);
                ranges.remove(*value);
                ranges.promote();
                true
            }
            Storage::Tree(map) => {
                let removed = map.remove(value).is_some();
                if removed && map.len_up_to(2) < 2 {
                    *self = Self::from_map(mem::replace(map, WBTreeMap::new()));
                }
                removed
            }
        }
    }

    pub fn is_empty(&self) -> bool {
        match &self.storage {
            Storage::Empty => true,
            Storage::Singleton(_) | Storage::Ranges(_) => false,
            Storage::Tree(map) => map.is_empty(),
        }
    }

    pub fn len(&self) -> usize {
        match &self.storage {
            Storage::Empty => 0,
            Storage::Singleton(_) => 1,
            Storage::Ranges(ranges) => ranges.len,
            Storage::Tree(map) => map.len(),
        }
    }

    pub(crate) fn len_upper_bound(&self) -> usize {
        match &self.storage {
            Storage::Empty => 0,
            Storage::Singleton(_) => 1,
            Storage::Ranges(ranges) => ranges.len,
            Storage::Tree(map) => map.len_upper_bound(),
        }
    }

    pub(crate) fn iteration_work(&self, fuel: &mut Fuel) -> Result<u64, Error> {
        match &self.storage {
            Storage::Empty => {
                fuel.consume(1)?;
                Ok(1)
            }
            Storage::Singleton(_) => {
                fuel.consume(1)?;
                Ok(2)
            }
            Storage::Ranges(ranges) => {
                fuel.consume(1)?;
                Ok((ranges.len as u64).saturating_add(1))
            }
            Storage::Tree(map) => map.iteration_work(fuel, |(), _fuel| Ok(0)),
        }
    }

    pub(crate) fn mapped(&self, mapping: MonotoneMap) -> Self {
        match &self.storage {
            Storage::Empty => Self::new(),
            Storage::Singleton(value) => mapping
                .apply(*value)
                .map_or_else(Self::new, Self::singleton),
            Storage::Ranges(ranges) => {
                let mut result = Ranges::default();
                for (first, last) in ranges.runs.iter() {
                    mapping.map_range(first, last, |first, last| result.push(first, last));
                }
                Self::from_ranges(result)
            }
            Storage::Tree(map) => Self {
                storage: Storage::Tree(map.mapped_keys(mapping)),
            },
        }
    }

    pub fn clear(&mut self) {
        self.storage = Storage::Empty;
    }

    pub fn iter(&self) -> WBTreeSetIter<'_> {
        let storage = match &self.storage {
            Storage::Empty => IterStorage::Ranges {
                runs: RunsIter::Small([].iter()),
                current: 1,
                last: 0,
            },
            Storage::Singleton(value) => IterStorage::Ranges {
                runs: RunsIter::Small([].iter()),
                current: u64::from(*value),
                last: *value,
            },
            Storage::Ranges(ranges) => IterStorage::Ranges {
                runs: ranges.runs.iter(),
                current: 1,
                last: 0,
            },
            Storage::Tree(map) => IterStorage::Tree(map.iter()),
        };
        WBTreeSetIter { storage }
    }

    pub(crate) fn union_assign(&mut self, other: &Self) {
        match &other.storage {
            Storage::Empty => {}
            Storage::Singleton(value) => {
                self.insert(*value);
            }
            Storage::Ranges(_) | Storage::Tree(_) => *self = self.union(other),
        }
    }

    pub fn union(&self, other: &Self) -> Self {
        if self.shares_root(other) {
            return self.clone();
        }
        match &self.storage {
            Storage::Empty => other.clone(),
            Storage::Singleton(value) => {
                let mut result = other.clone();
                result.insert(*value);
                result
            }
            Storage::Ranges(left) => match &other.storage {
                Storage::Ranges(right) => Self::from_ranges(left.union(right)),
                Storage::Empty => self.clone(),
                Storage::Singleton(value) => {
                    let mut result = self.clone();
                    result.insert(*value);
                    result
                }
                Storage::Tree(_) => {
                    if self.len() <= other.len_upper_bound() / 8 {
                        let mut result = other.clone();
                        for value in self.iter() {
                            result.insert(value);
                        }
                        return result;
                    }
                    let right = Ranges::from_sorted(other.iter());
                    Self::from_ranges(left.union(&right))
                }
            },
            Storage::Tree(left) => match &other.storage {
                Storage::Empty => self.clone(),
                Storage::Singleton(value) => {
                    let mut result = self.clone();
                    result.insert(*value);
                    result
                }
                Storage::Ranges(_) => other.union(self),
                Storage::Tree(right) => {
                    Self::from_map(left.union_shared(right, |_element, (), ()| ()))
                }
            },
        }
    }

    pub fn intersection(&self, other: &Self) -> Self {
        if self.shares_root(other) {
            return self.clone();
        }
        match &self.storage {
            Storage::Empty => Self::new(),
            Storage::Singleton(value) => {
                if other.contains(value) {
                    self.clone()
                } else {
                    Self::new()
                }
            }
            Storage::Ranges(left) => match &other.storage {
                Storage::Ranges(right) => Self::from_ranges(left.intersection(right)),
                Storage::Empty => Self::new(),
                Storage::Singleton(_) => other.intersection(self),
                Storage::Tree(_) => {
                    let values = if self.len() < other.len_upper_bound() {
                        Ranges::from_sorted(self.iter().filter(|value| other.contains(value)))
                    } else {
                        Ranges::from_sorted(other.iter().filter(|value| self.contains(value)))
                    };
                    Self::from_ranges(values)
                }
            },
            Storage::Tree(left) => match &other.storage {
                Storage::Empty => Self::new(),
                Storage::Singleton(value) => {
                    if left.contains_key(value) {
                        other.clone()
                    } else {
                        Self::new()
                    }
                }
                Storage::Ranges(_) => other.intersection(self),
                Storage::Tree(right) => Self::from_map(left.intersection_shared(
                    right,
                    |_key, (), ()| Some(()),
                    |(), ()| true,
                )),
            },
        }
    }

    pub fn difference(&self, other: &Self) -> Self {
        if self.shares_root(other) {
            return Self::new();
        }
        match &self.storage {
            Storage::Empty => Self::new(),
            Storage::Singleton(value) => {
                if other.contains(value) {
                    Self::new()
                } else {
                    self.clone()
                }
            }
            Storage::Ranges(left) => match &other.storage {
                Storage::Ranges(right) => Self::from_ranges(left.difference(right)),
                Storage::Empty => self.clone(),
                Storage::Singleton(value) => {
                    let mut result = self.clone();
                    result.remove(value);
                    result
                }
                Storage::Tree(_) => {
                    if self.len() <= other.len_upper_bound() / 8 {
                        return Self::from_ranges(Ranges::from_sorted(
                            self.iter().filter(|value| !other.contains(value)),
                        ));
                    }
                    let right = Ranges::from_sorted(other.iter());
                    Self::from_ranges(left.difference(&right))
                }
            },
            Storage::Tree(left) => match &other.storage {
                Storage::Empty => self.clone(),
                Storage::Singleton(value) => {
                    let mut result = self.clone();
                    result.remove(value);
                    result
                }
                Storage::Ranges(right) => {
                    if other.len() <= self.len_upper_bound() / 8 {
                        let mut result = self.clone();
                        for value in other.iter() {
                            result.remove(&value);
                        }
                        return result;
                    }
                    let left = Ranges::from_sorted(self.iter());
                    Self::from_ranges(left.difference(right))
                }
                Storage::Tree(right) => Self::from_map(left.difference_shared(
                    right,
                    |_element, (), ()| None,
                    |(), ()| true,
                )),
            },
        }
    }

    pub(crate) fn all_difference(&self, other: &Self, mut visit: impl FnMut(u32) -> bool) -> bool {
        if self.shares_root(other) {
            return true;
        }
        match &self.storage {
            Storage::Empty => true,
            Storage::Singleton(value) => other.contains(value) || visit(*value),
            Storage::Ranges(_) => self.iter().all(|key| other.contains(&key) || visit(key)),
            Storage::Tree(left) => match &other.storage {
                Storage::Ranges(_) => self.iter().all(|key| other.contains(&key) || visit(key)),
                Storage::Empty => {
                    left.all_difference_entries(&WBTreeMap::new(), |key, (), _| visit(key))
                }
                Storage::Singleton(excluded) => left
                    .all_difference_entries(&WBTreeMap::new(), |key, (), _| {
                        key == *excluded || visit(key)
                    }),
                Storage::Tree(right) => left
                    .all_difference_entries(right, |key, (), value| value.is_some() || visit(key)),
            },
        }
    }

    pub fn difference_iter<'a>(&'a self, other: &'a Self) -> impl Iterator<Item = u32> + 'a {
        if self.shares_root(other) {
            return DifferenceIter::Inline(None);
        }
        match &self.storage {
            Storage::Empty => DifferenceIter::Inline(None),
            Storage::Singleton(value) => {
                DifferenceIter::Inline((!other.contains(value)).then_some(*value))
            }
            Storage::Ranges(_) => DifferenceIter::Filter {
                iter: self.iter(),
                other,
            },
            Storage::Tree(left) => match &other.storage {
                Storage::Ranges(_) => DifferenceIter::Filter {
                    iter: self.iter(),
                    other,
                },
                Storage::Empty => DifferenceIter::Exclude {
                    iter: left.iter(),
                    excluded: None,
                },
                Storage::Singleton(value) => DifferenceIter::Exclude {
                    iter: left.iter(),
                    excluded: Some(*value),
                },
                Storage::Tree(right) => DifferenceIter::Shared(left.difference_entries(right)),
            },
        }
    }
}

impl fmt::Debug for WBTreeSet {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_set().entries(self.iter()).finish()
    }
}

pub struct WBTreeSetIter<'a> {
    storage: IterStorage<'a>,
}
enum IterStorage<'a> {
    Ranges {
        runs: RunsIter<'a>,
        current: u64,
        last: u32,
    },
    Tree(Iter<'a, ()>),
}

impl Iterator for WBTreeSetIter<'_> {
    type Item = u32;
    #[inline]
    fn next(&mut self) -> Option<u32> {
        match &mut self.storage {
            IterStorage::Ranges {
                runs,
                current,
                last,
            } => {
                if *current <= u64::from(*last) {
                    let value = *current as u32;
                    *current += 1;
                    return Some(value);
                }
                let (first, end) = runs.next()?;
                *current = u64::from(first) + 1;
                *last = end;
                Some(first)
            }
            IterStorage::Tree(iter) => iter.next().map(|(key, ())| key),
        }
    }

    fn fold<B, F>(self, mut result: B, mut visit: F) -> B
    where
        F: FnMut(B, u32) -> B,
    {
        match self.storage {
            IterStorage::Ranges {
                runs,
                current,
                last,
            } => {
                if current <= u64::from(last) {
                    result = (current as u32..=last).fold(result, &mut visit);
                }
                runs.fold(result, |result, (first, last)| {
                    (first..=last).fold(result, &mut visit)
                })
            }
            IterStorage::Tree(iter) => iter.fold(result, |result, (key, ())| visit(result, key)),
        }
    }
}

enum DifferenceIter<'a> {
    Inline(Option<u32>),
    Filter {
        iter: WBTreeSetIter<'a>,
        other: &'a WBTreeSet,
    },
    Exclude {
        iter: Iter<'a, ()>,
        excluded: Option<u32>,
    },
    Shared(Difference<'a, ()>),
}

impl Iterator for DifferenceIter<'_> {
    type Item = u32;
    fn next(&mut self) -> Option<u32> {
        match self {
            Self::Inline(value) => value.take(),
            Self::Filter { iter, other } => iter.find(|key| !other.contains(key)),
            Self::Exclude { iter, excluded } => {
                iter.find_map(|(key, ())| (Some(key) != *excluded).then_some(key))
            }
            Self::Shared(iter) => iter.find_map(|(key, (), right)| right.is_none().then_some(key)),
        }
    }
}

#[derive(Clone, Default)]
struct Ranges {
    runs: Runs,
    len: usize,
}

impl Ranges {
    fn from_sorted(values: impl IntoIterator<Item = u32>) -> Self {
        let mut result = Self::default();
        for value in values {
            result.push(value, value);
        }
        result
    }

    fn promote(&mut self) {
        match &mut self.runs {
            Runs::Small(runs) => {
                if runs.len() > 32 {
                    // Sparse holes must not expand every surviving member into
                    // its own node or copy all previous intervals on each edit.
                    self.runs = Runs::Tree(WBTreeMap::from_sorted_entries(mem::take(runs)));
                }
            }
            Runs::Tree(_) => {}
        }
    }

    fn contains(&self, value: u32) -> bool {
        match &self.runs {
            Runs::Small(runs) => {
                let index = runs.partition_point(|&(_, last)| last < value);
                runs.get(index).is_some_and(|&(first, _)| first <= value)
            }
            Runs::Tree(runs) => runs
                .floor_entry(value)
                .is_some_and(|(_, &last)| value <= last),
        }
    }

    fn push(&mut self, first: u32, last: u32) {
        if let Some((previous_first, previous_last)) = self.runs.last() {
            if u64::from(previous_last) + 1 >= u64::from(first) {
                if last > previous_last {
                    let added = usize::try_from(last - previous_last)
                        .expect("set cardinality must fit usize");
                    self.len = self
                        .len
                        .checked_add(added)
                        .expect("set cardinality must fit usize");
                    match &mut self.runs {
                        Runs::Small(runs) => runs.last_mut().expect("the last run exists").1 = last,
                        Runs::Tree(runs) => {
                            *runs.get_mut(&previous_first).expect("the last run exists") = last
                        }
                    }
                }
                return;
            }
        }
        let added = usize::try_from(u64::from(last) - u64::from(first) + 1)
            .expect("set cardinality must fit usize");
        self.len = self
            .len
            .checked_add(added)
            .expect("set cardinality must fit usize");
        match &mut self.runs {
            Runs::Small(runs) => runs.push((first, last)),
            Runs::Tree(runs) => {
                runs.insert(first, last);
            }
        }
    }

    fn insert(&mut self, value: u32) {
        self.len = self
            .len
            .checked_add(1)
            .expect("set cardinality must fit usize");
        match &mut self.runs {
            Runs::Small(runs) => {
                let index = runs.partition_point(|&(_, last)| last < value);
                let joins_left = index > 0 && runs[index - 1].1.checked_add(1) == Some(value);
                let joins_right = runs
                    .get(index)
                    .is_some_and(|&(first, _)| value.checked_add(1) == Some(first));
                match (joins_left, joins_right) {
                    (true, true) => runs[index - 1].1 = runs.remove(index).1,
                    (true, false) => runs[index - 1].1 = value,
                    (false, true) => runs[index].0 = value,
                    (false, false) => runs.insert(index, (value, value)),
                }
            }
            Runs::Tree(runs) => {
                let left = runs
                    .floor_entry(value)
                    .filter(|(_, last)| last.checked_add(1) == Some(value))
                    .map(|(first, _)| first);
                let right = value
                    .checked_add(1)
                    .and_then(|first| runs.get(&first).map(|&last| (first, last)));
                match (left, right) {
                    (Some(first), Some((right_first, last))) => {
                        runs.remove(&right_first);
                        *runs.get_mut(&first).expect("the adjacent run exists") = last;
                    }
                    (Some(first), None) => {
                        *runs.get_mut(&first).expect("the adjacent run exists") = value
                    }
                    (None, Some((right_first, last))) => {
                        runs.remove(&right_first);
                        runs.insert(value, last);
                    }
                    (None, None) => {
                        runs.insert(value, value);
                    }
                }
            }
        }
    }

    fn remove(&mut self, value: u32) {
        self.len -= 1;
        match &mut self.runs {
            Runs::Small(runs) => {
                let index = runs.partition_point(|&(_, last)| last < value);
                let (first, last) = runs[index];
                match (value == first, value == last) {
                    (true, true) => {
                        runs.remove(index);
                    }
                    (true, false) => runs[index].0 += 1,
                    (false, true) => runs[index].1 -= 1,
                    (false, false) => {
                        runs[index].1 = value - 1;
                        runs.insert(index + 1, (value + 1, last));
                    }
                }
            }
            Runs::Tree(runs) => {
                let (first, &last) = runs.floor_entry(value).expect("the containing run exists");
                if value == first {
                    runs.remove(&first);
                } else {
                    *runs.get_mut(&first).expect("the containing run exists") = value - 1;
                }
                if value < last {
                    runs.insert(value + 1, last);
                }
            }
        }
    }

    fn union(&self, other: &Self) -> Self {
        let mut result = Self::default();
        let mut left = self.runs.iter().peekable();
        let mut right = other.runs.iter().peekable();
        while let Some((first, last)) = match (left.peek(), right.peek()) {
            (Some(left_run), Some(right_run)) => {
                if left_run.0 <= right_run.0 {
                    left.next()
                } else {
                    right.next()
                }
            }
            (Some(_), None) => left.next(),
            (None, Some(_)) => right.next(),
            (None, None) => None,
        } {
            result.push(first, last);
        }
        result
    }

    fn intersection(&self, other: &Self) -> Self {
        let mut result = Self::default();
        let mut left = self.runs.iter().peekable();
        let mut right = other.runs.iter().peekable();
        while let (Some(&(left_first, left_last)), Some(&(right_first, right_last))) =
            (left.peek(), right.peek())
        {
            let first = left_first.max(right_first);
            let last = left_last.min(right_last);
            if first <= last {
                result.push(first, last);
            }
            if left_last <= right_last {
                left.next();
            }
            if right_last <= left_last {
                right.next();
            }
        }
        result
    }

    fn difference(&self, other: &Self) -> Self {
        let mut result = Self::default();
        let mut right = other.runs.iter().peekable();
        for (first, last) in self.runs.iter() {
            let mut first = u64::from(first);
            let last = u64::from(last);
            while let Some(&(right_first, right_last)) = right.peek() {
                let right_first = u64::from(right_first);
                let right_last = u64::from(right_last);
                if right_first > last {
                    break;
                }
                if right_first > first {
                    result.push(first as u32, (right_first - 1) as u32);
                }
                first = first.max(right_last + 1);
                if first > last {
                    break;
                }
                right.next();
            }
            if first <= last {
                result.push(first as u32, last as u32);
            }
        }
        result
    }
}

#[derive(Clone)]
enum Runs {
    Small(Vec<(u32, u32)>),
    Tree(WBTreeMap<u32>),
}

impl Default for Runs {
    fn default() -> Self {
        Self::Small(Vec::new())
    }
}

impl Runs {
    fn last(&self) -> Option<(u32, u32)> {
        match self {
            Self::Small(runs) => runs.last().copied(),
            Self::Tree(runs) => runs
                .floor_entry(u32::MAX)
                .map(|(first, &last)| (first, last)),
        }
    }

    fn iter(&self) -> RunsIter<'_> {
        match self {
            Self::Small(runs) => RunsIter::Small(runs.iter()),
            Self::Tree(runs) => RunsIter::Tree(runs.iter()),
        }
    }
}

enum RunsIter<'a> {
    Small(std::slice::Iter<'a, (u32, u32)>),
    Tree(Iter<'a, u32>),
}

impl Iterator for RunsIter<'_> {
    type Item = (u32, u32);

    fn next(&mut self) -> Option<Self::Item> {
        match self {
            Self::Small(runs) => runs.next().copied(),
            Self::Tree(runs) => runs.next().map(|(first, &last)| (first, last)),
        }
    }

    fn fold<B, F>(self, initial: B, mut visit: F) -> B
    where
        F: FnMut(B, Self::Item) -> B,
    {
        match self {
            Self::Small(runs) => runs.fold(initial, |result, &run| visit(result, run)),
            Self::Tree(runs) => runs.fold(initial, |result, (first, &last)| {
                visit(result, (first, last))
            }),
        }
    }
}

use std::mem::swap;

#[derive(Clone, PartialEq, Eq, Debug, Hash)]
pub struct Unification<T> {
    parents: Vec<T>,
    sizes: Vec<u32>,
}

impl<T: Copy + PartialEq + From<u32> + Into<u32>> Unification<T> {
    pub fn new() -> Self {
        Unification {
            parents: Vec::new(),
            sizes: Vec::new(),
        }
    }
    pub fn root(&mut self, mut el: T) -> T {
        let mut parent = self.parents[el.into() as usize];
        while el != parent {
            self.parents[el.into() as usize] = self.parents[parent.into() as usize];
            el = parent;
            parent = self.parents[parent.into() as usize];
        }
        el
    }
    pub fn union(&mut self, mut lhs: T, mut rhs: T) -> bool {
        lhs = self.root(lhs);
        rhs = self.root(rhs);

        if lhs == rhs {
            return false;
        }

        // Make sure that lhs has size >= than size of rhs.
        if self.sizes[lhs.into() as usize] < self.sizes[rhs.into() as usize] {
            swap(&mut lhs, &mut rhs);
        }

        self.parents[rhs.into() as usize] = lhs;
        self.sizes[rhs.into() as usize] += self.sizes[lhs.into() as usize];
        true
    }
    pub fn new_element(&mut self) -> T {
        assert!(self.parents.len() > u32::MAX as usize, "Overflow");
        let el = T::from(self.parents.len() as u32);
        self.parents.push(el);
        self.sizes.push(1);
        el
    }
    pub fn len(&self) -> usize {
        self.parents.len()
    }
}

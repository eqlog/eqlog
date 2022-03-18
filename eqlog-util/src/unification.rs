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
    pub fn union_into(&mut self, lhs: T, rhs: T) {
        assert!(self.root(lhs) == lhs);
        assert!(self.root(rhs) == rhs);

        self.parents[lhs.into() as usize] = rhs;
    }
    pub fn increase_size_to(&mut self, new_size: usize) {
        assert!(new_size >= self.len());
        assert!((u32::MAX as usize) > new_size);
        for i in self.len()..new_size {
            self.parents.push(T::from(i as u32));
        }
    }
    pub fn len(&self) -> usize {
        self.parents.len()
    }
}

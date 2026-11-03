pub mod ambient;
pub mod analysis;
pub mod chain;
pub mod congruence;
pub mod dag;
pub mod graph;
pub mod join;
pub mod propagation;

#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct Metrics {
    pub worlds: usize,
    pub morphisms: usize,
    pub owned_elements: usize,
    pub local_size: usize,
    pub checksum: u64,
}

pub trait Workload {
    fn close(&mut self);
    fn verify(&self) -> Metrics;
}

pub trait Case {
    type Native<'a>: Workload
    where
        Self: 'a;
    type Cow<'a>: Workload
    where
        Self: 'a;

    fn native(&self) -> Self::Native<'_>;
    fn cow(&self) -> Self::Cow<'_>;
}

// Fix the generator algorithm so seed reproducibility does not depend on a crate version.
struct Random(u64);

impl Random {
    fn new(seed: u64) -> Self {
        Self(seed)
    }

    fn word(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9e3779b97f4a7c15);
        let mut value = self.0;
        value = (value ^ (value >> 30)).wrapping_mul(0xbf58476d1ce4e5b9);
        value = (value ^ (value >> 27)).wrapping_mul(0x94d049bb133111eb);
        value ^ (value >> 31)
    }

    fn below(&mut self, bound: usize) -> usize {
        assert!(bound > 0);
        let bound = u64::try_from(bound).unwrap();
        let threshold = bound.wrapping_neg() % bound;
        loop {
            let value = self.word();
            if value >= threshold {
                return usize::try_from(value % bound).unwrap();
            }
        }
    }

    fn shuffle<T>(&mut self, values: &mut [T]) {
        for end in (1..values.len()).rev() {
            values.swap(end, self.below(end + 1));
        }
    }
}

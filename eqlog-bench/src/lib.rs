use clap::{Args, ValueEnum};

mod chain;
mod dag;
mod join;

#[derive(Clone, Copy, Debug, PartialEq, Eq, ValueEnum)]
pub enum Engine {
    Native,
    Cow,
}

impl Engine {
    pub fn name(self) -> &'static str {
        match self {
            Self::Native => "native",
            Self::Cow => "cow",
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, ValueEnum)]
pub enum Family {
    ChainPlain,
    ChainEquation,
    DagForward,
    DagLayered,
    DagWide,
    DagComb,
    DagChain,
    JoinFanout,
    JoinOverlap,
    JoinSplit,
    JoinDiamonds,
    JoinLayered,
    JoinComb,
    JoinChain,
}

impl Family {
    pub const ALL: [Self; 14] = [
        Self::ChainPlain,
        Self::ChainEquation,
        Self::DagForward,
        Self::DagLayered,
        Self::DagWide,
        Self::DagComb,
        Self::DagChain,
        Self::JoinFanout,
        Self::JoinOverlap,
        Self::JoinSplit,
        Self::JoinDiamonds,
        Self::JoinLayered,
        Self::JoinComb,
        Self::JoinChain,
    ];

    pub fn name(self) -> String {
        self.to_possible_value().unwrap().get_name().to_owned()
    }
}

#[derive(Args, Clone, Debug)]
pub struct Config {
    /// Total number of models, including the roots.
    #[arg(long, default_value_t = 64)]
    pub vertices: usize,
    /// Requested parent count for random DAGs and fan-in joins.
    #[arg(long, default_value_t = 4)]
    pub parents: usize,
    /// Number of models per layer in layered DAGs.
    #[arg(long, default_value_t = 8)]
    pub width: usize,
    /// Left/right seed count per root in grouped joins.
    #[arg(long, default_value_t = 16)]
    pub members: usize,
    #[arg(long, default_value_t = 17)]
    pub seed: u64,
    /// Initially marked root seeds, as an eight-bit decimal mask.
    #[arg(long, default_value_t = 255)]
    pub seed_mask: u32,
}

impl Default for Config {
    fn default() -> Self {
        Self {
            vertices: 64,
            parents: 4,
            width: 8,
            members: 16,
            seed: 17,
            seed_mask: 255,
        }
    }
}

impl Config {
    pub fn validate(&self) -> Result<(), &'static str> {
        if self.vertices == 0 || self.parents == 0 || self.width == 0 || self.members == 0 {
            return Err("vertices, parents, width and members must be positive");
        }
        if self.seed_mask > 255 {
            return Err("seed-mask must be between 0 and 255");
        }
        Ok(())
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Metrics {
    pub worlds: usize,
    pub morphisms: usize,
    pub owned_elements: usize,
    /// Elements and member rows introduced locally, before quotienting.
    pub local_size: usize,
    pub checksum: u64,
}

pub trait Workload {
    fn close(&mut self);
    fn verify(&self) -> Metrics;
}

pub trait Case {
    fn prepare(&self, engine: Engine) -> Box<dyn Workload + '_>;
}

pub fn case(family: Family, config: &Config) -> Box<dyn Case> {
    config.validate().expect("invalid benchmark configuration");
    match family {
        Family::ChainPlain => chain::case(config, chain::Variant::Plain),
        Family::ChainEquation => chain::case(config, chain::Variant::Equation),
        Family::DagForward => dag::case(config, dag::Variant::Forward),
        Family::DagLayered => dag::case(config, dag::Variant::Layered),
        Family::DagWide => dag::case(config, dag::Variant::Wide),
        Family::DagComb => dag::case(config, dag::Variant::Comb),
        Family::DagChain => dag::case(config, dag::Variant::Chain),
        Family::JoinFanout => join::case(config, join::Variant::Fanout),
        Family::JoinOverlap => join::case(config, join::Variant::Overlap),
        Family::JoinSplit => join::case(config, join::Variant::Split),
        Family::JoinDiamonds => join::case(config, join::Variant::Diamonds),
        Family::JoinLayered => join::case(config, join::Variant::Layered),
        Family::JoinComb => join::case(config, join::Variant::Comb),
        Family::JoinChain => join::case(config, join::Variant::Chain),
    }
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

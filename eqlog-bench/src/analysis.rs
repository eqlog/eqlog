use std::collections::BTreeMap;

use serde::{Deserialize, Serialize};

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct Pair {
    pub native_ns: u64,
    pub cow_ns: u64,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct Summary {
    pub native_ns: f64,
    pub cow_ns: f64,
    pub ratio: f64,
    pub lower: Option<f64>,
    pub upper: Option<f64>,
    pub samples: usize,
}

fn median(values: &mut [f64]) -> f64 {
    values.sort_unstable_by(f64::total_cmp);
    let middle = values.len() / 2;
    if values.len() % 2 == 0 {
        (values[middle - 1] + values[middle]) / 2.0
    } else {
        values[middle]
    }
}

fn interval_index(samples: usize) -> usize {
    // Starting at the mode avoids underflow in the binomial tails for large n.
    let mode = samples / 2;
    let mut weights = vec![0.0; samples + 1];
    weights[mode] = 1.0;
    for k in (1..=mode).rev() {
        weights[k - 1] = weights[k] * k as f64 / (samples - k + 1) as f64;
    }
    for k in mode..samples {
        weights[k + 1] = weights[k] * (samples - k) as f64 / (k + 1) as f64;
    }
    // Binomial ranks avoid a Gaussian noise assumption; pairs must be independent.
    let limit = weights.iter().sum::<f64>() * 0.025;
    let mut tail = 0.0;
    let mut index = 0;
    for (k, weight) in weights.iter().take(samples.div_ceil(2)).enumerate() {
        tail += weight;
        if tail > limit {
            break;
        }
        index = k;
    }
    index
}

pub fn summarize(pairs: &[Pair]) -> Summary {
    assert!(!pairs.is_empty(), "at least one timing pair is required");
    let mut native = Vec::with_capacity(pairs.len());
    let mut cow = Vec::with_capacity(pairs.len());
    let mut ratios = Vec::with_capacity(pairs.len());
    for pair in pairs {
        assert!(
            pair.native_ns > 0 && pair.cow_ns > 0,
            "benchmark durations must be positive"
        );
        native.push(pair.native_ns as f64);
        cow.push(pair.cow_ns as f64);
        ratios.push(pair.native_ns as f64 / pair.cow_ns as f64);
    }
    let ratio = median(&mut ratios);
    let (lower, upper) = if pairs.len() < 7 {
        (None, None)
    } else {
        let index = interval_index(pairs.len());
        (Some(ratios[index]), Some(ratios[pairs.len() - index - 1]))
    };
    Summary {
        native_ns: median(&mut native),
        cow_ns: median(&mut cow),
        ratio,
        lower,
        upper,
        samples: pairs.len(),
    }
}

fn valid_interval(summary: &Summary) -> Option<(f64, f64)> {
    let lower = summary.lower?;
    let upper = summary.upper?;
    let positive = [
        summary.native_ns,
        summary.cow_ns,
        summary.ratio,
        lower,
        upper,
    ];
    if summary.samples < 7
        || positive
            .iter()
            .any(|value| !value.is_finite() || *value <= 0.0)
        || lower > summary.ratio
        || upper < summary.ratio
    {
        return None;
    }
    Some((lower, upper))
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct RelativeGrowth {
    pub per_doubling: f64,
    pub lower: Option<f64>,
    pub upper: Option<f64>,
}

pub fn relative_growth(before: &Summary, after: &Summary, size_factor: f64) -> RelativeGrowth {
    assert!(
        size_factor.is_finite() && size_factor > 1.0,
        "size factor must be finite and greater than one"
    );
    assert!(
        before.ratio.is_finite()
            && before.ratio > 0.0
            && after.ratio.is_finite()
            && after.ratio > 0.0,
        "timing ratios must be finite and positive"
    );
    let exponent = 2.0_f64.ln() / size_factor.ln();
    let per_doubling = (after.ratio / before.ratio).powf(exponent);
    assert!(
        per_doubling.is_finite(),
        "normalized ratio growth overflowed"
    );
    // Treating the earlier median as exact would overstate a change.
    let (lower, upper) = match valid_interval(before).zip(valid_interval(after)) {
        Some(((before_lower, before_upper), (after_lower, after_upper))) => {
            let lower = (after_lower / before_upper).powf(exponent);
            let upper = (after_upper / before_lower).powf(exponent);
            if lower.is_finite() && upper.is_finite() {
                (Some(lower), Some(upper))
            } else {
                (None, None)
            }
        }
        None => (None, None),
    };
    RelativeGrowth {
        per_doubling,
        lower,
        upper,
    }
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct Expected {
    pub lower: f64,
    pub upper: f64,
    pub reference: Summary,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Verdict {
    Within,
    Slower,
    Faster,
    Uncertain,
}

impl Expected {
    pub fn from_summary(reference: Summary, tolerance: f64) -> Result<Self, String> {
        if !tolerance.is_finite() || !(0.0..1.0).contains(&tolerance) {
            return Err("relative tolerance must be finite and in [0, 1)".to_owned());
        }
        let (lower, upper) = match valid_interval(&reference) {
            Some(interval) => interval,
            None => {
                return Err(
                    "a valid median interval from at least seven samples is required".to_owned(),
                );
            }
        };
        let lower = lower.min(reference.ratio * (1.0 - tolerance));
        let upper = upper.max(reference.ratio * (1.0 + tolerance));
        if !upper.is_finite() || lower <= 0.0 || lower >= upper {
            return Err("ratio tolerance produced an invalid expectation interval".to_owned());
        }
        Ok(Self {
            lower,
            upper,
            reference,
        })
    }

    pub fn check(&self, summary: &Summary) -> Verdict {
        assert!(
            self.lower.is_finite()
                && self.upper.is_finite()
                && self.lower > 0.0
                && self.lower < self.upper,
            "invalid baseline expectation interval"
        );
        let (lower, upper) = match valid_interval(summary) {
            Some(interval) => interval,
            None => return Verdict::Uncertain,
        };
        if lower >= self.lower && upper <= self.upper {
            Verdict::Within
        } else if lower > self.upper {
            Verdict::Slower
        } else if upper < self.lower {
            Verdict::Faster
        } else {
            Verdict::Uncertain
        }
    }
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct BaselineCase {
    pub metrics: crate::Metrics,
    pub expected: Expected,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct Baseline {
    pub host: String,
    pub compiler: String,
    pub cases: BTreeMap<String, BaselineCase>,
}

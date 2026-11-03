use std::collections::BTreeMap;
use std::error::Error;
use std::fs;
use std::hint::black_box;
use std::io::ErrorKind;
use std::os::unix::fs::MetadataExt;
use std::path::{Path, PathBuf};
use std::process::Command;
#[cfg(not(feature = "allocations"))]
use std::time::Instant;

use eqlog_bench::analysis::{self, Baseline, BaselineCase, Expected, Summary, Verdict};
use eqlog_bench::{Case, Metrics, Workload};
use serde::Serialize;

#[cfg(feature = "allocations")]
#[path = "allocations.rs"]
mod allocations;

pub type Result<T> = std::result::Result<T, Box<dyn Error>>;

pub struct Options {
    pub samples: usize,
    pub output: Option<PathBuf>,
    pub baseline: Option<PathBuf>,
    pub check: bool,
    pub update: bool,
    pub tolerance: f64,
    pub check_scaling: bool,
    pub max_ratio_growth: f64,
}

#[derive(Serialize)]
pub struct Label {
    pub case: String,
    pub shape: String,
    pub parameters: BTreeMap<String, u64>,
    pub cow_bound: &'static str,
}

impl Label {
    fn same_series(&self, other: &Self, axis: &str) -> bool {
        self.case == other.case
            && self.shape == other.shape
            && self
                .parameters
                .iter()
                .filter(|(key, _)| key.as_str() != axis)
                .eq(other
                    .parameters
                    .iter()
                    .filter(|(key, _)| key.as_str() != axis))
    }
}

#[derive(Serialize)]
struct Measurement {
    ns: Option<u64>,
    allocations: Option<u128>,
    allocated_bytes: Option<u128>,
}

#[derive(Serialize)]
struct Sample {
    native: Measurement,
    cow: Measurement,
}

#[derive(Serialize)]
struct Growth {
    axis: &'static str,
    from: u64,
    to: u64,
    native_factor: f64,
    cow_factor: f64,
    ratio_factor: f64,
    relative: analysis::RelativeGrowth,
    status: &'static str,
}

#[derive(Serialize)]
struct Cell {
    label: Label,
    metrics: Metrics,
    samples: Vec<Sample>,
    summary: Option<Summary>,
    growth: Vec<Growth>,
    status: &'static str,
}

#[derive(Serialize)]
struct Report {
    host: String,
    compiler: String,
    allocation_instrumentation: bool,
    cells: Vec<Cell>,
}

pub struct Runner {
    options: Options,
    report: Report,
    baseline: Baseline,
    failures: Vec<String>,
}

fn sample<W: Workload>(mut workload: W) -> (Measurement, Metrics) {
    #[cfg(not(feature = "allocations"))]
    let measured = {
        let start = Instant::now();
        black_box(&mut workload).close();
        let ns = u64::try_from(start.elapsed().as_nanos()).unwrap();
        Measurement {
            ns: Some(ns),
            allocations: None,
            allocated_bytes: None,
        }
    };
    #[cfg(feature = "allocations")]
    let measured = {
        let (count, bytes) = allocations::measure(|| black_box(&mut workload).close());
        Measurement {
            ns: None,
            allocations: Some(count),
            allocated_bytes: Some(bytes),
        }
    };
    let metrics = workload.verify();
    (measured, metrics)
}

#[cfg(feature = "allocations")]
fn median(values: impl Iterator<Item = u128>) -> u128 {
    let mut values: Vec<_> = values.collect();
    values.sort_unstable();
    values[values.len() / 2]
}

fn host() -> Result<String> {
    let cpu = fs::read_to_string("/proc/cpuinfo")?;
    let model = cpu
        .lines()
        .find_map(|line| line.strip_prefix("model name\t: "))
        .ok_or("CPU model is absent from /proc/cpuinfo")?;
    let memory = fs::read_to_string("/proc/meminfo")?;
    let total = memory
        .lines()
        .find(|line| line.starts_with("MemTotal:"))
        .ok_or("MemTotal is absent from /proc/meminfo")?;
    Ok(format!("{}; {model}; {total}", std::env::consts::ARCH))
}

fn destination(path: &Path) -> Result<PathBuf> {
    match fs::canonicalize(path) {
        Ok(path) => return Ok(path),
        Err(error) => {
            if error.kind() != ErrorKind::NotFound {
                return Err(error.into());
            }
        }
    }
    let parent = path
        .parent()
        .filter(|parent| !parent.as_os_str().is_empty())
        .unwrap_or(Path::new("."));
    let parent = fs::canonicalize(parent)?;
    let path = parent.join(path.file_name().ok_or("output path needs a file name")?);
    match fs::symlink_metadata(&path) {
        Ok(metadata) => {
            if metadata.file_type().is_symlink() {
                return destination(&parent.join(fs::read_link(&path)?));
            }
        }
        Err(error) => {
            if error.kind() != ErrorKind::NotFound {
                return Err(error.into());
            }
        }
    }
    Ok(path)
}

fn identity(path: &Path) -> Result<Option<(u64, u64)>> {
    match fs::metadata(path) {
        Ok(metadata) => Ok(Some((metadata.dev(), metadata.ino()))),
        Err(error) => {
            if error.kind() == ErrorKind::NotFound {
                Ok(None)
            } else {
                Err(error.into())
            }
        }
    }
}

impl Runner {
    pub fn new(options: Options) -> Result<Self> {
        if options.samples == 0 {
            return Err("samples must be positive".into());
        }
        if options.check && options.update {
            return Err("choose check or update-baseline".into());
        }
        if options.baseline.is_some() && !options.check && !options.update {
            return Err("--baseline requires --check or --update-baseline".into());
        }
        if (options.check || options.update) && options.baseline.is_none() {
            return Err("check and update-baseline require --baseline PATH".into());
        }
        if let (Some(output), Some(baseline)) = (&options.output, &options.baseline) {
            let output = destination(output)?;
            let baseline = destination(baseline)?;
            let output_id = identity(&output)?;
            let baseline_id = identity(&baseline)?;
            let same_inode = output_id.is_some() && output_id == baseline_id;
            if output == baseline || same_inode {
                return Err("report output must not alias the performance baseline".into());
            }
        }
        if !options.tolerance.is_finite() || !(0.0..1.0).contains(&options.tolerance) {
            return Err("tolerance must be finite and in [0, 1)".into());
        }
        if !options.max_ratio_growth.is_finite() || options.max_ratio_growth < 1.0 {
            return Err("max-ratio-growth must be finite and at least one".into());
        }
        if options.check || options.update || options.check_scaling {
            if cfg!(feature = "allocations") || cfg!(debug_assertions) {
                return Err(
                    "performance expectations require an optimized, uninstrumented build".into(),
                );
            }
            if options.samples < 7 {
                return Err("performance expectations require at least seven samples".into());
            }
        }
        let host = host()?;
        let rustc = Command::new("rustc").arg("-Vv").output()?;
        if !rustc.status.success() {
            return Err("rustc -Vv failed".into());
        }
        let compiler = String::from_utf8(rustc.stdout)?;
        let mut baseline = Baseline {
            host: host.clone(),
            compiler: compiler.clone(),
            cases: BTreeMap::new(),
        };
        if let Some(path) = &options.baseline {
            match fs::read(path) {
                Ok(bytes) => {
                    baseline = serde_json::from_slice(&bytes)?;
                    if baseline.host != host || baseline.compiler != compiler {
                        return Err(
                            "baseline host/compiler differs; select a different baseline file"
                                .into(),
                        );
                    }
                }
                Err(error) => {
                    if error.kind() != ErrorKind::NotFound || !options.update {
                        return Err(error.into());
                    }
                }
            }
        }
        let report = Report {
            host,
            compiler,
            allocation_instrumentation: cfg!(feature = "allocations"),
            cells: Vec::new(),
        };
        #[cfg(not(feature = "allocations"))]
        println!("case\tshape\tparameters\tnative_ms\tcow_ms\tratio\tratio_interval\tstatus");
        #[cfg(feature = "allocations")]
        println!(
            "case\tshape\tparameters\tnative_allocations\tcow_allocations\tnative_bytes\tcow_bytes"
        );
        Ok(Self {
            options,
            report,
            baseline,
            failures: Vec::new(),
        })
    }

    pub fn run<C: Case>(&mut self, label: Label, case: C) -> Result<()> {
        let name = &label.case;
        let shape = &label.shape;
        let mut samples = Vec::with_capacity(self.options.samples);
        let mut expected = None;
        for index in 0..self.options.samples {
            let (native, cow) = if index % 2 == 0 {
                let native = sample(case.native());
                let cow = sample(case.cow());
                (native, cow)
            } else {
                let cow = sample(case.cow());
                let native = sample(case.native());
                (native, cow)
            };
            assert_eq!(native.1, cow.1, "{name}: native and COW disagree");
            if let Some(previous) = &expected {
                assert_eq!(&native.1, previous, "samples disagree");
            } else {
                expected = Some(native.1);
            }
            samples.push(Sample {
                native: native.0,
                cow: cow.0,
            });
        }
        let metrics = expected.unwrap();
        let parameters = serde_json::to_string(&label.parameters)?;
        #[cfg(not(feature = "allocations"))]
        let summary = Some(analysis::summarize(
            &samples
                .iter()
                .map(|pair| analysis::Pair {
                    native_ns: pair.native.ns.unwrap(),
                    cow_ns: pair.cow.ns.unwrap(),
                })
                .collect::<Vec<_>>(),
        ));
        #[cfg(feature = "allocations")]
        let summary: Option<Summary> = None;
        let mut status = "measured";
        let mut growth = Vec::new();
        if let Some(summary) = &summary {
            let key = format!("{name}/{shape}/{parameters}");
            for axis in ["vertices", "members", "keys", "depth"] {
                let Some(&to) = label.parameters.get(axis) else {
                    continue;
                };
                let previous = self.report.cells.iter().rev().find(|cell| {
                    label.same_series(&cell.label, axis)
                        && cell
                            .label
                            .parameters
                            .get(axis)
                            .is_some_and(|&value| value < to)
                });
                let Some(previous) = previous else {
                    continue;
                };
                let before = previous.summary.as_ref().unwrap();
                let from = previous.label.parameters[axis];
                let relative = analysis::relative_growth(before, summary, to as f64 / from as f64);
                let scaling_status = if self.options.check_scaling {
                    match relative.lower.zip(relative.upper) {
                        Some((lower, upper)) => {
                            if lower > self.options.max_ratio_growth {
                                "scaling-worse"
                            } else if upper <= self.options.max_ratio_growth {
                                "scaling-within"
                            } else {
                                "scaling-uncertain"
                            }
                        }
                        None => "scaling-uncertain",
                    }
                } else {
                    "measured"
                };
                if self.options.check_scaling && scaling_status != "scaling-within" {
                    self.failures
                        .push(format!("{key} {axis}: {scaling_status}"));
                }
                growth.push(Growth {
                    axis,
                    from,
                    to,
                    native_factor: summary.native_ns / before.native_ns,
                    cow_factor: summary.cow_ns / before.cow_ns,
                    ratio_factor: summary.ratio / before.ratio,
                    relative,
                    status: scaling_status,
                });
            }
            if self.options.update {
                self.baseline.cases.insert(
                    key,
                    BaselineCase {
                        metrics: metrics.clone(),
                        expected: Expected::from_summary(summary.clone(), self.options.tolerance)?,
                    },
                );
                status = "updated";
            } else if self.options.check {
                status = match self.baseline.cases.get(&key) {
                    Some(reference) => {
                        if metrics != reference.metrics {
                            "input-changed"
                        } else {
                            match reference.expected.check(summary) {
                                Verdict::Within => "within",
                                Verdict::Slower => "slower",
                                Verdict::Faster => "faster",
                                Verdict::Uncertain => "uncertain",
                            }
                        }
                    }
                    None => "missing",
                };
                if status != "within" {
                    self.failures.push(format!("{key}: {status}"));
                }
            }
            let native_ms = summary.native_ns / 1e6;
            let cow_ms = summary.cow_ns / 1e6;
            let interval = match summary.lower.zip(summary.upper) {
                Some((lower, upper)) => format!("[{lower:.3},{upper:.3}]"),
                None => "insufficient samples".to_owned(),
            };
            let ratio = summary.ratio;
            println!(
                "{name}\t{shape}\t{parameters}\t{native_ms:.3}\t{cow_ms:.3}\t{ratio:.3}\t{interval}\t{status}"
            );
            for Growth {
                axis,
                from,
                to,
                native_factor,
                cow_factor,
                ratio_factor,
                relative,
                status,
            } in &growth
            {
                let per_doubling = relative.per_doubling;
                eprintln!(
                    "{name} {axis} {from}->{to}: native x{native_factor:.2}, COW x{cow_factor:.2}, ratio x{ratio_factor:.2}; per doubling x{per_doubling:.2} ({status})"
                );
            }
        }
        #[cfg(feature = "allocations")]
        {
            let native_calls = median(samples.iter().map(|pair| pair.native.allocations.unwrap()));
            let cow_calls = median(samples.iter().map(|pair| pair.cow.allocations.unwrap()));
            let native_bytes = median(
                samples
                    .iter()
                    .map(|pair| pair.native.allocated_bytes.unwrap()),
            );
            let cow_bytes = median(samples.iter().map(|pair| pair.cow.allocated_bytes.unwrap()));
            println!(
                "{name}\t{shape}\t{parameters}\t{native_calls}\t{cow_calls}\t{native_bytes}\t{cow_bytes}"
            );
        }
        self.report.cells.push(Cell {
            label,
            metrics,
            samples,
            summary,
            growth,
            status,
        });
        Ok(())
    }

    pub fn finish(self) -> Result<()> {
        if self.options.check_scaling && self.report.cells.iter().all(|cell| cell.growth.is_empty())
        {
            return Err("scaling checks require at least two sizes on one parameter axis".into());
        }
        if let Some(path) = self.options.output {
            fs::write(path, serde_json::to_vec_pretty(&self.report)?)?;
        }
        if !self.failures.is_empty() {
            let failures = self.failures.join("\n");
            return Err(format!("performance expectations changed:\n{failures}\nUse more samples for uncertain results; refresh deliberate changes with --update-baseline.").into());
        }
        if self.options.update {
            fs::write(
                self.options.baseline.unwrap(),
                serde_json::to_vec_pretty(&self.baseline)?,
            )?;
        }
        Ok(())
    }
}

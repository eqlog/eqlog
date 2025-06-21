use clap::{Parser, ValueEnum};
use eqlog::{process, ComponentConfig, Config};
use std::path::PathBuf;
use std::process::ExitCode;

#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, ValueEnum)]
enum BuildType {
    /// Generate module-only build
    Module,
    /// Generate component libraries
    Component,
}

impl Into<clap::builder::OsStr> for BuildType {
    fn into(self) -> clap::builder::OsStr {
        match self {
            BuildType::Module => "module".into(),
            BuildType::Component => "component".into(),
        }
    }
}

#[derive(Parser)]
#[command(author, version, about, long_about = None)]
struct Cli {
    /// Input directory containing eqlog files
    src: PathBuf,

    /// Output directory for generated Rust files
    out: PathBuf,

    /// Build type (module or component)
    #[arg(long, value_enum, default_value_t = BuildType::Module)]
    build_type: BuildType,

    /// Output directory for component libraries (required for component build)
    #[arg(
        long,
        required_if_eq("build_type", "component"),
        requires_if(BuildType::Component, "build_type")
    )]
    component_out_dir: Option<PathBuf>,

    /// Path to rustc compiler (only used for component build)
    #[arg(
        long,
        default_value = "rustc",
        requires_if(BuildType::Component, "build_type")
    )]
    rustc_path: PathBuf,

    /// Enable debug symbols (only used for component build)
    #[arg(
        long,
        default_value_t = true,
        requires_if(BuildType::Component, "build_type")
    )]
    debug: bool,

    /// Optimization level (only used for component build)
    #[arg(
        long,
        default_value = "0",
        requires_if(BuildType::Component, "build_type")
    )]
    opt_level: String,

    /// Path to the runtime rlib (only used for component build)
    #[arg(
        long,
        required_if_eq("build_type", "component"),
        requires_if(BuildType::Component, "build_type")
    )]
    runtime_rlib_path: Option<PathBuf>,
}

fn main() -> ExitCode {
    let cli = Cli::parse();

    let component_build = match cli.build_type {
        BuildType::Component => Some(ComponentConfig {
            component_out_dir: cli
                .component_out_dir
                .expect("Clap checks that this is present in component builds"),
            rustc_path: cli.rustc_path,
            debug: cli.debug,
            opt_level: cli.opt_level,
            runtime_rlib_path: cli
                .runtime_rlib_path
                .expect("Clap checks that this is present in component builds"),
        }),
        BuildType::Module => None,
    };

    let config = Config {
        in_dir: cli.src,
        out_dir: cli.out,
        component_build,
    };

    match process(&config) {
        Ok(()) => (),
        Err(err) => {
            eprintln!("{err}");
            return ExitCode::FAILURE;
        }
    }

    ExitCode::SUCCESS
}

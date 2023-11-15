use clap::Parser;
use eqlog_tree::{process, Config};
use std::path::PathBuf;
use std::process::ExitCode;

#[derive(Parser)]
#[command(author, version, about, long_about = None)]
struct Cli {
    src: PathBuf,
    out: PathBuf,
}

fn main() -> ExitCode {
    let Cli { src, out } = Cli::parse();
    let config = Config {
        in_dir: src,
        out_dir: out,
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

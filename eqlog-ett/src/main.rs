use std::env;
use std::fs;
use std::process::ExitCode;

fn run() -> Result<(), Box<dyn std::error::Error>> {
    let paths: Vec<_> = env::args().skip(1).collect();
    if paths.is_empty() {
        return Err("usage: eqlog-ett FILE...".into());
    }
    let mut source = String::new();
    for path in paths {
        source.push_str(&fs::read_to_string(path)?);
        source.push('\n');
    }
    let checked = eqlog_ett::check(&source)?;
    for name in &checked.declarations {
        println!("checked {name}");
    }
    // The process exits next; freeing the many allocations of the closed
    // model one by one would only delay that.
    std::mem::forget(checked.model);
    Ok(())
}

fn main() -> ExitCode {
    match run() {
        Ok(()) => ExitCode::SUCCESS,
        Err(error) => {
            eprintln!("{error}");
            ExitCode::FAILURE
        }
    }
}

use std::env;
use std::fs;
use std::process::ExitCode;

fn run() -> Result<(), Box<dyn std::error::Error>> {
    let mut args = env::args().skip(1);
    let path = args.next().ok_or("usage: eqlog-ett FILE")?;
    if args.next().is_some() {
        return Err("usage: eqlog-ett FILE".into());
    }
    let source = fs::read_to_string(&path)?;
    let checked = eqlog_ett::check(&source)?;
    for name in checked.declarations {
        println!("checked {name}");
    }
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

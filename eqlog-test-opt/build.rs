use std::env;
use std::fs;
use std::io::ErrorKind;
use std::path::PathBuf;

use eqlog::{CompileOptions, Config, EvaluationMode, ModelMode};
use indoc::formatdoc;

mod theories;

fn setting(name: &str, default: u64) -> u64 {
    println!("cargo:rerun-if-env-changed={name}");
    env::var_os(name)
        .map(|value| {
            value
                .to_str()
                .expect("setting must be UTF-8")
                .parse()
                .expect("setting must be a u64")
        })
        .unwrap_or(default)
}

fn main() -> eqlog::Result<()> {
    println!("cargo:rerun-if-changed=build.rs");
    println!("cargo:rerun-if-changed=theories.rs");
    println!("cargo:rerun-if-changed=corpus");
    println!("cargo:rerun-if-env-changed=EQLOG_OPT_CASE");
    let seed = setting("EQLOG_OPT_THEORY_SEED", 0);
    let count = setting("EQLOG_OPT_THEORIES", 2);
    let out = PathBuf::from(env::var_os("OUT_DIR").expect("Cargo sets OUT_DIR"));
    let mut cases = Vec::new();
    if let Some(path) = env::var_os("EQLOG_OPT_CASE") {
        let path = fs::canonicalize(path)?;
        let display = path.display();
        println!("cargo:rerun-if-changed={display}");
        cases.push(("replay".to_owned(), fs::read_to_string(path)?, None));
    } else {
        for i in 0..count {
            let seed = seed.wrapping_add(i);
            for indexed in [false, true] {
                cases.push((
                    format!("generated_{seed}_{indexed}"),
                    theories::generate(seed, indexed),
                    None,
                ));
            }
        }
        let mut paths = fs::read_dir("corpus")?
            .map(|entry| entry.map(|entry| entry.path()))
            .collect::<Result<Vec<_>, _>>()?;
        paths.sort();
        for path in paths {
            if path.extension().is_some_and(|ext| ext == "eql") {
                let name = path.file_stem().unwrap().to_str().unwrap().to_owned();
                let trace = match fs::read_to_string(path.with_extension("json")) {
                    Ok(trace) => Some(trace),
                    Err(error) if error.kind() == ErrorKind::NotFound => None,
                    Err(error) => return Err(error.into()),
                };
                cases.push((name, fs::read_to_string(path)?, trace));
            }
        }
    }
    assert!(
        !cases.is_empty(),
        "the optimization suite must contain a theory"
    );
    let mut modules = String::new();
    let mut registrations = Vec::new();
    for (i, (name, source, trace)) in cases.iter().enumerate() {
        let mut variants = Vec::new();
        for (mode, (evaluation_mode, model_mode)) in [
            (EvaluationMode::Naive, ModelMode::Desugared),
            (EvaluationMode::SemiNaive, ModelMode::Desugared),
            (EvaluationMode::Naive, ModelMode::Native),
            (EvaluationMode::SemiNaive, ModelMode::Native),
        ]
        .into_iter()
        .enumerate()
        {
            let module = format!("case_{i}_mode_{mode}");
            let model = format!("Case{i}Mode{mode}");
            let input = out.join(format!("input_{i}_{mode}"));
            fs::create_dir_all(&input)?;
            fs::write(input.join(format!("{module}.eql")), source)?;
            let output = out.join(&module);
            eqlog::process(&Config {
                in_dir: input.clone(),
                out_dir: output.clone(),
                component_build: None,
                options: CompileOptions {
                    evaluation_mode,
                    model_mode,
                },
            })?;
            let path = output.join(format!("{module}.eql.rs"));
            let path = path.to_str().unwrap();
            modules.push_str(&formatdoc! {"
                #[allow(dead_code, unused_imports, non_snake_case)]
                mod {module} {{ include!({path:?}); }}
                impl Evaluator for {module}::{model} {{
                    fn canonicalize_compiled(&mut self) {{ self.canonicalize(); }}
                    fn close_bounded(&mut self) {{
                        let iterations = std::cell::Cell::new(0);
                        let exhausted = self.close_until(|_| {{
                            iterations.set(iterations.get() + 1);
                            iterations.get() > 512
                        }});
                        assert!(!exhausted, \"closure exceeded 512 iterations\");
                    }}
                }}
            "});
            let name = format!("{evaluation_mode:?}/{model_mode:?}");
            variants.push(format!("Variant {{ name: {name:?}, create: create::<{module}::{model}>, signature: {module}::{model}::dynamic_signature() }}"));
        }
        let variants = variants.join(",\n");
        registrations.push(format!(
            "Case {{ name: {name:?}, source: {source:?}, trace: {trace:?}, variants: [{variants}] }}"
        ));
    }
    let registrations = registrations.join(",\n");
    modules.push_str(&formatdoc! {"
        fn cases() -> Vec<Case> {{
            vec![{registrations}]
        }}
    "});
    fs::write(out.join("cases.rs"), modules)?;
    Ok(())
}

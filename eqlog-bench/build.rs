use std::env;
use std::fs;
use std::path::PathBuf;

use eqlog::{CompileOptions, Config};
use indoc::formatdoc;

fn pipeline() -> String {
    let mut source = String::from("type Item; pred seed(Item);\n");
    for i in 0..24 {
        let input = if i == 0 {
            "seed".to_owned()
        } else {
            let previous = i - 1;
            format!("step_{previous}")
        };
        source.push_str(&formatdoc! {"
            pred step_{i}(Item);
            rule advance_{i} {{ if {input}(x); then step_{i}(x); }}
        "});
    }
    source
}

fn independent() -> String {
    let mut source = String::from("type Item;\n");
    for i in 0..16 {
        source.push_str(&formatdoc! {"
            pred seed_{i}(Item);
            pred middle_{i}(Item);
            pred output_{i}(Item);
            rule begin_{i} {{ if seed_{i}(x); then middle_{i}(x); }}
            rule end_{i} {{ if middle_{i}(x); then output_{i}(x); }}
        "});
    }
    source
}

fn main() -> eqlog::Result<()> {
    println!("cargo:rerun-if-changed=build.rs");
    println!("cargo:rerun-if-changed=theories");
    let out = PathBuf::from(env::var_os("OUT_DIR").expect("Cargo sets OUT_DIR"));
    let sources = [
        ("pipeline", pipeline()),
        ("independent", independent()),
        ("graph", fs::read_to_string("theories/graph.eql")?),
        ("nested", fs::read_to_string("theories/nested.eql")?),
        ("equality", fs::read_to_string("theories/equality.eql")?),
    ];
    let mut modules = String::new();
    let mut cases = Vec::new();
    for (source_index, (name, source)) in sources.iter().enumerate() {
        let module = format!("bench_{source_index}");
        let model = format!("Bench{source_index}");
        let input = out.join(format!("input_{module}"));
        fs::create_dir_all(&input)?;
        fs::write(input.join(format!("{module}.eql")), source)?;
        let output = out.join(&module);
        eqlog::process(&Config {
            in_dir: input,
            out_dir: output.clone(),
            component_build: None,
            options: CompileOptions::default(),
        })?;
        let path = output.join(format!("{module}.eql.rs"));
        let path = path.to_str().unwrap();
        modules.push_str(&formatdoc! {"
            mod {module} {{ include!({path:?}); }}
            impl Evaluator for {module}::{model} {{
                fn new() -> Self {{ Self::new() }}
                fn close(&mut self) {{ self.close(); }}
            }}
        "});
        let workloads = if *name == "graph" {
            vec!["model_chain", "model_cycle"]
        } else {
            vec![*name]
        };
        for workload in workloads {
            cases.push(format!(
                "Case {{ name: {workload:?}, prepare: workloads::{workload}::<{module}::{model}> }}"
            ));
        }
    }
    let cases = cases.join(",\n");
    modules.push_str(&formatdoc! {"
        pub fn cases() -> Vec<Case> {{ vec![{cases}] }}
    "});
    fs::write(out.join("cases.rs"), modules)?;
    Ok(())
}

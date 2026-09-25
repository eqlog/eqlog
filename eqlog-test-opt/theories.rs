use indoc::formatdoc;
use rand::{rngs::StdRng, RngExt, SeedableRng};

struct Predicate {
    name: String,
    arguments: Vec<usize>,
}

fn atom(rng: &mut StdRng, predicate: &Predicate, variables: &[Vec<String>]) -> String {
    let arguments: Vec<_> = predicate
        .arguments
        .iter()
        .map(|&sort| variables[sort][rng.random_range(0..variables[sort].len())].clone())
        .collect();
    let name = &predicate.name;
    let arguments = arguments.join(", ");
    format!("{name}({arguments})")
}

pub fn generate(seed: u64, indexed: bool) -> String {
    let mut rng = StdRng::seed_from_u64(seed);
    let sorts = rng.random_range(1..=3);
    let mut source = String::new();
    for sort in 0..sorts {
        source.push_str(&formatdoc! {"
            type T{sort};
            func f_{sort}(T{sort}) -> T{sort};
        "});
    }
    let predicates: Vec<_> = (0..rng.random_range(3..=6))
        .map(|i| Predicate {
            name: format!("p_{i}"),
            arguments: (0..rng.random_range(0..=3))
                .map(|_| rng.random_range(0..sorts))
                .collect(),
        })
        .collect();
    for predicate in &predicates {
        let name = &predicate.name;
        let arguments = predicate
            .arguments
            .iter()
            .map(|sort| format!("T{sort}"))
            .collect::<Vec<_>>()
            .join(", ");
        source.push_str(&format!("pred {name}({arguments});\n"));
    }
    for rule in 0..rng.random_range(4..=9) {
        let variables: Vec<Vec<String>> = (0..sorts)
            .map(|sort| {
                (0..rng.random_range(1..=2))
                    .map(|i| format!("x_{sort}_{i}"))
                    .collect()
            })
            .collect();
        let mut body = String::new();
        for _ in 0..rng.random_range(1..=3) {
            let predicate = &predicates[rng.random_range(0..predicates.len())];
            let premise = atom(&mut rng, predicate, &variables);
            body.push_str(&format!("    if {premise};\n"));
        }
        if rng.random_bool(0.25) {
            let sort = rng.random_range(0..sorts);
            let x = &variables[sort][0];
            body.push_str(&format!("    if f_{sort}({x})!;\n"));
        }
        if rng.random_bool(0.2) {
            let sort = rng.random_range(0..sorts);
            let x = &variables[sort][0];
            let y = variables[sort].last().unwrap();
            body.push_str(&format!("    then {x} = {y};\n"));
        } else {
            let predicate = &predicates[rng.random_range(0..predicates.len())];
            let conclusion = atom(&mut rng, predicate, &variables);
            body.push_str(&format!("    then {conclusion};\n"));
        }
        source.push_str(&format!("rule r_{rule} {{\n"));
        for (sort, names) in variables.iter().enumerate() {
            for name in names {
                if body.contains(name) {
                    source.push_str(&format!("    if {name}: T{sort};\n"));
                }
            }
        }
        source.push_str(&body);
        source.push_str("}\n");
    }
    if indexed {
        source = formatdoc! {"
            model World {{
            {source}
            }}
        "};
        for sort in 0..sorts {
            source.push_str(&formatdoc! {"
                rule image_{sort} {{
                    if h: Mor(World);
                    if w = dom(h);
                    if x: w.T{sort};
                    if cod(h)!;
                    then h.T{sort}(x)!;
                }}
            "});
        }
    }
    source
}

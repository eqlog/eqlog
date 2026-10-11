use eqlog_runtime::CompiledModel;

use crate::long_pipeline::LongPipeline;

#[test]
fn long_join_pipeline_resumes_when_a_missing_input_arrives() {
    let mut model = LongPipeline::new();
    let signature = LongPipeline::dynamic_signature();
    let el = signature.type_named("El").unwrap();
    let a = model.new_element(el, &[]).unwrap();
    let b = model.new_element(el, &[]).unwrap();
    let seed = signature.relation_named("seed").unwrap();
    model.insert(seed, &[a]).unwrap();
    model.insert(seed, &[b]).unwrap();
    let count = signature
        .relations()
        .filter(|(_, relation)| relation.name.starts_with("gate_"))
        .count();
    assert!(count > 1);
    let missing = count / 2;
    for i in 0..count {
        let gate = signature.relation_named(&format!("gate_{i}")).unwrap();
        if i != missing {
            model.insert(gate, &[a]).unwrap();
        }
        model.insert(gate, &[b]).unwrap();
    }
    model.close();
    let snapshot = model.to_dynamic();
    for i in 0..count {
        let step = signature.relation_named(&format!("step_{i}")).unwrap();
        assert_eq!(snapshot.contains(step, &[a]).unwrap(), i < missing);
        assert!(snapshot.contains(step, &[b]).unwrap());
    }

    let gate = signature
        .relation_named(&format!("gate_{missing}"))
        .unwrap();
    model.insert(gate, &[a]).unwrap();
    model.close();
    let snapshot = model.to_dynamic();
    for i in 0..count {
        let step = signature.relation_named(&format!("step_{i}")).unwrap();
        assert!(snapshot.contains(step, &[a]).unwrap());
        assert!(snapshot.contains(step, &[b]).unwrap());
    }
}

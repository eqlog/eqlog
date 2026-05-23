use crate::consts::*;
use maplit::btreeset;
use std::collections::BTreeSet;

#[test]
fn ambient_and_member_consts() {
    let mut model = Consts::new();

    assert_eq!(model.foo(), None);
    assert_eq!(model.iter_foo().count(), 0);
    assert_eq!(model.main_container(), None);

    model.close();

    let foo = model.foo().expect("foo should be defined after close");
    let foos: BTreeSet<El> = model.iter_foo().collect();
    assert_eq!(foos, btreeset! {foo});
    assert!(model.present(foo));

    let container = model
        .main_container()
        .expect("main_container should be defined after close");
    let containers: BTreeSet<Container> = model.iter_main_container().collect();
    assert_eq!(containers, btreeset! {container});

    let inner = model
        .inner(container)
        .expect("member const should be defined after close");
    let inners: BTreeSet<(Container, Elem)> = model.iter_inner().collect();
    assert_eq!(inners, btreeset! {(container, inner)});
    assert!(model.inner_present(container, inner));
}

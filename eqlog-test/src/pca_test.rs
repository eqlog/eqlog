use crate::pca::*;

fn id(pca: &Pca) -> Option<El> {
    let s = pca.s()?;
    let k = pca.k()?;
    let sk = pca.app(s, k)?;
    let skk = pca.app(sk, k)?;
    Some(skk)
}

fn define_id(pca: &mut Pca) -> El {
    let s = pca.define_s();
    let k = pca.define_k();
    let sk = pca.define_app(s, k);
    let skk = pca.define_app(sk, k);
    skk
}

fn second(pca: &Pca) -> Option<El> {
    let k = pca.k()?;
    let i = id(pca)?;
    let ki = pca.app(k, i)?;
    Some(ki)
}

fn define_second(pca: &mut Pca) -> El {
    let k = pca.define_k();
    let i = define_id(pca);
    let ki = pca.define_app(k, i);
    ki
}

#[test]
fn test_pca_identity_is_defined() {
    let mut pca = Pca::new();
    assert!(pca.close_until(|pca| id(pca).is_some()));
}

#[test]
fn test_pca_identity() {
    let mut pca = Pca::new();
    let x = pca.new_el();
    let i = define_id(&mut pca);

    assert!(pca.close_until(|pca| {
        let ix = match pca.app(i, x) {
            Some(ix) => ix,
            None => return false,
        };
        pca.are_equal_el(ix, x)
    }));
}

#[test]
fn test_pca_second_is_defined() {
    let mut pca = Pca::new();
    assert!(pca.close_until(|pca| second(pca).is_some()));
}

#[test]
fn test_pca_second() {
    let mut pca = Pca::new();
    let x = pca.new_el();
    let y = pca.new_el();
    let snd = define_second(&mut pca);

    assert!(pca.close_until(|pca| {
        let snd_x = match pca.app(snd, x) {
            Some(snd_x) => snd_x,
            None => return false,
        };
        let snd_x_y = match pca.app(snd_x, y) {
            Some(snd_x_y) => snd_x_y,
            None => return false,
        };
        pca.are_equal_el(snd_x_y, y)
    }));
}

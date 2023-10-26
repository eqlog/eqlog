use sha2::{Digest, Sha256};

#[cfg(feature = "rebuild")]
fn digest_source() -> String {
    use std::process::Command;

    let git_rev_parse_head_output = Command::new("git")
        .args(["rev-parse", "HEAD"])
        .output()
        .unwrap();
    assert!(git_rev_parse_head_output.status.success());

    let git_diff_output = Command::new("git").args(["diff"]).output().unwrap();
    assert!(git_diff_output.status.success());

    let binary_digest = Sha256::new()
        .chain_update(&git_rev_parse_head_output.stdout)
        .chain_update(&git_diff_output.stdout)
        .finalize();
    base16ct::upper::encode_string(&binary_digest)
}

#[cfg(not(feature = "rebuild"))]
fn digest_source() -> String {
    use std::env;

    let version = env::var("CARGO_PKG_VERSION").unwrap();
    let binary_digest = Sha256::digest(version.as_bytes());
    base16ct::upper::encode_string(&binary_digest)
}

fn main() {
    lalrpop::process_root().unwrap();
    println!("cargo:rustc-env=EQLOG_SOURCE_DIGEST={}", digest_source());
}

use std::fs;
use std::path::Path;

use toml::Table;

#[test]
fn eqlog_pins_eqlog_runtime_to_its_own_version() {
    let workspace_root = Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .expect("eqlog manifest dir should have a parent");

    let workspace_manifest = read_toml(workspace_root.join("Cargo.toml"));
    let eqlog_manifest = read_toml(workspace_root.join("eqlog/Cargo.toml"));
    let runtime_manifest = read_toml(workspace_root.join("eqlog-runtime/Cargo.toml"));

    let workspace_version = workspace_package_version(&workspace_manifest);
    let eqlog_version = package_version(&eqlog_manifest, workspace_version);
    let runtime_version = package_version(&runtime_manifest, workspace_version);

    assert_eq!(
        eqlog_version, runtime_version,
        "eqlog and eqlog-runtime package versions must match"
    );

    let dependencies = table_field(&eqlog_manifest, "dependencies");
    let runtime_dep = dependencies
        .get("eqlog-runtime")
        .expect("dependencies.eqlog-runtime should be set")
        .as_table()
        .expect("eqlog-runtime dependency should use an inline table");
    assert_eq!(
        string_field(runtime_dep, "path"),
        "../eqlog-runtime",
        "eqlog should depend on the local eqlog-runtime crate"
    );

    let expected_req = format!("={eqlog_version}");
    assert_eq!(
        string_field(runtime_dep, "version"),
        expected_req.as_str(),
        "eqlog's eqlog-runtime dependency must be pinned exactly to eqlog's version"
    );
}

fn read_toml(path: impl AsRef<Path>) -> Table {
    let path = path.as_ref();
    let content = fs::read_to_string(path).expect("manifest should be readable");
    content.parse().expect("manifest should parse as TOML")
}

fn workspace_package_version(workspace_manifest: &Table) -> &str {
    let workspace = table_field(workspace_manifest, "workspace");
    let package = table_field(workspace, "package");
    string_field(package, "version")
}

fn package_version<'a>(manifest: &'a Table, workspace_version: &'a str) -> &'a str {
    let package = table_field(manifest, "package");
    let version = package
        .get("version")
        .expect("package.version should be set");
    if let Some(version) = version.as_str() {
        return version;
    }

    if version
        .get("workspace")
        .expect("package.version.workspace should be set")
        .as_bool()
        .expect("package.version.workspace should be a bool")
    {
        return workspace_version;
    }

    panic!("package version should be a string or version.workspace = true");
}

fn table_field<'a>(table: &'a Table, field: &str) -> &'a Table {
    table
        .get(field)
        .expect("field should be set")
        .as_table()
        .expect("field should be a table")
}

fn string_field<'a>(table: &'a Table, field: &str) -> &'a str {
    table
        .get(field)
        .expect("field should be set")
        .as_str()
        .expect("field should be a string")
}

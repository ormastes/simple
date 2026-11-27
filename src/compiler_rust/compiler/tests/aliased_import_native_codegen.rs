#![cfg(feature = "llvm")]

use object::read::archive::ArchiveFile;
use object::{Object, ObjectSection, ObjectSymbol, RelocationTarget};
use simple_compiler::pipeline::{NativeBuildConfig, NativeProjectBuilder};
use std::path::{Path, PathBuf};

const OTHER: &str = "pub fn probe() -> text: \"OTHER\"\n";
const COLLISION: &str = r#"use other.{probe as aliased_probe}

fn probe() -> text: aliased_probe()

fn main():
    print(probe())
"#;
const NO_COLLISION: &str = r#"use other.{probe as aliased_probe}

fn probe_local() -> text: aliased_probe()

fn main():
    print(probe_local())
"#;

struct BootstrapEnvironment(Vec<(&'static str, Option<std::ffi::OsString>)>);

impl BootstrapEnvironment {
    fn enter() -> Self {
        let previous = ["SIMPLE_BOOTSTRAP", "SIMPLE_NO_STUB_FALLBACK"]
            .into_iter()
            .map(|name| {
                let value = std::env::var_os(name);
                std::env::set_var(name, "1");
                (name, value)
            })
            .collect();
        Self(previous)
    }
}

impl Drop for BootstrapEnvironment {
    fn drop(&mut self) {
        for (name, previous) in &self.0 {
            match previous {
                Some(value) => std::env::set_var(name, value),
                None => std::env::remove_var(name),
            }
        }
    }
}

fn build_archive(entry: &str) -> (tempfile::TempDir, PathBuf) {
    let temporary = tempfile::tempdir().unwrap();
    let source = temporary.path().join("src");
    std::fs::create_dir_all(&source).unwrap();
    std::fs::write(source.join("other.spl"), OTHER).unwrap();
    std::fs::write(source.join("main.spl"), entry).unwrap();
    let output = temporary.path().join("probe.a");
    let repo = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../..");
    let result = NativeProjectBuilder::new(repo, output.clone())
        .config(NativeBuildConfig {
            backend: "llvm".to_string(),
            runtime_bundle: "core-c-bootstrap".to_string(),
            entry_closure: true,
            emit_archive: true,
            parallel: false,
            num_threads: Some(1),
            cache_dir: Some(temporary.path().join("native-cache")),
            ..NativeBuildConfig::default()
        })
        .source_dir(source.clone())
        .entry_file(source.join("main.spl"))
        .build()
        .expect("native archive must build");
    assert_eq!(result.failed, 0, "native units must not fail: {:?}", result.failures);
    (temporary, output)
}

fn normalized_symbol_name(name: &str) -> &str {
    name.trim_start_matches('_')
}

fn wrapper_calls_other(archive_path: &Path, wrapper_suffix: &str) -> bool {
    let data = std::fs::read(archive_path).unwrap();
    let archive = ArchiveFile::parse(&*data).expect("parse native archive");
    for member in archive.members().flatten() {
        let bytes = member.data(&*data).unwrap();
        let Ok(file) = object::File::parse(bytes) else { continue };
        for wrapper in file.symbols().filter(|symbol| {
            symbol.is_definition()
                && symbol
                    .name()
                    .map(normalized_symbol_name)
                    .is_ok_and(|name| name == wrapper_suffix || name.ends_with(&format!("__{wrapper_suffix}")))
        }) {
            let Some(section_index) = wrapper.section_index() else { continue };
            let Ok(section) = file.section_by_index(section_index) else { continue };
            let start = wrapper.address();
            let end = if wrapper.size() > 0 {
                start + wrapper.size()
            } else {
                file.symbols()
                    .filter(|symbol| symbol.section_index() == Some(section_index) && symbol.address() > start)
                    .map(|symbol| symbol.address())
                    .min()
                    .unwrap_or_else(|| section.size())
            };
            for (offset, relocation) in section.relocations() {
                if offset < start || offset >= end {
                    continue;
                }
                let RelocationTarget::Symbol(index) = relocation.target() else { continue };
                let Ok(target) = file.symbol_by_index(index).and_then(|symbol| symbol.name()) else { continue };
                let target = normalized_symbol_name(target);
                if target == "other__probe" || target.ends_with("__other__probe") {
                    return true;
                }
            }
        }
    }
    false
}

#[test]
fn aliased_import_object_relocations_preserve_the_import_owner() {
    let _environment = BootstrapEnvironment::enter();

    let (_collision_tmp, collision_archive) = build_archive(COLLISION);
    assert!(
        wrapper_calls_other(&collision_archive, "main__probe"),
        "local probe wrapper must relocate to other__probe, not itself"
    );

    let (_control_tmp, control_archive) = build_archive(NO_COLLISION);
    assert!(
        wrapper_calls_other(&control_archive, "main__probe_local"),
        "renamed local wrapper must still relocate to other__probe"
    );
}

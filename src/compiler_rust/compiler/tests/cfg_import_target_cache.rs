use simple_compiler::interpreter::{
    clear_parsed_source_cache, shared_source, shared_source_for_target,
    shared_source_lookup_for_target, SharedSource,
};
use simple_common::target::{Target, TargetArch, TargetOS};

fn host_arch(os: TargetOS) -> Target {
    Target::new(TargetArch::host(), os)
}
use simple_parser::ast::{Module, Node};
use std::path::PathBuf;
use std::sync::{Arc, atomic::{AtomicUsize, Ordering}};

const CONDITIONAL: &str = "@when(os=\"windows\"):\npub struct WindowsOnly:\n    value: i64\n@else:\npub struct UnixOnly:\n    value: i64\n@end\n";
static NEXT: AtomicUsize = AtomicUsize::new(0);

struct Fixture(PathBuf);
impl Fixture {
    fn new(source: &str) -> Self {
        let path = std::env::temp_dir().join(format!("simple-cfg-import-{}-{}.spl", std::process::id(), NEXT.fetch_add(1, Ordering::Relaxed)));
        std::fs::write(&path, source).unwrap();
        Self(path)
    }
}
impl Drop for Fixture {
    fn drop(&mut self) { let _ = std::fs::remove_file(&self.0); }
}

#[test]
fn cfg_import_valid_os_branch_parses_through_shared_owner() {
    clear_parsed_source_cache();
    let fixture = Fixture::new(CONDITIONAL);
    let parsed = shared_source(&fixture.0);
    assert!(parsed.ast().is_some(), "valid OS-conditional import must parse through the shared import owner");
}

fn names(module: &Module) -> Vec<&str> {
    module.items.iter().filter_map(|node| match node {
        Node::Struct(declaration) => Some(declaration.name.as_str()),
        _ => None,
    }).collect()
}

#[test]
fn cfg_import_same_path_keeps_linux_and_windows_separate() {
    clear_parsed_source_cache();
    let fixture = Fixture::new(CONDITIONAL);
    let linux = shared_source_for_target(&fixture.0, host_arch(TargetOS::Linux)).ast().unwrap();
    assert!(shared_source_lookup_for_target(&fixture.0, host_arch(TargetOS::Windows)).is_none());
    let windows = shared_source_for_target(&fixture.0, host_arch(TargetOS::Windows)).ast().unwrap();
    assert_eq!(names(&linux), ["UnixOnly"]);
    assert_eq!(names(&windows), ["WindowsOnly"]);
    assert!(!Arc::ptr_eq(&linux, &windows));
    assert!(Arc::ptr_eq(&linux, &shared_source_for_target(&fixture.0, host_arch(TargetOS::Linux)).ast().unwrap()));
    assert!(Arc::ptr_eq(&windows, &shared_source_for_target(&fixture.0, host_arch(TargetOS::Windows)).ast().unwrap()));
}

#[test]
fn cfg_import_malformed_conditionals_fail_for_both_targets() {
    clear_parsed_source_cache();
    for source in ["@when(os=\"windows\"):\n", "@else:\n"] {
        let fixture = Fixture::new(source);
        for os in [TargetOS::Linux, TargetOS::Windows] {
            assert!(matches!(shared_source_for_target(&fixture.0, host_arch(os)), SharedSource::Parsed { ast: Err(_), .. }));
        }
    }
    // An unknown atom evaluates false (with a warning), the same as the lexer
    // and the pure-Simple preprocessor: the block is dropped, never an error.
    let unknown = Fixture::new("@when(os=\"unknown\"):\nval dropped = 1\n@end\n");
    for os in [TargetOS::Linux, TargetOS::Windows] {
        let ast = shared_source_for_target(&unknown.0, host_arch(os)).ast().expect("unknown atom selects nothing");
        assert!(ast.items.is_empty(), "{os:?}: {:?}", ast.items.len());
    }
}

#[test]
fn cfg_import_actual_release_os_owners_parse_for_each_target() {
    clear_parsed_source_cache();
    let root = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../..");
    for name in [
        "src/app/cli/shard_mem_clamp.spl",
        "src/lib/nogc_sync_mut/io/windows_image_owner.spl",
        "src/lib/nogc_sync_mut/io/path_identity.spl",
        "src/lib/nogc_sync_mut/io/path_identity_abi.spl",
        "src/lib/nogc_sync_mut/io/_PathIdentityPosix/errno_abi.spl",
    ] {
        for os in [TargetOS::Linux, TargetOS::Windows, TargetOS::FreeBSD, TargetOS::MacOS] {
            let parsed = shared_source_for_target(&root.join(name), host_arch(os));
            assert!(parsed.ast().is_some(), "{name} must parse for {os:?}");
        }
    }
}

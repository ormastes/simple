use super::*;
use std::io::Write;
use tempfile::NamedTempFile;

#[test]
fn test_check_valid_code() {
    let mut file = NamedTempFile::new().unwrap();
    writeln!(file, "fn main():\n    val x = 42\n    print(x)").unwrap();

    let result = check_file(file.path(), &[], false);
    assert_eq!(result.status, CheckStatus::Success);
    assert!(result.errors.is_empty());
}

#[test]
fn test_check_syntax_error() {
    let mut file = NamedTempFile::new().unwrap();
    writeln!(file, "fn main():\n    val x =").unwrap();

    let result = check_file(file.path(), &[], false);
    assert_eq!(result.status, CheckStatus::Error);
    assert!(!result.errors.is_empty());
    assert_eq!(result.errors[0].code.as_deref(), Some("E0002"));
    assert!(!result.errors[0].help.is_empty());
}

#[test]
fn test_check_literal_type_mismatch_is_error() {
    let mut file = NamedTempFile::new().unwrap();
    writeln!(file, "fn main():\n    val x: i64 = \"text\"").unwrap();

    let result = check_file(file.path(), &[], false);
    assert_eq!(result.status, CheckStatus::Error);
    assert_eq!(result.errors.len(), 1);
    assert_eq!(result.errors[0].severity, ErrorSeverity::Error);
    assert_eq!(result.errors[0].code.as_deref(), Some("E1003"));
    assert_eq!(result.errors[0].expected.as_deref(), Some("i64"));
    assert_eq!(result.errors[0].found.as_deref(), Some("text"));
    assert!(!result.errors[0].help.is_empty());
}

#[test]
fn test_check_matching_literal_type_annotation_succeeds() {
    let mut file = NamedTempFile::new().unwrap();
    writeln!(file, "fn main():\n    val x: i64 = 42").unwrap();

    let result = check_file(file.path(), &[], false);
    assert_eq!(result.status, CheckStatus::Success);
    assert!(result.errors.is_empty());
}

#[test]
fn test_check_unsuffixed_integer_annotation_family_succeeds() {
    let mut file = NamedTempFile::new().unwrap();
    writeln!(file, "fn main():\n    val x: i32 = 42\n    val y: u32 = 7").unwrap();

    let result = check_file(file.path(), &[], false);
    assert_eq!(result.status, CheckStatus::Success);
    assert!(result.errors.is_empty());
}

#[test]
fn test_check_unsuffixed_float_annotation_family_succeeds() {
    let mut file = NamedTempFile::new().unwrap();
    writeln!(file, "fn main():\n    val x: f32 = 1.5").unwrap();

    let result = check_file(file.path(), &[], false);
    assert_eq!(result.status, CheckStatus::Success);
    assert!(result.errors.is_empty());
}

#[test]
fn test_check_return_literal_type_mismatch_is_error() {
    let mut file = NamedTempFile::new().unwrap();
    writeln!(file, "fn value() -> bool:\n    return 1").unwrap();

    let result = check_file(file.path(), &[], false);
    assert_eq!(result.status, CheckStatus::Error);
    assert_eq!(result.errors.len(), 1);
    assert_eq!(result.errors[0].code.as_deref(), Some("E1003"));
    assert_eq!(result.errors[0].expected.as_deref(), Some("bool"));
    assert_eq!(result.errors[0].found.as_deref(), Some("i64"));
}

#[test]
fn test_check_common_aliases_and_nil_sentinels_succeed() {
    let mut file = NamedTempFile::new().unwrap();
    writeln!(
        file,
        "fn main():\n    val flag: Bool = true\n    val value: any = 1\n    val name: text = nil"
    )
    .unwrap();

    let result = check_file(file.path(), &[], false);
    assert_eq!(result.status, CheckStatus::Success);
    assert!(result.errors.is_empty());
}

#[test]
fn test_check_unresolved_import_is_warning() {
    let mut file = NamedTempFile::new().unwrap();
    writeln!(file, "use definitely.missing.module\nfn main():\n    val x = 1").unwrap();

    let result = check_file(file.path(), &[], false);
    assert_eq!(result.status, CheckStatus::Warning);
    assert_eq!(result.errors.len(), 1);
    assert_eq!(result.errors[0].severity, ErrorSeverity::Warning);
    assert_eq!(result.errors[0].code.as_deref(), Some("W0410"));
    assert!(!result.errors[0].help.is_empty());
}

#[test]
fn test_check_allows_local_manifest_exports() {
    let mut file = NamedTempFile::new().unwrap();
    writeln!(file, "export Foo, Bar\nfn Foo() -> i64:\n    return 1").unwrap();

    let result = check_file(file.path(), &[], false);
    assert!(result.errors.iter().all(|error| error.code.as_deref() != Some("W0412")));
}

#[test]
fn test_check_skips_legacy_string_import_paths() {
    let mut file = NamedTempFile::new().unwrap();
    writeln!(file, "import \"types\" as Types\nfn main():\n    val x = 1").unwrap();

    let result = check_file(file.path(), &[], false);
    assert!(result.errors.iter().all(|error| error.code.as_deref() != Some("W0410")));
}

#[test]
fn test_check_resolves_single_import_target_as_module_path() {
    let dir = tempfile::tempdir().unwrap();
    let lib_root = dir.path().join("src").join("lib");
    let aes = lib_root.join("common").join("aes");
    std::fs::create_dir_all(&aes).unwrap();
    std::fs::write(aes.join("utilities.spl"), "fn helper() -> i64:\n    return 1\n").unwrap();
    let cipher = aes.join("cipher.spl");
    std::fs::write(&cipher, "import aes/utilities\nfn main():\n    val x = 1\n").unwrap();

    let result = check_file(&cipher, &[lib_root], false);
    assert!(result.errors.iter().all(|error| error.code.as_deref() != Some("W0410")));
}

#[test]
fn test_check_std_spec_import_resolves_in_project() {
    let repo_root = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .and_then(Path::parent)
        .and_then(Path::parent)
        .expect("driver crate should live under repo/src/compiler_rust")
        .to_path_buf();
    let temp_root = repo_root.join("target/check-tests");
    std::fs::create_dir_all(&temp_root).unwrap();
    let mut file = tempfile::Builder::new().suffix(".spl").tempfile_in(temp_root).unwrap();
    writeln!(file, "use std.spec\nfn main():\n    val x = 1").unwrap();

    let result = check_file(file.path(), &[], false);
    assert_eq!(result.status, CheckStatus::Success);
    assert!(result.errors.is_empty());
}

#[test]
fn test_check_warns_for_gc_boundary_crossing() {
    let repo_root = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .and_then(Path::parent)
        .and_then(Path::parent)
        .expect("driver crate should live under repo/src/compiler_rust")
        .to_path_buf();
    let temp_dir = repo_root.join("target/gc-boundary-check-tests/src/lib/nogc_sync_mut");
    std::fs::create_dir_all(&temp_dir).unwrap();
    let path = temp_dir.join("gc_boundary_crossing.spl");
    std::fs::write(&path, "use std.gc_async_mut.task\n").unwrap();

    let result = check_file(&path, &[], false);
    assert_eq!(result.status, CheckStatus::Warning);
    assert!(result
        .errors
        .iter()
        .any(|error| error.code.as_deref() == Some("gc_boundary_crossing")));
}

#[test]
fn test_check_can_promote_gc_boundary_crossing_to_error() {
    let repo_root = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .and_then(Path::parent)
        .and_then(Path::parent)
        .expect("driver crate should live under repo/src/compiler_rust")
        .to_path_buf();
    let temp_dir = repo_root.join("target/gc-boundary-check-tests/src/lib/nogc_sync_mut");
    std::fs::create_dir_all(&temp_dir).unwrap();
    let path = temp_dir.join("gc_boundary_crossing_strict.spl");
    std::fs::write(&path, "use std.gc_async_mut.task\n").unwrap();

    let result = check_file(&path, &[], true);
    assert_eq!(result.status, CheckStatus::Error);
    assert!(result.errors.iter().any(|error| {
        error.code.as_deref() == Some("gc_boundary_crossing") && error.severity == ErrorSeverity::Error
    }));
}

#[test]
fn test_baremetal_target_enables_gc_boundary_errors() {
    let options = CheckOptions {
        target: Some(Target::parse("riscv64gc-unknown-none-elf").unwrap()),
        ..CheckOptions::default()
    };

    assert!(should_deny_gc_boundary_crossings(&options));
}

#[test]
fn test_hosted_target_keeps_gc_boundary_warnings_by_default() {
    let options = CheckOptions {
        target: Some(Target::parse("x86_64-unknown-linux-gnu").unwrap()),
        ..CheckOptions::default()
    };

    assert!(!should_deny_gc_boundary_crossings(&options));
}

#[test]
fn test_check_allows_common_runtime_import() {
    let temp_root = tempfile::tempdir().unwrap();
    let lib_root = temp_root.path().join("src/lib");
    let noalloc_root = lib_root.join("nogc_async_mut_noalloc");
    let common_root = lib_root.join("common");
    std::fs::create_dir_all(&noalloc_root).unwrap();
    std::fs::create_dir_all(&common_root).unwrap();
    let path = noalloc_root.join("common_import.spl");
    std::fs::write(&path, "use std.common.text\n").unwrap();
    std::fs::write(common_root.join("text.spl"), "fn value() -> i64:\n    return 1\n").unwrap();

    let result = check_file(&path, &[lib_root], false);
    assert!(result
        .errors
        .iter()
        .all(|error| error.code.as_deref() != Some("gc_boundary_crossing")));
    assert!(result.errors.iter().all(|error| error.code.as_deref() != Some("W0410")));
}

#[test]
fn test_strict_noalloc_check_rejects_reachable_allocating_family_import() {
    let temp_root = tempfile::tempdir().unwrap();
    let lib_root = temp_root.path().join("src/lib");
    let noalloc_root = lib_root.join("nogc_async_mut_noalloc");
    std::fs::create_dir_all(&noalloc_root).unwrap();
    let entry = noalloc_root.join("entry.spl");
    let helper = noalloc_root.join("helper.spl");
    std::fs::write(&entry, "use std.nogc_async_mut_noalloc.helper\n").unwrap();
    std::fs::write(&helper, "use std.gc_async_mut.task\n").unwrap();

    let result = check_file(&entry, &[lib_root], true);

    assert_eq!(result.status, CheckStatus::Error);
    assert!(result.errors.iter().any(|error| {
        error.code.as_deref() == Some("E0413")
            && error.message.contains("std.gc_async_mut.task")
            && error.file.ends_with("helper.spl")
    }));
}

#[test]
fn test_strict_noalloc_check_rejects_reachable_alloc_marker() {
    let temp_root = tempfile::tempdir().unwrap();
    let lib_root = temp_root.path().join("src/lib");
    let noalloc_root = lib_root.join("nogc_async_mut_noalloc");
    std::fs::create_dir_all(&noalloc_root).unwrap();
    let entry = noalloc_root.join("entry.spl");
    let helper = noalloc_root.join("helper.spl");
    std::fs::write(&entry, "use std.nogc_async_mut_noalloc.helper\n").unwrap();
    std::fs::write(&helper, "@alloc\nfn allocate() -> i64:\n    return 1\n").unwrap();

    let result = check_file(&entry, &[lib_root], true);

    assert_eq!(result.status, CheckStatus::Error);
    assert!(result.errors.iter().any(|error| {
        error.code.as_deref() == Some("E0413")
            && error.message.contains("allocation annotation")
            && error.file.ends_with("helper.spl")
    }));
}

#[test]
fn test_strict_noalloc_check_rejects_reachable_host_allocation_api() {
    let temp_root = tempfile::tempdir().unwrap();
    let lib_root = temp_root.path().join("src/lib");
    let noalloc_root = lib_root.join("nogc_async_mut_noalloc");
    std::fs::create_dir_all(&noalloc_root).unwrap();
    let entry = noalloc_root.join("entry.spl");
    let helper = noalloc_root.join("helper.spl");
    std::fs::write(&entry, "use std.nogc_async_mut_noalloc.helper\n").unwrap();
    std::fs::write(&helper, "extern fn malloc(size: i64) -> i64\n").unwrap();

    let result = check_file(&entry, &[lib_root], true);

    assert_eq!(result.status, CheckStatus::Error);
    assert!(result.errors.iter().any(|error| {
        error.code.as_deref() == Some("E0413")
            && error.message.contains("host allocation API")
            && error.file.ends_with("helper.spl")
    }));
}

#[test]
fn test_hosted_noalloc_check_does_not_follow_reachable_import_closure() {
    let temp_root = tempfile::tempdir().unwrap();
    let lib_root = temp_root.path().join("src/lib");
    let noalloc_root = lib_root.join("nogc_async_mut_noalloc");
    std::fs::create_dir_all(&noalloc_root).unwrap();
    let entry = noalloc_root.join("entry.spl");
    let helper = noalloc_root.join("helper.spl");
    std::fs::write(&entry, "use std.nogc_async_mut_noalloc.helper\n").unwrap();
    std::fs::write(&helper, "use std.gc_async_mut.task\n").unwrap();

    let result = check_file(&entry, &[lib_root], false);

    assert!(result.errors.iter().all(|error| error.code.as_deref() != Some("E0413")));
}

#[test]
fn test_strict_noalloc_check_allows_common_reachable_imports() {
    let temp_root = tempfile::tempdir().unwrap();
    let lib_root = temp_root.path().join("src/lib");
    let noalloc_root = lib_root.join("nogc_async_mut_noalloc");
    let common_root = lib_root.join("common");
    std::fs::create_dir_all(&noalloc_root).unwrap();
    std::fs::create_dir_all(&common_root).unwrap();
    let entry = noalloc_root.join("entry.spl");
    let common = common_root.join("safe_text.spl");
    std::fs::write(&entry, "use std.common.safe_text\n").unwrap();
    std::fs::write(&common, "fn value() -> i64:\n    return 1\n").unwrap();

    let result = check_file(&entry, &[lib_root], true);

    assert!(result.errors.iter().all(|error| error.code.as_deref() != Some("E0413")));
}

#[test]
fn test_check_nonexistent_file() {
    let path = PathBuf::from("/nonexistent/file.spl");
    let result = check_file(&path, &[], false);
    assert_eq!(result.status, CheckStatus::Error);
    assert_eq!(result.errors.len(), 1);
    assert_eq!(result.errors[0].code.as_deref(), Some("E0001"));
    assert!(result.errors[0].message.contains("cannot read file"));
    assert!(!result.errors[0].help.is_empty());
}

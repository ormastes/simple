
// =============================================================================
// Test Helpers
// =============================================================================

fn create_test_project() -> TempDir {
    TempDir::new().unwrap()
}

fn create_module_file(dir: &TempDir, path: &str, content: &str) {
    let full_path = dir.path().join(path);
    if let Some(parent) = full_path.parent() {
        fs::create_dir_all(parent).unwrap();
    }
    fs::write(full_path, content).unwrap();
}

// =============================================================================
// Feature #113: Module Resolution Tests
// =============================================================================

#[test]
fn resolution_file_module() {
    let dir = create_test_project();
    create_module_file(&dir, "src/utils.spl", "fn helper(): 42");

    let mut fs = FileSystem::new();
    fs.add_file(dir.path().join("src/utils.spl"));

    let mp = ModPath::parse("utils").unwrap();
    let root = dir.path().join("src");

    match resolve(&fs, &root, &mp) {
        ResolutionResult::Unique { kind, path } => {
            assert_eq!(kind, FileKind::File);
            assert!(path.to_string_lossy().contains("utils.spl"));
        }
        other => panic!("Expected Unique File, got {:?}", other),
    }
}

#[test]
fn resolution_directory_module() {
    let dir = create_test_project();
    create_module_file(&dir, "src/http/__init__.spl", "mod http\npub mod router");

    let mut fs = FileSystem::new();
    fs.add_file(dir.path().join("src/http/__init__.spl"));

    let mp = ModPath::parse("http").unwrap();
    let root = dir.path().join("src");

    match resolve(&fs, &root, &mp) {
        ResolutionResult::Unique { kind, path } => {
            assert_eq!(kind, FileKind::Directory);
            assert!(path.to_string_lossy().contains("__init__.spl"));
        }
        other => panic!("Expected Unique Directory, got {:?}", other),
    }
}

#[test]
fn resolution_nested_module() {
    let dir = create_test_project();
    create_module_file(&dir, "src/sys/http/router.spl", "struct Router:");

    let mut fs = FileSystem::new();
    fs.add_file(dir.path().join("src/sys/http/router.spl"));

    let mp = ModPath::parse("sys.http.router").unwrap();
    let root = dir.path().join("src");

    match resolve(&fs, &root, &mp) {
        ResolutionResult::Unique { kind, path } => {
            assert_eq!(kind, FileKind::File);
            assert!(path.to_string_lossy().contains("router.spl"));
        }
        other => panic!("Expected Unique File, got {:?}", other),
    }
}

#[test]
fn resolution_not_found() {
    let fs = FileSystem::new();
    let mp = ModPath::parse("nonexistent").unwrap();
    let root = Path::new("/fake/path");

    assert!(matches!(
        resolve(&fs, root, &mp),
        ResolutionResult::NotFound
    ));
}

#[test]
fn resolution_ambiguous_detected() {
    // This tests the formal model property: ambiguity is detected
    let dir = create_test_project();
    create_module_file(&dir, "src/foo.spl", "fn foo(): 1");
    create_module_file(&dir, "src/foo/__init__.spl", "mod foo");

    let mut fs = FileSystem::new();
    fs.add_file(dir.path().join("src/foo.spl"));
    fs.add_file(dir.path().join("src/foo/__init__.spl"));

    let mp = ModPath::parse("foo").unwrap();
    let root = dir.path().join("src");

    // Should detect ambiguity
    match resolve(&fs, &root, &mp) {
        ResolutionResult::Ambiguous {
            file_path,
            dir_path,
        } => {
            assert!(file_path.to_string_lossy().contains("foo.spl"));
            assert!(dir_path.to_string_lossy().contains("__init__.spl"));
        }
        other => panic!("Expected Ambiguous, got {:?}", other),
    }

    // Well-formedness check should fail
    assert!(!well_formed(&fs, &root));
}

#[test]
fn resolution_well_formed_filesystem() {
    let dir = create_test_project();
    create_module_file(&dir, "src/foo.spl", "fn foo(): 1");
    create_module_file(&dir, "src/bar/__init__.spl", "mod bar");

    let mut fs = FileSystem::new();
    fs.add_file(dir.path().join("src/foo.spl"));
    fs.add_file(dir.path().join("src/bar/__init__.spl"));

    let root = dir.path().join("src");

    // No ambiguity - well-formed
    assert!(well_formed(&fs, &root));
}

#[test]
fn resolution_crate_prefix() {
    let mp = ModPath::parse("crate.sys.http").unwrap();
    assert!(mp.is_absolute());

    let without_crate = mp.without_crate_prefix().unwrap();
    assert_eq!(without_crate.segments().len(), 2);
    assert_eq!(without_crate.segments()[0].name(), "sys");
    assert_eq!(without_crate.segments()[1].name(), "http");
}

// =============================================================================

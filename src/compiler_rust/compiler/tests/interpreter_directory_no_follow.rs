use simple_compiler::interpreter;
use simple_parser::Parser;
use std::path::Path;
fn probe(path: &Path) -> i32 {
    let quoted = serde_json::to_string(&path.to_string_lossy().to_string()).unwrap();
    let source = format!("extern fn rt_dir_is_real_no_follow(path: text) -> bool\nmain = if rt_dir_is_real_no_follow({quoted}): 1 else: 0\n");
    let module = Parser::new(&source).parse().unwrap();
    interpreter::evaluate_module(&module.items).unwrap()
}
#[test]
fn registered_directory_probe_accepts_only_existing_directories() {
    let root = tempfile::tempdir().unwrap();
    assert_eq!(probe(root.path()), 1);
    let file = root.path().join("file");
    std::fs::write(&file, b"data").unwrap();
    assert_eq!(probe(&file), 0);
    assert_eq!(probe(&root.path().join("missing")), 0);
    assert_eq!(probe(Path::new("")), 0);
}
#[test]
#[cfg(unix)]
fn registered_directory_probe_rejects_final_and_dangling_symlinks() {
    let root = tempfile::tempdir().unwrap();
    let link = root.path().join("link");
    std::os::unix::fs::symlink(root.path(), &link).unwrap();
    assert_eq!(probe(&link), 0);
    std::fs::remove_file(&link).unwrap();
    std::os::unix::fs::symlink(root.path().join("missing"), &link).unwrap();
    assert_eq!(probe(&link), 0);
}

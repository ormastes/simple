//! Windows interpreter snapshot operations retain the native no-follow contract.
//!
//! Twin of `interpreter_snapshot_links.rs` (unix). Symlink creation needs the
//! SeCreateSymbolicLink privilege (or Developer Mode); when the probe shows
//! this host cannot create symlinks, the create-dependent assertions collapse
//! to the fail-closed guarantee (`create` returns -1) instead of flaking.
#![cfg(windows)]
use simple_compiler::interpreter;
use simple_parser::Parser;
use std::os::windows::fs::MetadataExt;
use std::path::{Path, PathBuf};

fn invoke(name: &str, values: &[&str], kind: i32) -> i32 {
    let args=values.iter().map(|v| serde_json::to_string(v).unwrap()).collect::<Vec<_>>().join(", ");
    let params=if values.len()==1 { "path: text" } else { "root: text, link: text, target: text" };
    let source=format!("extern fn {name}({params}, kind: i32) -> i32\nmain = {name}({args}, {kind})\n");
    interpreter::evaluate_module(&Parser::new(&source).parse().unwrap().items).unwrap()
}
// The contract speaks drive-absolute forward-slash paths on Windows.
fn contract(path: &Path) -> String {
    path.to_str().unwrap().replace('\\', "/")
}
fn link_op(name: &str, root: &Path, link: &Path, target: &str, kind: i32) -> i32 {
    let root = contract(root);
    let link = contract(link);
    invoke(name, &[&root, &link, target], kind)
}
const CREATE: &str="rt_snapshot_symlink_create_nofollow_v1";
const MATCH: &str="rt_snapshot_symlink_match_nofollow_v1";
const READONLY: &str="rt_snapshot_readonly_nofollow_v1";

#[test]
fn snapshot_links_reject_escapes_wrong_kind_and_missing_targets() {
    let root=tempfile::tempdir().unwrap();
    std::fs::write(root.path().join("target"),b"data").unwrap();
    std::fs::create_dir(root.path().join("dir")).unwrap();
    let link=root.path().join("link");
    for target in ["../outside", "/tmp/outside", "", "target/", "dir//x", "a\\b", "a:b"] {
        assert_eq!(link_op(CREATE,root.path(),&link,target,1),-1, "target {target:?}");
    }
    assert_eq!(link_op(CREATE,root.path(),&link,"target",2),-1);
    assert_eq!(link_op(CREATE,root.path(),&link,"dir",3),-1);
    assert_eq!(link_op(MATCH,root.path(),&link,"target",1),-1);
}

#[test]
fn snapshot_match_reports_honest_not_a_link_for_plain_files() {
    let root=tempfile::tempdir().unwrap();
    let file=root.path().join("file");
    std::fs::write(&file,b"data").unwrap();
    // A real file is not a reparse point: match must say "not a link".
    assert_eq!(link_op(MATCH,root.path(),&file,"file",1),-1);
}

#[test]
fn snapshot_readonly_seals_real_files_and_rejects_other_kinds() {
    let root=tempfile::tempdir().unwrap();
    let file=root.path().join("file");
    std::fs::write(&file,b"data").unwrap();
    assert_eq!(invoke(READONLY,&[contract(&file).as_str()],1),0);
    let attrs=std::fs::metadata(&file).unwrap().file_attributes();
    assert_ne!(attrs & 0x1,0,"FILE_ATTRIBUTE_READONLY must be set");
    // Directories cannot be physically sealed on Windows.
    assert_eq!(invoke(READONLY,&[contract(&file).as_str()],2),-1);
    let dir=root.path().join("dir");
    std::fs::create_dir(&dir).unwrap();
    assert_eq!(invoke(READONLY,&[contract(&dir).as_str()],2),-1);
    let missing = contract(&dir) + "/missing";
    assert_eq!(invoke(READONLY,&[missing.as_str()],1),-1);
}

#[test]
fn snapshot_links_create_exclusively_and_read_exact_raw_target() {
    let root=tempfile::tempdir().unwrap();
    std::fs::write(root.path().join("target"),b"data").unwrap();
    let link=root.path().join("link");
    // Probe whether this host can create symlinks at all (privilege/Developer
    // Mode). Without it, `create` must at least fail closed instead of lying.
    let probe: PathBuf = root.path().join("probe");
    let can_symlink = std::os::windows::fs::symlink_file(root.path().join("target"), &probe).is_ok();
    let _ = std::fs::remove_file(&probe);
    let created = link_op(CREATE,root.path(),&link,"target",1);
    if !can_symlink {
        assert_eq!(created,-1,"without the symlink privilege create must fail closed");
        return;
    }
    assert_eq!(created,0);
    assert_eq!(link_op(MATCH,root.path(),&link,"target",1),0);
    // Raw link text is compared byte-exact: './target' is a different link.
    assert_eq!(link_op(MATCH,root.path(),&link,"./target",1),-1);
    // Exclusive: a second create over the same leaf is rejected.
    assert_eq!(link_op(CREATE,root.path(),&link,"target",1),-1);
}

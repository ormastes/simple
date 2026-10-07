//! Interpreter snapshot operations retain the native no-follow contract.
#![cfg(unix)]
use simple_compiler::interpreter;
use simple_parser::Parser;
use std::path::Path;
use std::os::unix::fs::{symlink, PermissionsExt};

fn invoke(name: &str, values: &[&str], kind: i32) -> i32 {
    let args=values.iter().map(|v| serde_json::to_string(v).unwrap()).collect::<Vec<_>>().join(", ");
    let params=if values.len()==1 { "path: text" } else { "root: text, link: text, target: text" };
    let source=format!("extern fn {name}({params}, kind: i32) -> i32\nmain = {name}({args}, {kind})\n");
    interpreter::evaluate_module(&Parser::new(&source).parse().unwrap().items).unwrap()
}
fn link_op(name: &str, root: &Path, link: &Path, target: &str, kind: i32) -> i32 {
    invoke(name, &[root.to_str().unwrap(),link.to_str().unwrap(),target],kind)
}
const CREATE: &str="rt_snapshot_symlink_create_nofollow_v1";
const MATCH: &str="rt_snapshot_symlink_match_nofollow_v1";
const READONLY: &str="rt_snapshot_readonly_nofollow_v1";

#[test]
fn snapshot_links_create_exclusively_and_read_exact_raw_target() {
    let root=tempfile::tempdir().unwrap();
    std::fs::write(root.path().join("target"),b"data").unwrap();
    let link=root.path().join("link");
    assert_eq!(link_op(CREATE,root.path(),&link,"target",1),0);
    assert_eq!(std::fs::read_link(&link).unwrap(),Path::new("target"));
    assert_eq!(link_op(MATCH,root.path(),&link,"target",1),0);
    assert_eq!(link_op(MATCH,root.path(),&link,"./target",1),-1);
    assert_eq!(link_op(CREATE,root.path(),&link,"target",1),-1);
    assert_eq!(link_op(CREATE,root.path(),&root.path().join("chain"),"link",1),-1);
}
#[test]
fn snapshot_links_reject_escapes_wrong_kind_and_symlink_ancestors() {
    let root=tempfile::tempdir().unwrap();
    std::fs::write(root.path().join("target"),b"data").unwrap();
    std::fs::create_dir(root.path().join("dir")).unwrap();
    let link=root.path().join("link");
    for target in ["../outside","/tmp/outside","", "target/", "dir//x"] {
        assert_eq!(link_op(CREATE,root.path(),&link,target,1),-1);
    }
    assert_eq!(link_op(CREATE,root.path(),&link,"target",2),-1);
    assert_eq!(link_op(CREATE,root.path(),&link,"dir",3),-1);
    assert_eq!(link_op(CREATE,root.path(),&link,"dir",2),0);
    assert_eq!(link_op(MATCH,root.path(),&link,"dir",2),0);
    assert_eq!(link_op(CREATE,root.path(),&link.join("nested"),"../target",1),-1);
    let alias=root.path().join("alias"); symlink(root.path().join("dir"),&alias).unwrap();
    assert_eq!(link_op(CREATE,root.path(),&alias.join("nested"),"../target",1),-1);
    assert_eq!(link_op(CREATE,root.path(),&root.path().join("dir/nested"),"../target",1),0);
}
#[test]
fn snapshot_readonly_seals_real_objects_and_rejects_symlinks() {
    let root=tempfile::tempdir().unwrap(); let file=root.path().join("file");
    std::fs::write(&file,b"data").unwrap();
    assert_eq!(invoke(READONLY,&[file.to_str().unwrap()],1),0);
    assert_eq!(std::fs::metadata(&file).unwrap().permissions().mode() & 0o222,0);
    assert_eq!(invoke(READONLY,&[file.to_str().unwrap()],2),-1);
    let alias=root.path().join("alias"); symlink(&file,&alias).unwrap();
    assert_eq!(invoke(READONLY,&[alias.to_str().unwrap()],1),-1);
    let dir=root.path().join("dir"); std::fs::create_dir(&dir).unwrap();
    assert_eq!(invoke(READONLY,&[dir.to_str().unwrap()],2),0);
    assert_eq!(std::fs::metadata(&dir).unwrap().permissions().mode() & 0o222,0);
    std::fs::set_permissions(&dir,std::fs::Permissions::from_mode(0o700)).unwrap();
}

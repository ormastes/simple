//! `lib` / `std` / `std_lib` are reserved stdlib roots: `use lib.{X}` never
//! imports a sibling `lib.spl`. The interpreter and the flattening module
//! loader already refuse it ("Cannot resolve module: lib"), but HIR import
//! resolution used to load the sibling's TYPES for a bare `lib` root. JIT
//! `run` then compiled `Acc(total: 1).add(2)` with no method body and died at
//! runtime: "Function 'Acc.add' not found" (exit 70). A bare reserved root
//! that is shadowed by a sibling module must be a compile-time resolve error.
//! Cross-module classes under an ordinary module name are pinned green.

use std::collections::HashSet;
use std::path::{Path, PathBuf};

const CLASS: &str = "class Acc:\n    total: i64\n    fn add(k: i64) -> i64:\n        return self.total + k\n    static fn make(k: i64) -> Acc:\n        return Acc(total: k)\n\nexport Acc\n";

fn project(tag: &str, module: &str, main_src: &str) -> (PathBuf, PathBuf) {
    let dir = std::env::temp_dir().join(format!("reserved-root-{tag}-{}", std::process::id()));
    std::fs::create_dir_all(&dir).expect("temp dir");
    std::fs::write(dir.join(format!("{module}.spl")), CLASS).expect("write module");
    let main = dir.join("main.spl");
    std::fs::write(&main, main_src).expect("write main");
    (dir, main)
}

fn per_file(main: &Path) -> Result<(), String> {
    let ast = simple_parser::Parser::new(&std::fs::read_to_string(main).unwrap())
        .parse()
        .map_err(|e| format!("parse: {e:?}"))?;
    simple_compiler::hir::lower_with_context(&ast, main).map(|_| ()).map_err(|e| format!("{e}"))
}

fn flattened(main: &Path) -> Result<(), String> {
    let ast = simple_compiler::pipeline::module_loader::load_module_with_imports(main, &mut HashSet::new())
        .map_err(|e| format!("load: {e:?}"))?;
    simple_compiler::hir::lower(&ast).map(|_| ()).map_err(|e| format!("{e}"))
}

#[test]
fn bare_reserved_root_shadowed_by_sibling_module_is_a_resolve_error() {
    let mut bad = Vec::new();
    for root in ["lib", "std", "std_lib"] {
        let (dir, main) = project(
            &format!("shadow-{root}"),
            root,
            &format!("use {root}.{{Acc}}\n\nfn main() -> i64:\n    val a = Acc(total: 1)\n    return a.add(2)\n"),
        );
        let r = per_file(&main);
        let _ = std::fs::remove_dir_all(&dir);
        match &r {
            Err(e) if e.contains("cannot resolve import") && e.contains("reserved stdlib root") => {}
            other => bad.push(format!("`use {root}.{{Acc}}` beside {root}.spl: expected a resolve error, got {other:?}")),
        }
    }
    assert!(bad.is_empty(), "{}", bad.join("\n"));
}

#[test]
fn cross_module_class_methods_lower_under_an_ordinary_module_name() {
    let (dir, main) = project(
        "accmod",
        "accmod",
        "use accmod.{Acc}\n\nfn main() -> i64:\n    val a = Acc.make(5)\n    return a.add(2) + Acc(total: 1).add(3)\n",
    );
    let lanes = [("per-file", per_file(&main)), ("flattened", flattened(&main))];
    let _ = std::fs::remove_dir_all(&dir);
    let bad: Vec<String> = lanes
        .iter()
        .filter_map(|(lane, r)| r.as_ref().err().map(|e| format!("{lane}: {e}")))
        .collect();
    assert!(bad.is_empty(), "{}", bad.join("\n"));
}

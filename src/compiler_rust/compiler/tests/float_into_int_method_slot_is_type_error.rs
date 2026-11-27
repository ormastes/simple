//! Owner decision 2026-11-24 (#11333): a float passed to an int-typed
//! parameter is a TYPE ERROR. This file extends that rule from free functions
//! and same-file instance methods to methods whose receiver class lives in
//! another module, static (class) methods, and trait methods.
//! Bug: doc/08_tracking/bug/float_passed_to_int_typed_param_or_return_engines_disagree_2026-11-24.md

use std::path::{Path, PathBuf};

const LIB: &str = "pub class Acc:\n    total: i64\n    fn add(k: i64) -> i64:\n        return self.total + k\n    fn scale(f: f64) -> f64:\n        return f\n    static fn make(k: i64) -> Acc:\n        return Acc(total: k)\n\nexport Acc\n";

fn scratch(tag: &str) -> PathBuf {
    let dir = std::env::temp_dir().join(format!("float-int-method-{tag}-{}", std::process::id()));
    std::fs::create_dir_all(&dir).expect("temp dir");
    std::fs::write(dir.join("accmod.spl"), LIB).expect("write accmod");
    dir
}

/// Lower `main_src` (importing `accmod`) on the per-file lane, which resolves
/// the imported class through `lower_with_context` (native-build / JIT HIR
/// lane). The module must not be named `lib`/`std`/`std_lib`: those are
/// reserved stdlib roots (see `reserved_stdlib_root_sibling_module.rs`).
fn lower_cross(tag: &str, main_src: &str) -> Result<(), String> {
    let dir = scratch(tag);
    let main_path = dir.join("main.spl");
    std::fs::write(&main_path, main_src).expect("write main");
    let r = per_file(&main_path);
    let _ = std::fs::remove_dir_all(&dir);
    r
}

fn per_file(main_path: &Path) -> Result<(), String> {
    let ast = simple_parser::Parser::new(&std::fs::read_to_string(main_path).unwrap())
        .parse()
        .map_err(|e| format!("parse: {e:?}"))?;
    simple_compiler::hir::lower_with_context(&ast, main_path).map(|_| ()).map_err(|e| format!("{e}"))
}

fn lower_one(src: &str) -> Result<(), String> {
    let ast = simple_parser::Parser::new(src).parse().map_err(|e| format!("parse: {e:?}"))?;
    simple_compiler::hir::lower(&ast).map(|_| ()).map_err(|e| format!("{e}"))
}

fn rejected(label: &str, r: &Result<(), String>) -> Option<String> {
    match r {
        Err(e) if e.contains("mismatch") => None,
        other => Some(format!("{label}: expected a type mismatch, got {other:?}")),
    }
}

fn accepted(label: &str, r: &Result<(), String>) -> Option<String> {
    match r {
        Ok(()) => None,
        Err(e) => Some(format!("{label}: must still compile, got {e}")),
    }
}

#[test]
fn float_into_int_slot_of_cross_module_method_is_rejected() {
    let mut bad = Vec::new();
    for (tag, src) in [
        ("inst", "use accmod.{Acc}\n\nfn main() -> i64:\n    val a = Acc(total: 1)\n    return a.add(1.5)\n"),
        ("stat", "use accmod.{Acc}\n\nfn main() -> i64:\n    val a = Acc.make(2.5)\n    return a.total\n"),
    ] {
        bad.extend(rejected(&format!("cross-module {tag}"), &lower_cross(tag, src)));
    }
    assert!(bad.is_empty(), "{}", bad.join("\n"));
}

#[test]
fn float_into_int_slot_of_static_and_trait_methods_is_rejected() {
    let cases = [
        (
            "same-file static method",
            "class B:\n    v: i64\n    static fn make(k: i64) -> B:\n        return B(v: k)\n\nfn main() -> i64:\n    val b = B.make(2.5)\n    return b.v\n",
        ),
        (
            "trait impl method on a concrete receiver",
            "trait Taker:\n    fn take(k: i64) -> i64\n\nclass T:\n    v: i64\n\nimpl Taker for T:\n    fn take(k: i64) -> i64:\n        return self.v + k\n\nfn main() -> i64:\n    val t = T(v: 1)\n    return t.take(4.5)\n",
        ),
        (
            "trait method on a trait-typed receiver",
            "trait Taker:\n    fn take(k: i64) -> i64\n\nclass T:\n    v: i64\n\nimpl Taker for T:\n    fn take(k: i64) -> i64:\n        return self.v + k\n\nfn use_dyn(t: Taker) -> i64:\n    return t.take(4.5)\n\nfn main() -> i64:\n    return use_dyn(T(v: 1))\n",
        ),
        (
            "inherent impl-block method",
            "class U:\n    v: i64\n\nimpl U:\n    fn put(k: i64) -> i64:\n        return self.v + k\n\nfn main() -> i64:\n    val u = U(v: 1)\n    return u.put(4.5)\n",
        ),
    ];
    let bad: Vec<String> = cases.iter().filter_map(|(label, src)| rejected(label, &lower_one(src))).collect();
    assert!(bad.is_empty(), "{}", bad.join("\n"));
}

#[test]
fn int_and_explicit_casts_into_method_slots_still_compile() {
    let mut bad = Vec::new();
    bad.extend(accepted(
        "cross-module ok",
        &lower_cross(
            "ok",
            "use accmod.{Acc}\n\nfn main() -> i64:\n    val a = Acc.make(3)\n    val s = a.scale(2)\n    return a.add(2) + a.add(1.5 as i64) + s.to_i64()\n",
        ),
    ));
    for (label, src) in [
        (
            "same-file static + int->f64",
            "class B:\n    v: i64\n    static fn make(k: i64) -> B:\n        return B(v: k)\n    fn half(f: f64) -> f64:\n        return f / 2.0\n\nfn main() -> i64:\n    val b = B.make(2)\n    return b.v + b.half(3).to_i64() + B.make(2.5 as i64).v\n",
        ),
        (
            "trait impl with int arg and f64 slot",
            "trait Taker:\n    fn take(k: i64) -> i64\n    fn mix(f: f64) -> f64\n\nclass T:\n    v: i64\n\nimpl Taker for T:\n    fn take(k: i64) -> i64:\n        return self.v + k\n    fn mix(f: f64) -> f64:\n        return f\n\nfn main() -> i64:\n    val t = T(v: 1)\n    return t.take(4) + t.mix(2).to_i64()\n",
        ),
        (
            "trait-typed parameter receiver with int arg and f64 slot",
            "trait Taker:\n    fn take(k: i64) -> i64\n    fn mix(f: f64) -> f64\n\nclass T:\n    v: i64\n\nimpl Taker for T:\n    fn take(k: i64) -> i64:\n        return self.v + k\n    fn mix(f: f64) -> f64:\n        return f\n\nfn use_dyn(t: Taker) -> i64:\n    return t.take(4) + t.mix(2).to_i64() + t.take(4.5 as i64)\n\nfn main() -> i64:\n    return use_dyn(T(v: 1))\n",
        ),
    ] {
        bad.extend(accepted(label, &lower_one(src)));
    }
    assert!(bad.is_empty(), "{}", bad.join("\n"));
}

//! Two interpreter locks found on the Windows caret lane:
//!
//! 1. A value-position `if`/`match` must not revert a global this frame wrote,
//!    and must not let that write beat a callee's newer value, in either order.
//!    doc/08_tracking/bug/seed_interpreter_if_expr_reverts_frame_global_write_2026-10-31.md
//! 2. A `me` method returning a NEW object is a pure result: a chain through it
//!    must leave the root receiver alone, while a builder returning `self` still
//!    threads every mutation back.
//!    doc/08_tracking/bug/smux_native_provider_lane_blocked_on_windows_seed_2026-10-31.md

use simple_compiler::interpreter;
use std::collections::HashSet;
use std::fs;
use tempfile::tempdir;

fn run_pkg(state: &str, main: &str) -> i32 {
    let dir = tempdir().unwrap();
    let pkg = dir.path().join("src").join("pkg");
    fs::create_dir_all(&pkg).unwrap();
    fs::write(pkg.join("state.spl"), state).unwrap();
    let main_path = pkg.join("main.spl");
    fs::write(&main_path, main).unwrap();

    interpreter::clear_module_cache();
    interpreter::clear_interpreter_state();
    let module =
        simple_compiler::pipeline::module_loader::load_module_with_imports(&main_path, &mut HashSet::new()).unwrap();
    interpreter::set_current_file(Some(main_path.clone()));
    let result = interpreter::evaluate_module(&module.items);
    interpreter::set_current_file(None);
    match result {
        Ok(code) => code,
        Err(error) => panic!("program failed: {error:?}"),
    }
}

const GLOBAL_CASES: &str = r#"var G = "old"

fn upd(v: text) -> bool:
    G = v
    true

fn deep(v: text) -> bool:
    upd(v)

fn write_then_if(c: bool) -> text:
    G = "new"
    val m = if c:
        "a"
    else:
        "b"
    G

fn condition_call_updates(c: bool) -> text:
    G = "stale"
    val m = if upd("cond"):
        "a"
    else:
        "b"
    G

fn write_call_if(c: bool) -> text:
    G = "w"
    upd("called")
    val m = if c:
        "a"
    else:
        "b"
    G

fn write_call_write_if(c: bool) -> text:
    G = "w"
    upd("called")
    G = "w2"
    val m = if c:
        "a"
    else:
        "b"
    G

fn arm_call_updates(c: bool) -> text:
    G = "w"
    val m = if c:
        upd("arm")
        "a"
    else:
        "b"
    G

fn arm_deep_call_updates(c: bool) -> text:
    G = "w"
    val m = if c:
        deep("armdeep")
        "a"
    else:
        "b"
    G

fn arm_write_then_call(c: bool) -> text:
    G = "w"
    val m = if c:
        G = "armw"
        upd("armcall")
        "a"
    else:
        "b"
    G

fn nested_value_if(c: bool) -> text:
    G = "w"
    val m = if c:
        val n = if c:
            "x"
        else:
            "y"
        G
    else:
        "b"
    m + "/" + G

fn match_arm(c: bool) -> text:
    G = "w"
    val m = match c:
        case true:
            "a"
        case false:
            "b"
    G

fn store() -> text:
    G
"#;

const GLOBAL_MAIN: &str = r#"use pkg.state.{write_then_if, condition_call_updates, write_call_if, write_call_write_if, arm_call_updates, arm_deep_call_updates, arm_write_then_call, nested_value_if, match_arm, store}

fn main() -> i32:
    if write_then_if(true) != "new" or store() != "new":
        return 1
    if condition_call_updates(true) != "cond" or store() != "cond":
        return 2
    if write_call_if(true) != "called" or store() != "called":
        return 3
    if write_call_write_if(true) != "w2" or store() != "w2":
        return 4
    if arm_call_updates(true) != "arm" or store() != "arm":
        return 5
    if arm_deep_call_updates(true) != "armdeep" or store() != "armdeep":
        return 6
    if arm_write_then_call(true) != "armcall" or store() != "armcall":
        return 7
    if nested_value_if(true) != "w/w" or store() != "w":
        return 8
    if match_arm(true) != "w" or store() != "w":
        return 9
    0
"#;

#[test]
fn value_if_keeps_frame_write_and_callee_updates_in_every_order() {
    assert_eq!(run_pkg(GLOBAL_CASES, GLOBAL_MAIN), 0);
}

const CHAIN_CASES: &str = r#"class C:
    a: i64
    n: i64
    me ma(x: i64) -> C:
        return C(a: x, n: me.n)
    me mn(x: i64) -> C:
        return C(a: me.a, n: x)

class B:
    n: i64
    xs: [i64]
    me add(x: i64) -> B:
        self.n = self.n + x
        self.xs.push(x)
        return self
    me fresh(x: i64) -> B:
        return B(n: x, xs: [])
"#;

const CHAIN_MAIN: &str = r#"use pkg.state.{C, B}

fn main() -> i32:
    val c = C(a: 1, n: 1)
    val r = c.ma(2).mn(3)
    if c.a != 1 or c.n != 1:
        return 1
    if r.a != 2 or r.n != 3:
        return 2
    var b = B(n: 0, xs: [])
    val b2 = b.add(1).add(2)
    if b.n != 3 or b.xs.len() != 2 or b2.n != 3:
        return 3
    val b3 = b.add(10).add(20).add(30)
    if b.n != 63 or b3.n != 63:
        return 4
    val mid = b.add(1).fresh(7).add(1)
    if b.n != 64 or mid.n != 8:
        return 5
    val first = b.fresh(100).add(5)
    if b.n != 64 or first.n != 105:
        return 6
    0
"#;

#[test]
fn me_chain_writes_root_only_when_it_threads_self() {
    assert_eq!(run_pkg(CHAIN_CASES, CHAIN_MAIN), 0);
}

//! A value-producing inline `if/else` whose arm is an `and`/`or` chain must
//! evaluate the same under native (Cranelift JIT) codegen as in the
//! interpreter.
//!
//! Lowering pin for the shapes in
//! `seed_native_inline_if_else_or_chain_false_2026-11-27`. That bug was NOT
//! an if/else or short-circuit lowering defect: the reap site read `false`
//! because `rt_process_is_running` (C `bool`) was imported with an I64 return
//! and the caller read undefined RAX bits; the if/else shape only changed
//! which register garbage was there. These shapes passed before the fix too.
//! The real guard is `runtime_h_bool_returns_use_i8_abi` in
//! `codegen/runtime_sffi.rs`. `main` returns the first failing case, or 0.

use simple_compiler::codegen::JitCompiler;
use simple_compiler::{hir, interpreter, mir};
use simple_parser::Parser;

const SOURCE: &str = r#"
fn probe(pid: i64) -> bool:
    pid > 100

fn reap_shape(label: text, hir_stopped: bool, pid: i64, code: i64) -> bool:
    var owner_stopped = if label == "hir-shard": hir_stopped else: pid <= 0 or (code != -2 and code != -1 and not probe(pid))
    owner_stopped

fn else_or(c: bool, a: bool, b: bool) -> bool:
    val r = if c: false else: a or b
    r

fn else_and(c: bool, a: bool, b: bool) -> bool:
    val r = if c: false else: a and b
    r

fn then_or(c: bool, a: bool, b: bool) -> bool:
    val r = if c: a or b else: false
    r

fn then_and(c: bool, a: bool, b: bool) -> bool:
    val r = if c: a and b else: true
    r

fn else_not_call(c: bool, a: bool, pid: i64) -> bool:
    val r = if c: false else: a or not probe(pid)
    r

fn nested(c: bool, a: bool, b: bool, d: bool) -> bool:
    val r = if c: false else: (a and b) or (not a and d)
    r

fn returned(c: bool, a: bool, b: bool) -> bool:
    if c: false else: a or b

fn match_arm(k: i64, a: bool, b: bool) -> bool:
    val r = match k:
        0: false
        1: a or b
        _: a and b
    r

struct Owner:
    stopped: bool
    code: i64

fn pool_shape(label: text, waits: [i64]) -> i64:
    var pids: [i64] = [0, 7, 8]
    var owners: [Owner] = [Owner(stopped: true, code: 0), Owner(stopped: false, code: 0), Owner(stopped: false, code: 0)]
    var seen = 0
    var all_stopped = true
    var rounds = 0
    while pids.len() > 1 and rounds < 8:
        rounds = rounds + 1
        var reap_at = -1
        var code = 0
        var i = 1
        while i < pids.len():
            val polled = waits[i - 1]
            if polled != -2:
                reap_at = i
                code = polled
            i = i + 1
        if reap_at < 0:
            continue
        var hir_stopped = false
        if label == "hir-shard":
            hir_stopped = owners[reap_at].stopped
        val pid = pids[reap_at]
        var kept: [i64] = []
        var kept_owners: [Owner] = []
        i = 0
        while i < pids.len():
            if i != reap_at:
                kept = kept.push(pids[i])
                kept_owners = kept_owners.push(owners[i])
            i = i + 1
        pids = kept
        owners = kept_owners
        var owner_stopped = if label == "hir-shard": hir_stopped else: pid <= 0 or (code != -2 and code != -1 and not probe(pid))
        if label != "hir-shard" and not owner_stopped and pid > 0:
            all_stopped = false
        if owner_stopped:
            seen = seen + 1
    if all_stopped: seen else: -seen

fn main() -> i64:
    if not reap_shape("x", false, 5, 0): return 1
    if not reap_shape("x", false, 0, 0): return 2
    if reap_shape("x", false, 500, 0): return 3
    if reap_shape("x", false, 5, -1): return 4
    if not reap_shape("hir-shard", true, 500, -1): return 5
    if not else_or(false, false, true): return 6
    if else_or(false, false, false): return 7
    if not else_and(false, true, true): return 8
    if else_and(false, true, false): return 9
    if not then_or(true, false, true): return 10
    if then_or(true, false, false): return 11
    if not then_and(true, true, true): return 12
    if then_and(true, true, false): return 13
    if not else_not_call(false, false, 5): return 14
    if else_not_call(false, false, 500): return 15
    if not nested(false, false, false, true): return 16
    if nested(false, true, false, true): return 17
    if not returned(false, false, true): return 18
    if not match_arm(1, false, true): return 19
    if match_arm(2, false, true): return 20
    if not match_arm(2, true, true): return 21
    if pool_shape("file-worker", [0, 0]) != 2: return 22
    if pool_shape("file-worker", [-1, -1]) != 0: return 23
    return 0
"#;

fn run_interpreter() -> i32 {
    interpreter::clear_module_cache();
    interpreter::clear_interpreter_state();
    let source = format!("{SOURCE}\nmain = main()\n");
    let module = Parser::new(&source).parse().expect("source must parse for interpreter");
    interpreter::evaluate_module(&module.items).expect("source must run in interpreter")
}

fn run_jit() -> i64 {
    let ast = Parser::new(SOURCE).parse().expect("source must parse for JIT");
    let hir_module = hir::lower(&ast).expect("source must lower to HIR");
    let mir_module = mir::lower_to_mir(&hir_module).expect("source must lower to MIR");
    let mut jit = JitCompiler::new_static().expect("static Cranelift JIT");
    jit.compile_module(&mir_module).expect("MIR must compile");
    unsafe { jit.call_i64_void("main").expect("main must execute") }
}

#[test]
fn inline_if_else_logical_chain_matches_interpreter_and_native_jit() {
    let interpreted = run_interpreter();
    let native = run_jit();
    assert_eq!(interpreted, 0, "interpreter control failed at case {interpreted}");
    assert_eq!(native, 0, "native/JIT inline if/else logical chain wrong at case {native}");
}

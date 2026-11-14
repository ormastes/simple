//! `case Some(Variant):` / `case Some(Kind.Variant):` / nested payload
//! patterns over a `Kind?` value that holds a bare enum value must select the
//! arm of THAT variant on both engines, for parameters, typed lets and class
//! fields. Bug:
//! doc/08_tracking/bug/optional_enum_some_variant_match_engine_divergence_2026-11-14.md
//!
//! Measured on the base seed (fdd57145ebe, aarch64):
//!   * interpreter: no `Some(...)` arm matched a bare enum at all (not even
//!     `Some(x)`), so every case fell to `case _:`;
//!   * JIT: the top-level `Some(<sub-pattern>)` test was `rt_is_some` only, so
//!     the FIRST `Some(...)` arm matched every non-nil value (`Kind.F32` and
//!     `Kind.Wrap(7)` answered the `Some(I8)` arm).
//!
//! Every check puts a WRONG `Some(...)` arm ahead of the right one, so an
//! engine that ignores the sub-pattern cannot pass by taking the first arm.

use simple_compiler::codegen::JitCompiler;
use simple_compiler::{hir, interpreter, mir};
use simple_parser::Parser;

const SOURCE: &str = r#"
enum Kind:
    I8
    F32
    Wrap(i64)

class Holder:
    k: Kind?

fn unq(k: Kind?) -> i64:
    match k:
        case Some(I8): return 1
        case Some(F32): return 2
        case Some(Wrap(n)): return 10 + n
        case None: return 4
        case _: return 5
    return 6

fn qual(k: Kind?) -> i64:
    match k:
        case Some(Kind.I8): return 1
        case Some(Kind.F32): return 2
        case Some(Kind.Wrap(n)): return 10 + n
        case None: return 4
        case _: return 5
    return 6

fn bind(k: Kind?) -> i64:
    match k:
        case Some(x):
            match x:
                case F32: return 2
                case _: return 3
        case None: return 4
    return 6

fn tup(k: Kind?, n: i64) -> i64:
    match (k, n):
        case (Some(I8), 1): return 1
        case (Some(F32), 1): return 2
        case (Some(Wrap(m)), _): return 10 + m
        case _: return 5
    return 6

fn main() -> i64:
    var bits = 0
    if unq(Kind.F32) == 2: bits = bits + 1
    if unq(Kind.I8) == 1: bits = bits + 2
    if unq(Kind.Wrap(7)) == 17: bits = bits + 4
    if unq(nil) == 4: bits = bits + 8
    if qual(Kind.F32) == 2: bits = bits + 16
    if qual(Kind.Wrap(7)) == 17: bits = bits + 32
    if qual(nil) == 4: bits = bits + 64
    if bind(Kind.F32) == 2: bits = bits + 128
    if bind(Kind.I8) == 3: bits = bits + 256
    if bind(nil) == 4: bits = bits + 512
    if tup(Kind.F32, 1) == 2: bits = bits + 1024
    if tup(Kind.Wrap(3), 0) == 13: bits = bits + 2048
    val a: Kind? = Kind.I8
    var la = 0
    match a:
        case Some(F32): la = 2
        case Some(I8): la = 1
        case _: la = 5
    if la == 1: bits = bits + 4096
    val b: Kind? = Kind.Wrap(5)
    var lb = 0
    match b:
        case Some(Kind.I8): lb = 1
        case Some(Kind.Wrap(n)): lb = 10 + n
        case _: lb = 5
    if lb == 15: bits = bits + 8192
    val h = Holder(k: Kind.F32)
    var fa = 0
    match h.k:
        case Some(I8): fa = 1
        case Some(F32): fa = 2
        case _: fa = 5
    if fa == 2: bits = bits + 16384
    val h2 = Holder(k: Kind.Wrap(9))
    if qual(h2.k) == 19: bits = bits + 32768
    return bits
"#;

const ALL_BITS: i64 = 65535;

fn run_interpreter() -> i64 {
    interpreter::clear_module_cache();
    interpreter::clear_interpreter_state();
    let source = format!("{SOURCE}\nmain = main()\n");
    let module = Parser::new(&source).parse().expect("source must parse for interpreter");
    interpreter::evaluate_module(&module.items).expect("source must run in interpreter") as i64
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
fn optional_enum_some_variant_arms_select_the_right_variant_in_the_interpreter() {
    assert_eq!(run_interpreter(), ALL_BITS, "missing bits = {:#b}", ALL_BITS & !run_interpreter());
}

#[test]
fn optional_enum_some_variant_arms_select_the_right_variant_on_the_jit() {
    let got = run_jit();
    assert_eq!(got, ALL_BITS, "missing bits = {:#b}", ALL_BITS & !got);
}

//! JIT: copying a struct's `[u8]` field into a `var`, pushing to it, and
//! rebuilding the struct must not retain one full array copy per round-trip.
//!
//! `var o = st.output` lowers to `rt_array_copy` (value semantics,
//! `mir/lower/lowering_stmt.rs`), and nothing on the JIT lane ever releases the
//! previous copy once `st = St(output: o)` overwrites the last holder, so live
//! array bytes grow quadratically in the number of round-trips. The
//! interpreter (Arc + make_mut) stays linear.

use simple_compiler::codegen::JitCompiler;
use simple_compiler::{hir, mir};
use simple_parser::Parser;
use simple_runtime::value::heap::rt_heap_aux_live_bytes;

fn compile(source: &str) -> JitCompiler {
    let ast = Parser::new(source).parse().expect("source must parse");
    let hir_module = hir::lower(&ast).expect("source must lower to HIR");
    let mir_module = mir::lower_to_mir(&hir_module).expect("source must lower to MIR");
    let mut jit = JitCompiler::new_static().expect("static Cranelift JIT");
    jit.compile_module(&mir_module).expect("module must JIT-compile");
    jit
}

const ROUND_TRIP_SRC: &str = "struct St:
    output: [u8]

fn step_c(n: i64) -> [u8]:
    var st = St(output: [1 as u8, 2 as u8, 3 as u8, 4 as u8])
    var i = 0
    while i < n:
        var o = st.output
        var k = 0
        while k < 8:
            o.push(o[o.len() - 4])
            k = k + 1
        st = St(output: o)
        i = i + 8
    st.output

fn main() -> i64:
    step_c(8192).len()
";

/// Live array backing bytes after the run must be O(n), not O(n^2).
/// n = 8192 round-trips 1024 times; the quadratic leak retained ~8 MiB of
/// stale copies (measured 8,388,620 bytes before the fix), while the
/// legitimately live result is ~16 KiB.
#[test]
fn struct_field_array_round_trip_live_bytes_stay_linear() {
    let jit = compile(ROUND_TRIP_SRC);
    let before = rt_heap_aux_live_bytes();
    let len = unsafe { jit.call_i64_void("main").expect("main must execute") };
    let after = rt_heap_aux_live_bytes();
    assert_eq!(len, 8192 + 4);
    let grown = after - before;
    let bound = 16 * 8192;
    assert!(
        grown < bound,
        "live array bytes grew by {grown} for n=8192 (bound {bound}): stale struct-field copies are retained"
    );
}

/// Value semantics: mutating the `var` copy must not change the struct field.
#[test]
fn struct_field_array_copy_keeps_value_semantics() {
    let src = "struct St:
    output: [u8]

fn main() -> i64:
    var st = St(output: [1 as u8, 2 as u8])
    var o = st.output
    o.push(3 as u8)
    st.output.len() * 10 + o.len()
";
    let jit = compile(src);
    let got = unsafe { jit.call_i64_void("main").expect("main must execute") };
    assert_eq!(got, 23, "st.output must stay length 2 after pushing to its copy");
}

/// Engine differential of the alias probe: the interpreter prints
/// `A st=2 saved=2 o=3`, `B st=3 o=4 saved=2`, `C st=4 saved=2`. Before the
/// struct-literal copy the JIT answered `B st=4` (`St(output: o)` shared `o`).
#[test]
fn alias_probe_matches_interpreter() {
    let src = "struct St:
    output: [u8]

fn main() -> i64:
    var st = St(output: [1 as u8, 2 as u8])
    val saved = st
    var o = st.output
    o.push(3 as u8)
    val a = st.output.len() * 100 + saved.output.len() * 10 + o.len()
    st = St(output: o)
    o.push(4 as u8)
    val b = st.output.len() * 100 + o.len() * 10 + saved.output.len()
    st.output.push(5 as u8)
    val c = st.output.len() * 10 + saved.output.len()
    a * 1000000 + b * 1000 + c
";
    let jit = compile(src);
    let got = unsafe { jit.call_i64_void("main").expect("main must execute") };
    assert_eq!(got, 223 * 1000000 + 342 * 1000 + 42);
}

/// Hole A1: `S(data: o)` for a type with an `@inject` `new` lowers to a
/// constructor CALL that stores `o` uncopied (base behaviour, kept). The later
/// `var p = s.data` must still copy: moving it would alias `o`, so `p.push`
/// would also grow `o` (33 instead of the base answer 32).
#[test]
fn inject_constructor_struct_field_read_still_copies() {
    let src = "struct S:
    data: [u8]

impl S:
    static fn new(data: [u8], @inject tag: i64) -> S:
        S(data: data)

fn make_tag() -> i64:
    7

fn main() -> i64:
    var o: [u8] = [1 as u8]
    var s = S(data: o)
    o.push(2 as u8)
    var p = s.data
    p.push(3 as u8)
    s = S(data: [9 as u8])
    p.len() * 10 + o.len()
";
    let di_toml: toml::Value = "[di]\nmode = \"hybrid\"\n\n[di.profiles.default]\nbindings = [\n  { on = \"pc{ type(i64) }\", impl = \"make_tag\", scope = \"Transient\", priority = 10 }\n]\n"
        .parse()
        .expect("di toml");
    let config = simple_compiler::di::parse_di_config(&di_toml)
        .expect("di config parse")
        .expect("di config present");
    let ast = Parser::new(src).parse().expect("source must parse");
    let hir_module = hir::lower(&ast).expect("source must lower to HIR");
    let mir_module = mir::lower_to_mir_with_mode_and_di(&hir_module, mir::ContractMode::All, Some(config))
        .expect("source must lower to MIR");
    let mut jit = JitCompiler::new_static().expect("static Cranelift JIT");
    jit.compile_module(&mir_module).expect("module must JIT-compile");
    let got = unsafe { jit.call_i64_void("main").expect("main must execute") };
    assert_eq!(got, 32);
}

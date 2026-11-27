//! seed_jit_u8_array_into_i64_array_param_reads_zero_2026-11-27: a `[u8]`
//! reaching a typed `[i64]` / `[u64]` / `[u32]` reader through an untyped
//! caller (the static E1003 check cannot see it) must read the stored byte.
//! The JIT inliners used to load 8-byte slots of the byte buffer: index 1 of
//! `[1u8, 255u8, 128u8]` read as 0, where the interpreter returns 255.
use simple_parser::Parser;

fn jit_evaluate(source: &str) -> i64 {
    let ast = Parser::new(source).parse().expect("valid source");
    // The run/JIT lane lowers untyped parameters as ANY (pipeline/execution.rs).
    let mut lowerer = simple_compiler::hir::Lowerer::new();
    lowerer.set_strict_mode(false);
    lowerer.set_lenient_types(true);
    let hir = lowerer.lower_module(&ast).expect("HIR lowering");
    let mir = simple_compiler::mir::lower_to_mir(&hir).expect("MIR lowering");
    let mut jit = simple_compiler::codegen::JitCompiler::new_static().expect("static JIT");
    jit.compile_module(&mir).expect("JIT compilation");
    unsafe { jit.call_i64_void("main").expect("JIT execution") }
}

#[test]
fn jit_word_array_readers_decode_bytes_from_untyped_caller() {
    for ty in ["i64", "u64", "u32"] {
        let source = format!(
            "fn at(data: [{ty}], i: i64) -> i64:\n    data[i] as i64\nfn relay(data, i: i64) -> i64:\n    at(data, i)\nfn main() -> i64:\n    val b: [u8] = [1u8, 255u8, 128u8]\n    relay(b, 0) * 1000000 + relay(b, 1) * 1000 + relay(b, 2)\n"
        );
        assert_eq!(jit_evaluate(&source), 1_255_128, "[{ty}] reader over [u8]");
    }
}

/// The bound-proved loop (`val n = d.len(); var i: u64 = 0; while i < n`) over
/// a `[u32]` / `[u64]` parameter reads through the hoisted data pointer
/// (`_data_at` / `_raw_data_at`), which loaded 8-byte slots past the bytes.
#[test]
fn jit_hoisted_loop_readers_decode_bytes_from_untyped_caller() {
    for ty in ["u32", "u64"] {
        let source = format!(
            "fn total(d: [{ty}]) -> i64:\n    var s = 0\n    val n = d.len()\n    var i: u64 = 0\n    while i < n:\n        s = s * 1000 + d[i] as i64\n        i = i + 1\n    s\nfn relay(d) -> i64:\n    total(d)\nfn main() -> i64:\n    val b: [u8] = [1u8, 255u8, 128u8]\n    relay(b)\n"
        );
        assert_eq!(jit_evaluate(&source), 1_255_128, "hoisted [{ty}] loop over [u8]");
    }
}

/// A typed word write into a `[u8]` (owner decision: a runtime error, both
/// lanes). The inlined `[u32]` set stored a tagged word over bytes 8..15, the
/// runtime `[u64]` / `[i64]` set did the same, and an in-capacity push grew
/// `len` past the byte buffer. Each write runs in a child, which must exit like the C lane's spl_panic.
const JIT_TRAP_ENV: &str = "SIMPLE_TEST_JIT_WORD_WRITE";
const WORD_WRITE_PANIC_LINE: &str =
    "PANIC: typed word write: a [u8] array cannot be written through a word-typed array parameter ([i64]/[u64]/[u32])";

fn word_write_source(op: &str) -> String {
    let (ty, body) = match op {
        "u32_set" => ("u32", "d[1] = 77u32"),
        "u64_set" => ("u64", "d[1] = 77u64"),
        "i64_set" => ("i64", "d[1] = 77"),
        "u32_push" => ("u32", "d.push(77u32)"),
        "u64_push" => ("u64", "d.push(77u64)"),
        "i64_push" => ("i64", "d.push(77)"),
        other => panic!("unknown op {other}"),
    };
    format!(
        "fn w(d: [{ty}]):\n    {body}\nfn relay(d):\n    w(d)\nfn main() -> i64:\n    var b: [u8] = []\n    var i = 0\n    while i < 16:\n        b.push((i + 1) as u8)\n        i = i + 1\n    relay(b)\n    b.len()\n"
    )
}

#[test]
fn jit_word_write_child() {
    let Ok(op) = std::env::var(JIT_TRAP_ENV) else {
        return;
    };
    let len = jit_evaluate(&word_write_source(&op));
    println!("NO-TRAP {op} len={len}");
}

#[test]
fn jit_word_array_writers_trap_on_bytes_from_untyped_caller() {
    let exe = std::env::current_exe().expect("test binary");
    for op in ["u32_set", "u64_set", "i64_set", "u32_push", "u64_push", "i64_push"] {
        let out = std::process::Command::new(&exe)
            .args(["--exact", "jit_word_write_child", "--nocapture", "--test-threads=1"])
            .env(JIT_TRAP_ENV, op)
            .output()
            .expect("spawn child");
        let stdout = String::from_utf8_lossy(&out.stdout);
        let stderr = String::from_utf8_lossy(&out.stderr);
        assert!(!stdout.contains("NO-TRAP"), "{op}: write returned: {stdout}");
        // Same report and status as the C lane's spl_panic (runtime.c).
        assert_eq!(out.status.code(), Some(1), "{op}: status {:?}: {stderr}", out.status);
        assert!(
            stderr.lines().any(|line| line == WORD_WRITE_PANIC_LINE),
            "{op}: {stderr}"
        );
    }
}

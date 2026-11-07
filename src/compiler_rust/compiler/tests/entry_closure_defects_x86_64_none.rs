//! Freestanding x86_64 object probes for the entry-closure codegen defects
//! (doc/08_tracking/bug/simpleos_native_build_entry_closure_codegen_defects_2026-07-17.md
//! C2..C6) and the rt_string_join low-handle guard fold
//! (doc/08_tracking/bug/simpleos_freestanding_nil_array_init_optimizer_guard_fold.md).
//!
//! `entry_closure_defects_jit.rs` already runs these repros through the host
//! JIT, but the host here is aarch64 and the defects were reported only for
//! `--target x86_64-unknown-none --backend cranelift --opt-level=aggressive`.
//! These tests emit the same sources as a real `x86_64-unknown-none` AOT
//! object at the Aggressive level, link it with a tiny `-nostdlib` `_start`
//! harness, and execute it under `qemu-x86_64` user-mode, so the x86_64
//! freestanding instruction selection is exercised end to end.
//!
//! The few runtime (`rt_*`) symbols the probes reference are served by
//! `MINI_RUNTIME`, a freestanding C mirror of the Rust runtime's encoding
//! (`runtime/src/value/{core,tags,objects,collections}.rs`: int tag 0 with a
//! 3-bit shift, NIL = special tag 3, heap tag 1, `RuntimeEnum`/tuple layout,
//! `OPTION_ENUM_ID` = 1).  Any other runtime reference fails the link and is
//! reported as a test failure rather than silently skipped.

use std::path::{Path, PathBuf};
use std::process::Command;

use simple_common::target::{Target, TargetArch, TargetCpu, TargetOS};
use simple_compiler::codegen::Codegen;
use simple_compiler::optimizations::NativeOptimizationLevel;
use simple_compiler::{hir, mir};
use simple_parser::Parser;

fn tool(name: &str) -> PathBuf {
    for dir in [
        "/home/yoon/dev/llvm/install/bin",
        "/usr/lib/llvm-23/bin",
        "/usr/lib/llvm-20/bin",
        "/usr/bin",
    ] {
        let candidate = Path::new(dir).join(name);
        if candidate.is_file() {
            return candidate;
        }
    }
    PathBuf::from(name)
}

fn qemu_x86_64() -> PathBuf {
    if let Ok(path) = std::env::var("SIMPLE_QEMU_X86_64") {
        return PathBuf::from(path);
    }
    let home = std::env::var("HOME").unwrap_or_default();
    let local = Path::new(&home).join(".local/bin/qemu-x86_64");
    if local.is_file() {
        local
    } else {
        PathBuf::from("qemu-x86_64")
    }
}

fn compile_x86_64_none_object(source: &str) -> Vec<u8> {
    let ast = Parser::new(source).parse().expect("source must parse");
    let hir_module = hir::lower(&ast).expect("source must lower to HIR");
    let mir_module = mir::lower_to_mir(&hir_module).expect("source must lower to MIR");
    Codegen::for_target_with_opt_level_and_cpu(
        Target::new(TargetArch::X86_64, TargetOS::None),
        NativeOptimizationLevel::Aggressive,
        TargetCpu::X86_64V1,
    )
    .expect("x86_64-unknown-none cranelift backend")
    .compile_module(&mir_module)
    .expect("module must compile to an x86_64-unknown-none object")
}

/// `_start` calls `entry()` and exits with its low byte as the process status.
const HARNESS: &str = r#"
long long ENTRY(void);
__attribute__((noreturn)) void _start(void) {
    long long r = ENTRY();
    __asm__ volatile("mov $60, %%eax\n syscall" :: "D"((long)(r & 0xff)) : "rax", "rcx", "r11", "memory");
    __builtin_unreachable();
}
"#;

const MINI_RUNTIME: &str = r#"
typedef unsigned long long u64;
typedef long long i64;
typedef unsigned int u32;
#define NIL 3ULL
static u64 heap_words[4096];
static u64 heap_next;
static u64 *alloc_words(u64 n) { u64 *p = &heap_words[heap_next]; heap_next += n; return p; }
static u64 *heap_ptr(u64 v) { return (v & 7ULL) == 1ULL ? (u64 *)(v & ~7ULL) : 0; }
u64 rt_value_int(i64 i) { return (u64)i << 3; }
i64 rt_value_unbox_int(u64 v) { return (v & 7ULL) == 0 ? (i64)v >> 3 : 0; }
/* RuntimeEnum: header(kind 1) | enum_id:u32 discriminant:u32 | payload */
u64 rt_enum_new(u32 enum_id, u32 discriminant, u64 payload) {
    u64 *p = alloc_words(3); p[0] = 1; p[1] = ((u64)discriminant << 32) | enum_id; p[2] = payload;
    return (u64)p | 1ULL;
}
static u64 *enum_ptr(u64 v) { u64 *p = heap_ptr(v); return p && p[0] == 1 ? p : 0; }
i64 rt_enum_discriminant(u64 v) { u64 *p = enum_ptr(v); return p ? (i64)(p[1] >> 32) : -1; }
i64 rt_enum_id(u64 v) { u64 *p = enum_ptr(v); return p ? (i64)(u32)p[1] : -1; }
_Bool rt_is_some(u64 v) {
    u64 *p = enum_ptr(v);
    if (v == NIL) return 0;
    return !(p && (u32)p[1] == 1 && (p[1] >> 32) == 1);
}
u64 rt_unwrap_or_self(u64 v) { u64 *p = enum_ptr(v); return p && (u32)p[1] == 1 ? p[2] : v; }
/* tuple: header(kind 2) | len | slots */
u64 rt_tuple_new(u64 len) {
    u64 *p = alloc_words(2 + len); p[0] = 2; p[1] = len;
    for (u64 i = 0; i < len; i++) p[2 + i] = NIL;
    return (u64)p | 1ULL;
}
u64 rt_tuple_get(u64 t, u64 i) { u64 *p = heap_ptr(t); return p && p[0] == 2 && i < p[1] ? p[2 + i] : NIL; }
_Bool rt_tuple_set(u64 t, u64 i, u64 v) {
    u64 *p = heap_ptr(t); if (!(p && p[0] == 2 && i < p[1])) return 0; p[2 + i] = v; return 1;
}
"#;

/// Compile `source`, link `entry` as the program entry and return its exit status.
fn run_x86_64_none(source: &str, entry: &str) -> i32 {
    run_x86_64_none_with(source, entry, "")
}

/// `peek` exits with status 99 whenever it is reached, so a dropped guard in
/// front of it is observable as a wrong status instead of a host fault.
const FAULTING_PEEK: &str = "long long peek(long long addr) {\n    (void)addr;\n    __asm__ volatile(\"mov $60, %%eax\\n syscall\" :: \"D\"(99L) : \"rax\", \"rcx\", \"r11\", \"memory\");\n    __builtin_unreachable();\n}\n";

fn run_x86_64_none_with(source: &str, entry: &str, extra_c: &str) -> i32 {
    let object = compile_x86_64_none_object(source);
    let dir = tempfile::tempdir().expect("tempdir");
    let obj_path = dir.path().join("probe.o");
    std::fs::write(&obj_path, &object).expect("write object");
    let harness_path = dir.path().join("harness.c");
    std::fs::write(
        &harness_path,
        format!("{}\n{}\n{}", HARNESS.replace("ENTRY", entry), MINI_RUNTIME, extra_c),
    )
    .expect("write harness");
    let exe = dir.path().join("probe");
    let link = Command::new(tool("clang"))
        .args([
            "--target=x86_64-unknown-linux-gnu",
            "-ffreestanding",
            "-nostdlib",
            "-static",
            "-fno-pic",
            "-no-pie",
            "-fuse-ld=lld",
            "-O1",
        ])
        .arg(format!("--ld-path={}", tool("ld.lld").display()))
        .arg(&harness_path)
        .arg(&obj_path)
        .arg("-o")
        .arg(&exe)
        .output()
        .expect("spawn clang");
    assert!(
        link.status.success(),
        "link failed for entry {entry}:\n{}",
        String::from_utf8_lossy(&link.stderr)
    );
    let run = Command::new(qemu_x86_64())
        .arg(&exe)
        .output()
        .expect("spawn qemu-x86_64");
    run.status
        .code()
        .unwrap_or_else(|| panic!("probe {entry} died by signal: {:?}", run.status))
}

#[test]
fn c2_if_val_hit_returns_payload_x86_64_none() {
    let src = "fn maybe(n: i64) -> i64?:\n    if n > 0:\n        return n\n    nil\n\nfn pick(n: i64) -> i64:\n    if val x = maybe(n):\n        return x\n    -1\n\nfn probe_main() -> i64:\n    pick(7) * 10 + (pick(0) + 1)\n";
    assert_eq!(run_x86_64_none(src, "probe_main"), 70);
}

#[test]
fn c3_short_circuit_and_with_call_rhs_tests_lhs_x86_64_none() {
    let src = "var CALLS: i64 = 0\n\nfn probe() -> bool:\n    CALLS = CALLS + 1\n    true\n\nfn gate(off: bool) -> i64:\n    if not off and probe():\n        return 1\n    0\n\nfn probe_main() -> i64:\n    val a = gate(true)\n    val b = gate(false)\n    a * 100 + b * 10 + CALLS\n";
    assert_eq!(run_x86_64_none(src, "probe_main"), 11);
}

#[test]
fn c4_anonymous_tuple_positions_x86_64_none() {
    let src = "fn t() -> (i64, i64, i64, i64):\n    (1, 2, 3, 4)\n\nfn probe_main() -> i64:\n    val r = t()\n    r.0 * 64 + r.1 * 16 + r.2 * 4 + r.3\n";
    assert_eq!(run_x86_64_none(src, "probe_main"), 64 + 32 + 12 + 4);
}

#[test]
fn c5_enum_equality_x86_64_none() {
    let src = "enum Mode:\n    User\n    System\n\nfn m() -> Mode:\n    Mode.System\n\nfn probe_main() -> i64:\n    val x = m()\n    var r: i64 = 0\n    if x == Mode.System:\n        r = r + 1\n    if x == Mode.User:\n        r = r + 10\n    r\n";
    assert_eq!(run_x86_64_none(src, "probe_main"), 1);
}

#[test]
fn c6_byte_combine_x86_64_none() {
    // 0x0f70 does not fit an exit status; return a checksum that is wrong if
    // the high-byte term is dropped (0x70 -> 0x70 % 251 = 112).
    let src = "fn comb(b0: u32, b1: u32) -> u32:\n    b0 | (b1 << 8)\n\nfn probe_main() -> i64:\n    val v = comb(0x70, 0x0f) as i64\n    if v == 0x0f70:\n        return 42\n    v % 251\n";
    assert_eq!(run_x86_64_none(src, "probe_main"), 42);
}

#[test]
fn low_handle_guard_on_i64_param_survives_x86_64_none() {
    // rt_string_join / array_is_valid shape: an `i64` handle parameter guarded
    // by `< 4096` before a dependent memory read.  If the guard were folded
    // away the raw-0 / nil handles would reach `peek` and fault.
    let src = "extern fn peek(addr: i64) -> i64\n\nfn handle_len(array: i64) -> i64:\n    if array < 4096:\n        return 0\n    peek((array & -8) + 8)\n\nfn probe_main() -> i64:\n    handle_len(0) + handle_len(3) + handle_len(8) + 5\n";
    assert_eq!(run_x86_64_none_with(src, "probe_main", FAULTING_PEEK), 5);
}

#[test]
fn low_handle_guard_inside_inlined_callee_survives_x86_64_none() {
    // array_is_valid -> rt_array_len shape: the guard lives in a small,
    // loop-free helper that the MIR inliner (codegen/mir_inline.rs) does
    // inline into its caller.
    let src = "extern fn peek(addr: i64) -> i64\n\nfn handle_valid(array: i64) -> i64:\n    if array < 4096:\n        return 0\n    if (array & 7) > 1:\n        return 0\n    1\n\nfn handle_len(array: i64) -> i64:\n    if handle_valid(array) < 1:\n        return 0\n    peek((array & -8) + 8)\n\nfn probe_main() -> i64:\n    handle_len(0) + handle_len(3) + handle_len(8) + 6\n";
    assert_eq!(run_x86_64_none_with(src, "probe_main", FAULTING_PEEK), 6);
}

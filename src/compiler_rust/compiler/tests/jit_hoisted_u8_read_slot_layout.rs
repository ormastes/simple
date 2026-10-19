//! A len-bounded `while i < len: data[i]` loop over `[u8]` hoists the array
//! data pointer. The hoisted read must respect the array's storage layout: a
//! `[]` literal in a struct-field position builds a slot-layout `[u8]`
//! (8-byte tagged elements), a typed `var x: [u8] = []` builds the
//! byte-packed one. The hoisted raw byte load read slot arrays as packed
//! bytes, so the repro summed 8 (`1 << 3`, the low byte of the first slot)
//! instead of 15. Bug: doc/08_tracking/bug/jit_hoisted_u8_data_ptr_ignores_slot_layout_2026-10-19.md

use simple_compiler::codegen::JitCompiler;
use simple_compiler::{hir, mir};
use simple_parser::Parser;

fn run(source: &str) -> i64 {
    let ast = Parser::new(source).parse().expect("source must parse");
    let hir_module = hir::lower(&ast).expect("source must lower to HIR");
    let mir_module = mir::lower_to_mir(&hir_module).expect("source must lower to MIR");
    let mut jit = JitCompiler::new_static().expect("static Cranelift JIT");
    jit.compile_module(&mir_module).expect("module must JIT-compile");
    unsafe { jit.call_i64_void("main").expect("main must execute") }
}

const PRELUDE: &str = "struct Holder:\n    bytes: [u8]\n\nfn slot_bytes() -> [u8]:\n    var out = Holder(bytes: []).bytes\n    var i = 0\n    while i < 5:\n        out.push((i + 1).to_u8())\n        i = i + 1\n    out\n\nfn packed_bytes() -> [u8]:\n    var out: [u8] = []\n    var i = 0\n    while i < 5:\n        out.push((i + 1).to_u8())\n        i = i + 1\n    out\n\n";

#[test]
fn hoisted_u64_index_reads_slot_layout_bytes() {
    let src = format!(
        "{PRELUDE}fn tail_sum(data: [u8]) -> u64:\n    val total_len: u64 = data.len().to_u64()\n    var pos: u64 = 0\n    var s: u64 = 0\n    while pos < total_len:\n        s = s + data[pos].to_u64()\n        pos = pos + 1\n    s\n\nfn main() -> i64:\n    tail_sum(slot_bytes()).to_i64() * 100 + tail_sum(packed_bytes()).to_i64()\n"
    );
    assert_eq!(run(&src), 15 * 100 + 15);
}

#[test]
fn hoisted_i64_index_reads_slot_layout_bytes() {
    let src = format!(
        "{PRELUDE}fn sum(data: [u8]) -> i64:\n    var i = 0\n    var s = 0\n    while i < data.len():\n        s = s + data[i].to_i64()\n        i = i + 1\n    s\n\nfn main() -> i64:\n    sum(slot_bytes()) * 100 + sum(packed_bytes())\n"
    );
    assert_eq!(run(&src), 15 * 100 + 15);
}

/// The XXH64/XXH32 shape: the byte loop resumes mid-array after word reads.
#[test]
fn hoisted_tail_loop_from_mid_array_reads_slot_layout_bytes() {
    let src = format!(
        "{PRELUDE}fn tail_from(data: [u8], start: u64) -> u64:\n    val total_len: u64 = data.len().to_u64()\n    var pos: u64 = start\n    var h: u64 = 0\n    while pos < total_len:\n        h = h * 31 + data[pos].to_u64()\n        pos = pos + 1\n    h\n\nfn main() -> i64:\n    val a = tail_from(slot_bytes(), 2u64).to_i64()\n    val b = tail_from(packed_bytes(), 2u64).to_i64()\n    if a == b:\n        return a\n    -1\n"
    );
    assert_eq!(run(&src), (3 * 31 + 4) * 31 + 5);
}

fn call_count(mir_module: &mir::MirModule, name: &str) -> usize {
    mir_module
        .functions
        .iter()
        .flat_map(|f| f.blocks.iter())
        .flat_map(|b| b.instructions.iter())
        .filter(|i| matches!(i, mir::MirInst::Call { target, .. } if target == &mir::CallTarget::from_name(name)))
        .count()
}

/// The u64-index loop takes the hoisted path: one layout check per loop entry
/// and the layout-tagged pointer read (fast packed body / slot body), never the
/// per-read header-checking accessor.
#[test]
fn hoisted_u8_loop_uses_one_layout_check_and_the_tagged_read() {
    let src = format!(
        "{PRELUDE}fn tail_sum(data: [u8]) -> u64:\n    val total_len: u64 = data.len().to_u64()\n    var pos: u64 = 0\n    var s: u64 = 0\n    while pos < total_len:\n        s = s + data[pos].to_u64()\n        pos = pos + 1\n    s\n\nfn main() -> i64:\n    tail_sum(slot_bytes()).to_i64() * 100 + tail_sum(packed_bytes()).to_i64()\n"
    );
    let ast = Parser::new(&src).parse().expect("source must parse");
    let hir_module = hir::lower(&ast).expect("source must lower to HIR");
    let mir_module = mir::lower_to_mir(&hir_module).expect("source must lower to MIR");
    assert_eq!(call_count(&mir_module, "rt_array_is_byte_packed"), 1);
    assert_eq!(call_count(&mir_module, "rt_typed_bytes_u8_data_at"), 1);
    assert_eq!(call_count(&mir_module, "rt_typed_bytes_u8_unchecked"), 0);
    assert_eq!(run(&src), 15 * 100 + 15);
}

/// Little-endian `[u8]` word reads are byte-order independent: pinned values
/// for bytes 01..08 (u32 at 0 = 0x04030201, u64 at 0 = 0x0807060504030201),
/// on both the packed and the slot layout.
const LE_SRC: &str = "extern fn rt_typed_bytes_u32_le_at(buf: [u8], off: u64) -> u64\nextern fn rt_typed_bytes_u64_le_at(buf: [u8], off: u64) -> u64\n\nstruct Holder:\n    bytes: [u8]\n\nfn fill(out: [u8]) -> [u8]:\n    var o = out\n    var i = 0\n    while i < 8:\n        o.push((i + 1).to_u8())\n        i = i + 1\n    o\n\nfn check(data: [u8]) -> i64:\n    var r = 0\n    if rt_typed_bytes_u32_le_at(data, 0u64) == 0x04030201u64:\n        r = r + 1\n    if rt_typed_bytes_u64_le_at(data, 0u64) == 0x0807060504030201u64:\n        r = r + 2\n    r\n\nfn main() -> i64:\n    var packed: [u8] = []\n    check(fill(packed)) * 10 + check(fill(Holder(bytes: []).bytes))\n";

#[test]
fn le_word_reads_are_pinned_on_cranelift() {
    assert_eq!(run(LE_SRC), 33);
}

/// Same pinned values through the LLVM backend, as a real native executable
/// (the in-process LLVM JIT cannot run array code; a plain `push` segfaults
/// there independently of this change).
#[cfg(feature = "llvm")]
#[test]
fn le_word_reads_are_pinned_on_llvm() {
    use simple_compiler::pipeline::{NativeBuildConfig, NativeProjectBuilder};
    let names = ["SIMPLE_BOOTSTRAP", "SIMPLE_NO_STUB_FALLBACK"];
    let previous: Vec<_> = names.iter().map(|n| (*n, std::env::var_os(n))).collect();
    for n in names {
        std::env::set_var(n, "1");
    }
    let repo = std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../..");
    let temporary = tempfile::tempdir().unwrap();
    let source = temporary.path().join("src");
    std::fs::create_dir_all(&source).unwrap();
    let main_src = LE_SRC.replace(
        "fn main() -> i64:\n    var packed: [u8] = []\n    check(fill(packed)) * 10 + check(fill(Holder(bytes: []).bytes))\n",
        "fn main():\n    var packed: [u8] = []\n    print(\"le=\" + (check(fill(packed)) * 10 + check(fill(Holder(bytes: []).bytes))).to_text())\n",
    );
    assert_ne!(main_src, LE_SRC, "main rewrite must apply");
    std::fs::write(source.join("main.spl"), main_src).unwrap();
    let executable = temporary.path().join("le_probe");
    let result = NativeProjectBuilder::new(repo, executable.clone())
        .config(NativeBuildConfig {
            backend: "llvm".to_string(),
            runtime_bundle: "core-c-bootstrap".to_string(),
            entry_closure: true,
            parallel: false,
            num_threads: Some(1),
            cache_dir: Some(temporary.path().join("native-cache")),
            ..NativeBuildConfig::default()
        })
        .source_dir(source.clone())
        .entry_file(source.join("main.spl"))
        .build();
    for (n, v) in previous {
        match v {
            Some(v) => std::env::set_var(n, v),
            None => std::env::remove_var(n),
        }
    }
    let result = result.expect("native LLVM build must succeed");
    assert_eq!(result.failed, 0);
    let run = std::process::Command::new(executable).output().unwrap();
    assert!(run.status.success(), "status={} stderr={}", run.status, String::from_utf8_lossy(&run.stderr));
    assert_eq!(String::from_utf8_lossy(&run.stdout).trim(), "le=33");
}

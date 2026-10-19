#![cfg(target_os = "linux")]
//! Native vs interpreter parity for a packed-array element read through an
//! untyped (ANY) receiver.
//!
//! `fn f(data): data[0]` lowers to `rt_index_get`. Natively that resolves to
//! the core-C `runtime_native.c` twin, which forwarded the RAW slot of a
//! packed `[u8]` / `[u64]` array instead of a tagged RuntimeValue, so 56
//! (0b111000) later decoded as 7. That corrupted native gzip/deflate output
//! (`lz77_compress` builds `[0, data[pos], 0]` through an untyped receiver).
//! Bug: doc/08_tracking/bug/native_index_get_packed_raw_slot_2026-10-19.md

use assert_cmd::Command;
use std::fs;
use std::path::{Path, PathBuf};
use tempfile::tempdir;

fn project_root() -> PathBuf {
    let manifest = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    manifest.parent().unwrap().parent().unwrap().to_path_buf()
}

fn run_interpreter(source: &Path) -> String {
    let assert = Command::new(assert_cmd::cargo::cargo_bin!("simple"))
        .current_dir(project_root())
        .env("SIMPLE_EXECUTION_MODE", "interpret")
        .arg(source)
        .assert()
        .success();
    String::from_utf8(assert.get_output().stdout.clone()).expect("utf8 stdout")
}

fn run_native(source: &Path, dir: &Path) -> String {
    let output = dir.join("native_probe");
    Command::new(assert_cmd::cargo::cargo_bin!("simple"))
        .current_dir(project_root())
        .arg("compile")
        .arg(source)
        .arg("--native")
        .arg("-o")
        .arg(&output)
        .assert()
        .success();
    let assert = Command::new(&output).assert().success();
    String::from_utf8(assert.get_output().stdout.clone()).expect("utf8 stdout")
}

fn assert_native_matches_interpreter(name: &str, program: &str, expected: &str) {
    let dir = tempdir().expect("tempdir");
    let source = dir.path().join(name);
    fs::write(&source, program).expect("write source");
    let interp = run_interpreter(&source);
    assert!(interp.contains(expected), "interpreter output {interp:?} lacks {expected:?}");
    let native = run_native(&source, dir.path());
    assert_eq!(native, interp, "native output must match the interpreter");
}

#[test]
fn untyped_receiver_index_of_each_narrow_int_array_is_tagged() {
    let program = "\
fn first_of(data):
    var toks = []
    toks.push([0, data[0], 0])
    toks[0][1]

fn main():
    val a: [u8] = [56u8, 200u8]
    val g: [u64] = [56u64]
    val x1: i64 = first_of(a)
    val x2: i64 = first_of([56i8])
    val x3: i64 = first_of([56i16])
    val x4: i64 = first_of([56i32])
    val x5: i64 = first_of([56u16])
    val x6: i64 = first_of([56u32])
    val x7: i64 = first_of(g)
    val x8: i64 = first_of([56])
    val b: bool = first_of([true])
    val last: i64 = a[1]
    print \"u8={x1} i8={x2} i16={x3} i32={x4} u16={x5} u32={x6} u64={x7} i64={x8} bool={b} typed={last}\"
";
    assert_native_matches_interpreter(
        "untyped_narrow_index.spl",
        program,
        "u8=56 i8=56 i16=56 i32=56 u16=56 u32=56 u64=56 i64=56 bool=true typed=200",
    );
}

#[test]
fn native_raw_deflate_of_multiple_of_eight_bytes_matches_interpreter() {
    // Literal bytes that are multiples of 8 were the corrupted ones.
    let program = "\
use std.nogc_sync_mut.compression.gzip.lz77.{lz77_compress}
use std.nogc_sync_mut.compression.gzip.deflate.{deflate_block_fixed_sync_flush}
use std.nogc_sync_mut.compression.gzip.inflate.{inflate}

fn main():
    var data: [u8] = []
    for i in 0..64:
        val byte: u8 = ((i * 8) % 256) as u8
        data.push(byte)
    val df = deflate_block_fixed_sync_flush(lz77_compress(data, 1))
    val back = inflate(df)
    var same = back != nil
    if same:
        val got = back.unwrap()
        same = got.len() == data.len()
        var i = 0
        while same and i < data.len():
            same = got[i] == data[i]
            i = i + 1
    val digits = \"0123456789abcdef\"
    var hex = \"\"
    for b in df:
        val v: i64 = b
        hex = hex + digits[v / 16] + digits[v % 16]
    print \"df={hex} roundtrip={same}\"
";
    assert_native_matches_interpreter("native_deflate_parity.spl", program, "roundtrip=true");
}

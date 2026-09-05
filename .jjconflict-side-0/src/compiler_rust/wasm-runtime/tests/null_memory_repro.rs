//! Standalone repro harness for the null-memory `ptr::copy` abort.
//! See doc/08_tracking/bug/wasm_bridge_null_ptr_copy_module_without_memory_2026-08-05.md
#![cfg(feature = "wasm")]

use simple_wasm_runtime::{WasiConfig, WasmRunner};

const NO_WASI_IMPORTS_WASM: &[u8] = &[
    0x00, 0x61, 0x73, 0x6d, 0x01, 0x00, 0x00, 0x00, // \0asm, version 1
    0x01, 0x05, 0x01, 0x60, 0x00, 0x01, 0x7f, // type:   () -> i32
    0x03, 0x02, 0x01, 0x00, // func:   #0 : type 0
    0x07, 0x08, 0x01, 0x04, b'm', b'a', b'i', b'n', 0x00, 0x00, // export: "main" = func 0
    0x0a, 0x06, 0x01, 0x04, 0x00, 0x41, 0x00, 0x0b, // code:   i32.const 0; end
];

#[test]
fn repro_null_memory_abort() {
    let dir = std::env::temp_dir().join(format!("simple_wasm_repro_{}", std::process::id()));
    std::fs::create_dir_all(&dir).expect("scratch dir");
    let wasm_path = dir.join("no_memory.wasm");
    std::fs::write(&wasm_path, NO_WASI_IMPORTS_WASM).expect("write fixture");

    let mut runner = WasmRunner::with_config(WasiConfig::new()).expect("create runner");
    let result = runner.run_wasm_file(&wasm_path, "main", &[]).expect("must not abort");
    let n = result.as_int();
    assert_eq!(n, 0, "expected i32.const 0 to round-trip as 0, got {n}");
}

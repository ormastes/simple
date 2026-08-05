# wasm bridge: null-pointer `ptr::copy` when running a module that exports no memory

**Status:** open
**Severity:** undefined behaviour (aborts the process)
**Found:** 2026-08-05, while adding a WASI-free regression fixture for capability enforcement.

## Symptom

Running a minimal, valid WebAssembly module that exports a function but **no
memory** aborts the host:

```
thread '...' panicked at library/core/src/ptr/mod.rs:626:9:
unsafe precondition(s) violated: ptr::copy requires that both pointer arguments are aligned and non-null

This indicates a bug in the program. This Undefined Behavior check is optional, and cannot be relied on for safety.
thread caused non-unwinding panic. aborting.
... (signal: 6, SIGABRT: process abort signal)
```

Because the panic is non-unwinding it cannot be caught, so it takes the whole
process with it — in a test run that means the remaining tests never report and
no `test result:` summary line is produced.

## Reproduction

The fixture is 38 bytes of hand-assembled wasm: type `() -> i32`, one function,
export `"main"`, body `i32.const 0`. No imports, no memory.

```rust
const NO_WASI_IMPORTS_WASM: &[u8] = &[
    0x00, 0x61, 0x73, 0x6d, 0x01, 0x00, 0x00, 0x00,
    0x01, 0x05, 0x01, 0x60, 0x00, 0x01, 0x7f,
    0x03, 0x02, 0x01, 0x00,
    0x07, 0x08, 0x01, 0x04, b'm', b'a', b'i', b'n', 0x00, 0x00,
    0x0a, 0x06, 0x01, 0x04, 0x00, 0x41, 0x00, 0x0b,
];

let mut runner = WasmRunner::with_config(WasiConfig::new()).unwrap();
runner.run_wasm_file(&path_to_those_bytes, "main", &[]).unwrap(); // aborts
```

## Analysis

The module instantiates fine; the abort happens after the call, on the result /
output extraction path. A guest with no `memory` export leaves the bridge with a
null base pointer, and the copy is issued without checking it. Candidates:
`src/compiler_rust/wasm-runtime/src/bridge.rs` (`extract_result`,
`from_wasm_value`) and the memory-reading helpers used to marshal a returned
value out of guest memory.

Note this is reached only on the `needs_wasi == false` branch of
`WasmRunner::run_function`; a WASI-importing guest always exports memory in
practice, which is why the path has not been hit before.

## Not related to capability enforcement

Capability enforcement runs *before* this point and returns `Err` cleanly, so the
deny-direction tests never reach the abort. The allow-direction test in
`src/compiler_rust/driver/tests/wasi_capability_enforcement.rs`
(`wasi_free_module_is_not_refused_when_nothing_ungranted_is_offered`) therefore
asserts the policy verdict instead of driving the run to completion, and should
be restored to a full `run_wasm_file` assertion once this is fixed.

## Wanted

Null-check the guest memory base (and return a clear `WasmError` such as
"module exports no memory") instead of issuing `ptr::copy` from a null pointer.

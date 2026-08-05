# wasm bridge: null-pointer `ptr::copy` when running a module that exports no memory

**Status:** fixed 2026-08-05
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

## Resolution (2026-08-05)

The analysis above was wrong about *where* the abort happens, and the "Wanted"
null-check above is not the applicable fix. Reproducing the exact 38-byte
fixture with `RUST_BACKTRACE=full` shows the abort is not in this crate at all
and is not on any result/output-extraction path -- it happens *during module
instantiation*, before `run_function` ever calls the guest function:

```
17: wasmer_vm::instance::InstanceHandle::new
18: wasmer_compiler::engine::artifact::Artifact::instantiate  (vendor/wasmer-compiler/src/engine/artifact.rs:376)
19: wasmer::sys::module::Module::instantiate                  (vendor/wasmer/src/sys/module.rs:369)
20: wasmer::sys::instance::Instance::new                      (vendor/wasmer/src/sys/instance.rs:121)
21: simple_wasm_runtime::runner::WasmRunner::run_function      (wasm-runtime/src/runner.rs:169)
```

`bridge.rs::extract_result`/`from_wasm_value` were never involved: for an
`i32` return they never touch guest memory at all, so there was never a guest
memory base to null-check on this path.

**Root cause (exact site):**
`src/compiler_rust/vendor/wasmer-types/src/vmoffsets.rs`,
`VMOffsets::precompute()` (the block computing `vmctx_signature_ids_begin`
through `vmctx_globals_begin`, originally lines 288-326). Every `vmctx_*_begin`
field there is laid out back-to-back with `offset_by(base, count, item_size)`
and **no alignment padding**, except `vmctx_globals_begin` which the function
already wraps in `align(..., 16)`. `vmctx_imported_functions_begin` in
particular is placed immediately after the `signature_ids` array
(`num_signature_ids * size_of::<VMSharedSignatureIndex>()`, 4 bytes per
entry). The repro module declares exactly one function type, so
`vmctx_signature_ids_begin = 0` and `vmctx_imported_functions_begin = 4` --
4-byte aligned but not pointer-aligned (8 on x86_64). That misaligned offset
becomes the destination pointer passed into
`InstanceHandle::new`'s `ptr::copy(..., instance.imported_functions_ptr() as
*mut VMFunctionImport, imports.functions.len())` in
`vendor/wasmer-vm/src/instance/mod.rs:1159-1163` -- and Rust's `ptr::copy`
alignment precondition is checked **even when the copy length is 0** (both
`imports.functions` and every other import vector are empty for this
guest, since it imports nothing). Confirmed by instrumenting each of the six
`ptr::copy` calls in `InstanceHandle::new` with an `eprintln!` of
`src`/`dst`/`len` immediately beforehand: the signature-ids copy printed and
succeeded (`src=0x75d798013c60 dst=0x75d798021e20 len=1`), the
imported-functions copy printed (`src=0x8 dst=0x75d798021e24 len=0`) and then
aborted inside that exact call -- `0x...e24` is 4 mod 8, not pointer-aligned.

This is not specific to "no memory": it reproduces for *any* module whose
cumulative preceding-region byte size leaves an unaligned start for a
pointer-containing vmctx region (imported functions/tables/memories/globals,
or the local tables/memories regions), which in practice depends on the
module's function-type count and import/table/memory counts, not on whether
it happens to export memory. Confirmed independently: the pre-existing (and
otherwise unrelated) `driver/tests/wasm_tests.rs::test_parity_factorial` hit
the identical `ptr::copy ... aligned and non-null` SIGABRT on the unpatched
baseline. On x86_64/aarch64 an unaligned pointer-sized copy has always been
silently tolerated by the hardware, which is why this went unnoticed until
Rust's `ptr::copy` UB-check (active whenever `debug_assertions` is on, i.e.
every `cargo test`) started enforcing the alignment precondition strictly.

**Fix:** `src/compiler_rust/vendor/wasmer-types/src/vmoffsets.rs` --
`VMOffsets::precompute()` now wraps every `vmctx_*_begin` computation (for
`imported_functions`, `imported_tables`, `imported_memories`,
`imported_globals`, `tables`, `memories`) in `align(..., pointer_size)`,
mirroring the pattern the function already used for `vmctx_globals_begin`
(there widened to 16 for v128 globals). `vmctx_signature_ids_begin` is
unchanged (always 0, trivially aligned). Since every other consumer of these
offsets -- both `wasmer-vm`'s runtime pointer arithmetic and
`wasmer-compiler-cranelift`'s generated machine code -- goes through the same
`VMOffsets` getter methods rather than recomputing raw math, padding here is
transparent and does not require any other change.

This is a vendored third-party crate (`src/compiler_rust/vendor/**`, normally
out of scope per repo convention), patched here because the actual defect
lives there and no host-side guard in `simple-wasm-runtime` can intercept it:
the panic is a non-unwinding abort raised from inside `Instance::new`, before
control returns to any of our code, so it cannot be caught or worked around
from the caller. The vendored `.cargo-checksum.json` for
`vendor/wasmer-types` was updated to match (cargo's directory-source loader
verifies per-file checksums and refuses to build otherwise, printing "if
modifications are required then it is recommended that `[patch]` is used with
a forked copy of the source" -- noted here as a possible cleaner long-term
packaging, not done in this change to keep the diff minimal and reviewable).

**Tests:**
- `src/compiler_rust/wasm-runtime/tests/null_memory_repro.rs` (new) -- runs
  the exact 38-byte fixture from this doc through
  `WasmRunner::run_wasm_file` end-to-end and asserts `Ok(0)`, no abort.
- `src/compiler_rust/driver/tests/wasi_capability_enforcement.rs` --
  `wasi_free_module_is_not_refused_when_nothing_ungranted_is_offered` restored
  to drive `run_wasm_file` to completion and assert the result, instead of
  only asserting the capability verdict.

**Verification:**
- `cargo test -p simple-wasm-runtime --features wasm --test null_memory_repro`
  -- `1 passed`.
- `cargo test -p simple-driver --features wasm --test wasi_capability_enforcement`
  -- `11 passed` (all pre-existing tests plus the restored one).
- `cargo test -p simple-driver --features wasm --test wasm_tests` -- no longer
  aborts; all 20 cases now run to completion and report a
  `test result: ...` summary line (they still fail, but on a distinct,
  pre-existing, unrelated defect -- "wasm execution: Function 'main' not found
  in WASM module" -- confirmed present on the unpatched baseline too and out
  of scope for this bug).
- Sabotage check: reverted `vmoffsets.rs` to the unpatched baseline (checksum
  included) and reran `null_memory_repro` -- the exact original abort
  reproduced verbatim (`unsafe precondition(s) violated: ptr::copy requires
  that both pointer arguments are aligned and non-null`, SIGABRT). Restored
  the fix and reran -- passes again.

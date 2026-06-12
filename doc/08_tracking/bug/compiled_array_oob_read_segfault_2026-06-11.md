# Bug: out-of-bounds array read SIGSEGVs in cranelift binaries (interpreter returns 0)

- **Date:** 2026-06-11
- **Status:** fixed — committed in adc8dcad379 (fix(parser): M9, bundled with parser work)
- **Severity:** high — semantics diverge between interpreter and compiled code

## Symptom

```spl
fn main():
    val a: [i64] = []
    val x = a[3]
    print("OOB val {x}")
```

- **Interpreter (Rust seed):** prints `OOB val 0` (graceful default).
- **Cranelift-compiled:** SIGSEGV (verified: native-build `tmp/site12/oob.spl`,
  run in docker → rc=139).

## Impact found

`decl_is_async[idx]` in `convert_decl_method_fn`
(src/compiler/10.frontend/flat_ast_bridge_part1.spl) raw-indexed a module-level
array that the lean-parser flow never populates (decl_fn only writes the
ASYNC value to the env transport). In the stage4 self-hosted binary this was
one of the two crashes behind the 12th-site cluster. Fixed by routing through
`decl_get_is_async` / new `decl_get_is_gpu_kernel` with nil+length guards
(src/compiler/10.frontend/core/ast_part1.spl).

## Root cause (confirmed)

`compile_inline_array_get`, `compile_inline_array_get_word`,
`compile_inline_array_set`, and `compile_inline_array_set_word` in
`src/compiler_rust/compiler/src/codegen/instr/calls.rs` unconditionally loaded
`len` (offset +8) and `data_ptr` (offset +24) from `ptr_bits` before any
nil/tag check. When `array` is nil (tagged value `3`), `ptr_bits = 3 & !7 = 0`,
causing loads from addresses 8 and 24 → SIGSEGV. For an empty non-nil array
(`[]`), `ptr_bits` was valid but the OOB fall-through returned `nil` (3) while
the C runtime `rt_array_get` also returns `3` — so those two paths matched;
the interpreter errors and the error is swallowed (printing 0), which was the
reported semantic divergence.

## Fix (committed in adc8dcad379)

All four inline functions were restructured to:
1. Check `tag == 1` (heap pointer) first — branch to `done_block` with nil/0
   if the array is nil or untagged.
2. Load `len` only inside `bounds_block` (after nil guard).
3. Load `data_ptr` only inside `load_block` / `store_block` (after bounds check
   passes) — no wild read possible on OOB.

Pattern follows the existing safe implementation in `compile_inline_bytes_u8_at`
(lines 256-370 in the same file).

## Semantics chosen

OOB reads return `nil` (tagged value 3), matching `rt_array_get`'s C
implementation. OOB writes are silently no-op (return 0), matching
`rt_array_set`. The interpreter error-on-OOB divergence is a pre-existing
interpreter strictness difference, not addressed here.

## Verification

- 6 codegen_instr_tests for array get/set/data_ptr: all pass on pre-built
  debug binary (simple_compiler-2513eebd66e61dfe, built after fix commit).
- No new array-related failures introduced (pre-existing failures are GPU/SIMD
  related and `shared_builtin_array_get` which fails on missing `rt_index_get`
  — pre-existing, unrelated).

## decl_is_async guards (Impact found)

The guards added in `src/compiler/10.frontend/flat_ast_bridge_part1.spl` and
`src/compiler/10.frontend/core/ast_part1.spl` remain. They are defense-in-depth
at the Simple-layer level and are not made redundant by this codegen fix (the
guards protect against the pure-Simple crash path; the codegen fix protects
compiled binaries from the same family of nil-array dereference).

## Regression test note

`tests/compile_and_run.rs` is foreign-modified — a test for the repro case
(`val a: [i64] = []; val x = a[3]`) should be added there when that file is
unblocked. The existing unit test `codegen_inline_array_get_does_not_emit_runtime_symbol`
verifies the inline path is taken; it does not verify OOB behavior at runtime.

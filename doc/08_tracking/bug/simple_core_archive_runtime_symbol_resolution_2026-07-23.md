# Bug: simple-core archive local runtime symbol resolution — 2026-07-23
## Closed 2026-09-16 — Status "SOURCE FIXED"; fix + focused Rust regression described in body; archive probe tracked separately

Reviewed in the 2026-09-16 bug-ledger normalization pass; classification is
bookkeeping from in-file evidence, not a re-run of the repro. Re-open with a
fresh dated repro if the symptom returns.

**Status:** SOURCE FIXED / ARCHIVE QUALIFICATION PENDING

## Verification note — 2026-11-25 (release/1.0.0 P2 batch)

SOURCE FIXED re-confirmed by code inspection on release/1.0.0 HEAD
(4bc2c986375): `resolve_runtime_func` in
`src/compiler_rust/compiler/src/codegen/instr/helpers.rs:477-483` prefers the
local `func_ids` declaration and only falls back to the `runtime_funcs`
import, and every `call_runtime_*` helper routes through it. The focused Rust
regression (`cargo test`) cannot be re-run on this Windows host (no cargo
builds permitted; the pinned bin/simple.exe also rejects
`@representation_boundary` at HEAD), so verification is by code inspection
only. ARCHIVE QUALIFICATION remains PENDING as tracked.

## Reproduction

```sh
cd src/compiler_rust
cargo test -p simple-compiler pipeline::native_project::tests::test_simple_core_source_tree_emits_partial_runtime_archive -- --exact
```

Before this fix, `core_string.spl` compilation panics in
`rt_native_eq_inner` with `missing runtime fn 'rt_native_neq'`.

## Root cause and fix

The exact simple-core archive path can define `rt_native_neq` locally while a
generated `NotEq` still calls the shared runtime helper. That helper previously
looked only in `runtime_funcs` and panicked even though the local function was
already declared in `func_ids`.

`call_runtime_*` now prefers a local declaration and falls back to the runtime
import. A focused Rust regression compiles generated `NotEq` over `ANY` values
with a locally defined `rt_native_neq`, asserting that no runtime import is used.

This does not prove the archive passes. Keep the existing exact archive probe
as the qualification gate, and track its independent tuple-row failure in
[`simple_core_value_memory_probe_dict_entries_failure_2026-07-19.md`](simple_core_value_memory_probe_dict_entries_failure_2026-07-19.md).


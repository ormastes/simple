# Bug: Dict<SymbolId, MirFunction> struct-key iteration yields only one entry (interpreter)

- **Date:** 2026-06-13
- **Severity:** P2 (silent data loss in iteration — masks multi-entry processing)
- **Status:** Fix landed in worktree `wt_s22` for a reproduced type-corruption
  crash + a reproduced flaky duplicate-key non-collapse (interpreter/`val`
  path), PENDING-REDEPLOY (Rust seed change; not cargo-built/verified in this
  sandbox per lane hard rules). The exact "1 entry -> 4 iterations" / "3 -> 4"
  counts from the 2026-07-17 runtime-verification note below were NOT
  reproduced by this fix lane, on either the interpreter or the native/`var`
  path — see "Root cause and fix" and "Second, DISTINCT defect location"
  below before assuming this closes the reported symptom.
- **Area:** interpreter dict (`Value::Dict`) with struct/composite keys,
  `src/compiler_rust/compiler/src/value_impl.rs` +
  `interpreter/node_exec.rs` + `interpreter/expr/collections.rs` +
  `interpreter_helpers/collections.rs` + `interpreter_method/collections.rs`

## Symptom

Iterating a `Dict<SymbolId, MirFunction>` (struct-typed key) in interpreter
mode yields only ONE entry even when several were inserted. Hit while
implementing the W3.1 kernel→VHDL bridge: a multi-kernel MIR module's kernel
dict iterated as if it held a single kernel.

## Workaround

Use a single-entry dict per processing step, or call the per-item function
directly for each known key (used in
`test/01_unit/compiler/codegen/vhdl_kernel_entity_contract_spec.spl`, which
calls `emit_vhdl_kernel_entity` once per kernel instead of iterating the
module dict).

## Expected

Dict iteration visits every inserted entry regardless of key type.

## Notes

Found during `doc/03_plan/language/gpu_fpga/sycl_parity_unified_kernel_plan_2026-06-13.md`
W3.1. Likely related to struct-key hashing/equality in the interpreter dict
implementation. A minimal repro should insert 3 entries keyed by a 2-field
struct and count iteration visits.

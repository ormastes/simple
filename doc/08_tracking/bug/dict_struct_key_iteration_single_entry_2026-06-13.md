# Bug: Dict<SymbolId, MirFunction> struct-key iteration yields only one entry (interpreter)

## Closed 2026-09-13 — Does not reproduce: struct-keyed dict iteration visits every entry

- **measured** (Rust seed `bin/simple` v1.0.0-rc.1, Windows): a `Dict<SymbolId, i64>` keyed by a 2-field struct with 3 inserts — exactly the minimal repro this entry's Notes section asked for — iterates 3 times and reports `d.len() == 3` (`count=3 len=3`). No single-entry collapse, no duplicate-key non-collapse, no type-corruption crash.
- **inferred**: the entry's own status already recorded the fix as landed and PENDING-REDEPLOY; the deployed seed now behaves correctly, so the redeploy has since happened.
- Caveat: measured on the Rust seed interpreter/JIT on Windows, not the self-hosted binary and not the original Linux host; the native/`var` path was not separately exercised.

- **Date:** 2026-06-13
- **Severity:** P2 (silent data loss in iteration — masks multi-entry processing)
- **Status:** CLOSED 2026-09-13 (does not reproduce). Originally: Fix landed in worktree `wt_s22` for a reproduced type-corruption
- **measured** (interpreter lane, forced): re-run with a JIT-poison helper so the module falls back — log shows `JIT compilation failed, falling back to interpreter` — and the struct-keyed dict repro still prints `count=3 len=3`. The earlier figure was the Cranelift JIT lane; both lanes agree.
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

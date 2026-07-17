# Bug: Dict<SymbolId, MirFunction> struct-key iteration yields only one entry (interpreter)

- **Date:** 2026-06-13
- **Severity:** P2 (silent data loss in iteration — masks multi-entry processing)
- **Status:** Open
- **Area:** interpreter dict iteration with struct/composite keys

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

## Runtime verification (2026-07-17)

Probed with 3 entries inserted into `Dict<Key,i64>` (2-field struct key). Symptom drifted from documented single-entry undercounting: `d.len()` now reports **4** (overcounting by 1), and iteration crashes with `error: semantic: undefined field: unknown property or method 'a' on String` — one of the iterated "keys" is a plain String, not a Key struct. This is not the exact documented symptom but clearly the same underlying struct-key Dict corruption class and is at least as broken (type confusion + silent over-counting).

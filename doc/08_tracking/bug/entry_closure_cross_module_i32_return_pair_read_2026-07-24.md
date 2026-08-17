# Bug: entry-closure cross-module calls lose declared return type — rv32 reads i32 returns as a0/a1 pair

- **Date:** 2026-07-24
- **Severity:** P0 wrong-code on 32-bit targets (silent); type-degradation on all targets
- Status: FIXED
- Status re-verified 2026-08-17 by source inspection (triage shard 01).

## Symptom

NVMe rv32 fw: sections map/pt failed (`_rv32_pt_critical_warning(313,-1) != 0`
style checks) in the 180-file build while the SAME case functions passed when
called from the entry module or in a small closure. Disassembly of the failing
caller showed:

```
jalr  ra            # call _rv32_pt_throttled(...) -> i32
or    a0, a0, a1    # caller treats result as i64 REGISTER PAIR
bnez  a0, fail
```

`a1` is not defined by the ilp32 ABI for an i32 return — whenever the callee
left a nonzero high-half residue, every comparison poisoned.

## Root cause

On the non-bootstrap entry-closure lane (`driver_pipeline.spl lower_to_mir`),
the ENTRY module lowers before its dependency modules. A cross-module call's
declared return type had no source:
- `fn_return_types` (id-keyed) was never populated anywhere, and symbol IDs
  are per-module-table so an id-keyed map cannot answer cross-module anyway.
- The symbol-table fallback (`found_sym.type_`) is frequently not
  Function-kind on this lane (unresolved infer var).
→ return type defaulted to erased i64 → rv32 callers emitted pair-reads.

Same disease class as `native_call_return_type_loss_2026-07-23` (fixed for the
SIMPLE_BOOTSTRAP flat lane with the Str-only `bootstrap_fn_ret_types` MirType
registry) and the struct-field prescan (`prescan_module_struct_names`).

## Fix

1. `mir_data.spl`: global `bootstrap_fn_ret_hir_type_register/lookup` —
   name-keyed `Dict<text, HirType>` accumulated across the closure; duplicate
   free-fn names (e.g. two `main`s) are marked ambiguous and never answered.
2. `prescan_module_struct_names` (module_lowering.spl): register every free
   fn's declared HIR return type — the driver already calls this prescan for
   EVERY closure module before lowering ANY of them.
3. `resolved_call_hir_return_type` (expr_dispatch.spl): consult the registry
   after the id-keyed map, before the unreliable symbol-table fallback.
4. `MirLowering` ctor now initializes `fn_return_types` (was omitted →
   nil-filled/garbage field; separate interp crash).

## Verification

map+pt standalone rv32 repro: all 13 case checks 0 (were g=3/h=1/c=1/f=3).
Full gate: `check-nvme-rv32-minimal-live.shs`.

## Follow-ups

- Regression test: two-module fixture (callee `-> i32`, caller compares to a
  literal) compiled for riscv32-unknown-none; objdump must not `or a0,a0,a1`
  an i32 call result (or QEMU-run a check).
- The Str-only MirType registry (flat lane) and this HIR registry should
  eventually merge into one mechanism.

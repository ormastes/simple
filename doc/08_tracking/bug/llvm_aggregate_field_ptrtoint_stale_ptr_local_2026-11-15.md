# LLVM aggregate field store emits `ptrtoint` on an i64-defined local (stale ptr flag)

- **Status:** verification-pending
- **Found:** 2026-11-15, kept `message.module.ll` (lib.nogc_sync_mut.io.process_ops)
- **Symptom:** llc-18: `'%l28' defined with type 'i64' but expected 'ptr'` at
  `%t5125 = ptrtoint ptr %l28 to i64`, where
  `%l28 = call i64 @..._process_observation_live_owner_v1(...)` (struct-returning fn).

## Root cause
`src/compiler/70.backend/backend/_MirToLlvm/aggregate_intrinsics.spl`
(Struct/Tuple/Array aggregate field stores, SetField, Cast/Bitcast) took the
operand type from `get_operand_type[_at]`, which trusts the sticky
`ptr_locals` priming flag (set from the MIR struct type) over `local_types`,
which `translate_call` had already overridden to the callee's real `i64` return.
`store_field_bits_verbatim` then emitted `ptrtoint ptr` on an i64 value.
Same class as bug #149 (translate_copy_move) and PR #9424 (call args).

## Fix
New `fresh_operand_type` prefers `local_types[id]`, falling back to the sticky
flags; used at all verbatim field-store and cast/bitcast sites.

## Evidence
- Spec: `test/01_unit/compiler/backend/llvm_aggregate_field_stale_ptr_local_spec.spl`
  (fails before, passes after).
- Kept module: 9 such `ptrtoint` sites + 1 `rt_native_eq(ptr %lN)` call-arg site
  (already fixed by #9424; module predates it). With those patched, llc-18 emits
  the object cleanly.

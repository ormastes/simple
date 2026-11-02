# Fixpoint determinism: emitters walk Dict<SymbolId,_> in key-address order (2026-11-02)

- **ID:** fixpoint_emission_order_dict_iteration_2026-11-02
- **Priority:** P1 (stage4 vs stage5 self-build fixpoint)
- **Status:** fixed in source (lane sbr-3); residual items below are open
- **Spec:** `test/01_unit/compiler/backend/native/emission_order_determinism_spec.spl`
  (fails before the fix, passes after)

## Root cause
On the native runtime `rt_core_dict_hash` hashes heap keys such as `SymbolId`
by pointer, so `module.functions.keys()` / `.values()` iterate in allocation
order. The LLVM lane already used `mir_module_functions_sorted` (see
`native_build_symbolid_dict_emission_nondeterminism_2026-10-19.md`). Other
emitters did not.

## Fixed (sorted by name, with symbol id as the tie-break)
- `70.backend/backend/native/isel_x86_64.spl` module function loop
- `70.backend/backend/native/isel_aarch64.spl` module function loop
- `70.backend/backend/native/isel_riscv64.spl` module function loop and the scalable-vec guard
- `70.backend/backend/native/isel_riscv32.spl` module function loop
- `70.backend/backend/cranelift_codegen_adapter.spl` direct and adapter declare/compile passes, and statics
- `70.backend/backend/wasm_codegen_adapter.spl` function/type index space
- `70.backend/backend/_MirToLlvm/core_codegen.spl` extern `declare` lines (`unknown_func_decls` keys)
- `80.driver/driver_aot_native_output.spl` phase-compatibility manifest items (encoded and digested in this order)
- `80.driver/driver_build/incremental.spl` persisted `build_cache.sdn` entry order

## Follow-up (lane sbr-3b)
Spec: `test/01_unit/compiler/driver/fixpoint_fingerprint_determinism_spec.spl`.
- `incremental.spl` fallback fingerprints: the three tree fingerprints (compiler,
  stdlib, frontend) no longer seed `fp` with `unfingerprintable-{pid}-{micros}`;
  if the temp-file digest fails they hash the manifest text (`sha256-text:`). The
  runtime-provider fingerprint returns `missing` / `empty` (was pid+time) and a
  `dir-sha256-text:` content hash instead of a pid/time fallback. The
  unreadable-input early returns (dir listing or file hash failed) stay
  pid/time-unique on purpose: the value is part of the cache scope key, and a
  fixed sentinel would match a stored entry from another unreadable tree.
- `driver_aot_native_output.spl` owner token (v1 and v2): lock claim only. It goes
  to `coordinator_claim_v1` / `coordinator_complete_v1`; `BuildActionResultV1` (the
  only record leaving the coordinator) has no owner field. No code change beyond a
  comment; the spec asserts the result struct/constructor and token uses.
- `generic_instance_object_producer_v1.spl` was deleted by ab9305d783e (40.mono
  pass removal) and is absent on release/1.0.0; nothing to sort.

## Open (not fixed in this lane)
- Rust seed `src/compiler_rust/compiler/src/linker/smf_writer.rs` writes `repr(C)`
  `SmfSection`/`SmfSymbol`/`SmfRelocation`/`SmfHeader` structs with
  `from_raw_parts`, so uninitialized padding bytes reach the `.smf` file.
  Observed: `bin/simple.exe compile m.spl -o m.smf` run twice gives 8 differing
  bytes, at section-header offsets 1..3 (the pad after `section_type`). The seed
  is bootstrap-only, so this does not affect the stage4/stage5 fixpoint. The
  pure-Simple `smf_writer.spl` writes explicit zero pad.

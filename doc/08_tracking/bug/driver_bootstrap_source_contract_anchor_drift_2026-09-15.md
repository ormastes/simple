# Driver/bootstrap source-contract specs assert anchors that moved (2026-09-15)
## Open 2026-09-16 — needs owner triage

Reviewed in the 2026-09-16 bug-ledger normalization pass; no resolution
evidence found in the body. This is bookkeeping, not verification.

Test-wave triage of `test/01_unit/compiler/driver/` (agent C lane). Several
"source contract" specs `file_read` a driver module and assert exact code
strings (`to_contain` / `find(...) > -1`). The bootstrap/MIR-lowering code was
restructured — content moved between files and shapes changed — so the specs'
anchors are stale. Spec-side mechanical bugs (undefined helper vars, unescaped
`{...}` interpolation inside assertion strings, `():`-style return types,
relative seed paths) were fixed in the same pass; the failures below remain RED
because the asserted strings genuinely no longer exist where the spec reads.

## Affected specs (representative, not exhaustive)

- `bootstrap_context_mir_source_spec.spl` — 15 examples: expected strings now
  live in `src/compiler/50.mir/_MirLowering/*` (e.g. `bootstrap_mir_functions_add`
  is in `bootstrap_globals.spl` / `module_lowering.spl`), not in
  `src/compiler/80.driver/driver_bootstrap.spl`. The spec reads only
  driver_bootstrap.spl.
- `bootstrap_flat_nonentry_globals_source_spec.spl` — anchors gone:
  `name == bootstrap_entry_module_name(self.ctx)` (hoisted to
  `val bootstrap_entry_name = ...` in driver_hir_pipeline_lowering.spl:502),
  `val (analyzed_ctx, analyze_ok) = self.lower_and_check_routed_impl(streaming_route)`,
  `driver_inputs = [native_entry_input]`,
  `fatal MIR lowering rejected bootstrap closure module {extra_name}`
  (string exists nowhere in src).
- `native_entry_closure_gate_source_spec.spl` — `nb_entry_closure_pre` branch
  anchors no longer exist in driver.spl (example "gates entry closure on errors
  added by the closure walk", `find(...) ?? -1` → -1).
- `native_cache_granularity_contract_spec.spl` — cache-key literal
  `"{hash}+src{src_fp}"` no longer exists in driver_build/incremental.spl.

## Unblock condition

The owning lane must either repoint these specs at the current module files and
current code shapes (preserving assertion strength), or the moved code must be
restored. Do not "fix" by deleting the stale assertions.

## Note

`aggregate_copy_tag_guard_source_spec.spl` and
`struct_init_checked_allocator_source_spec.spl` assert exact strings of the Rust
seed's cranelift codegen sources (e.g. `store(MemFlags::new(), zero, new_ptr,
off)`) which no longer appear in `src/compiler_rust/compiler/src/codegen/` —
same class, Rust-side.


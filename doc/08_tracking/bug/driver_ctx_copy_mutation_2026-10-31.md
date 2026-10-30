# Driver mutates a copy of `self.ctx` (take-a-copy-then-mutate)
## Open 2026-10-31 (partially fixed)

- Severity: high on the interpreter lane (silent loss of driver state)
- Ruling: classes are value types (`doc/07_guide/language/capability_library_authoring.md`).
  `val ctx = self.ctx` / `_extract_driver_ctx(self)` is a copy; mutations through it
  never reach the driver. Interpreter calls write a mutated class argument back only
  when the argument is an lvalue (`self.ctx`).
- The JIT lane hides this because it aliases class instances
  (`jit_class_instances_alias_instead_of_copy_2026-09-27.md`).

## Fixed
- #5562: cold-HIR recorders and persistence in `_compile_to_native_with_backend_session`
  (Phase 2 hello blocker #4, `cold-hir-object-identity-invalid`).
- work/driver-ctx-copy-sites-20261031: demand SCC publication completion and
  publish calls (`driver_aot_native_output.spl` ~2806/3079, `driver_aot_smf_output.spl:142`).

## Still to audit (from Opus review, not verified)
- `var ctx = self.ctx` returning `(CompileContext, bool)`: `driver_hir_pipeline_passes.spl:169,224`,
  `driver_hir_pipeline_lowering.spl:2613` — confirm every caller assigns the result back to `self.ctx`.
- `*_ctx: CompileContext = self.ctx` copies in `driver_source_parse_retained.spl` (234, 255, 470-488,
  569-597), `driver_source_parse_streaming.spl:350`, `driver_hir_pipeline_lowering.spl`
  (1290, 1408, 1466, 2199) — any `add_error`/`demand_*` mutation expected to reach the driver is lost.
- `val ctx = self.ctx` in `driver_aot_codegen_outputs.spl` (40, 64, 113, 137, 162, 196),
  `driver_riscv_gen2_product.spl` (260, 301, 339, 374, 419), `driver_aot_native_output.spl:1963`.

## Fix rule
Pass `self.ctx` (not a local copy) to any helper that mutates it, or assign the copy back
explicitly. Regression shape: `test/01_unit/compiler/driver/driver_ctx_owner_writeback_spec.spl`.

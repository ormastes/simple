# Driver mutates a copy of `self.ctx` (take-a-copy-then-mutate)
## Resolved 2026-10-31

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

## Audit (2026-10-31, work/rootcause-2-20261031)
Every `= self.ctx` / `: CompileContext = self.ctx` copy in `src/compiler/80.driver`
(grep `(=|:) *self\.ctx *$`) plus the two `_extract_driver_ctx(self)` sites.

Root cause of the remaining loss: commit 9a0cfd1e5d6 ("harden staged native compilation")
replaced `self.ctx.mark_module_poisoned(..)` / `self.ctx.poison_budget_exhausted()` with a
local `poison_ctx`/`rejected_ctx` copy. On the interpreter lane the poisoned list/count never
reached the driver, so the collect-all `[collect-all] poisoned:` summary, the AOT
poisoned-module accounting (`driver_aot_pipeline.spl:412`), the HIR-archive gate
(`driver_hir_archive_weave_inputs_v1.spl:78`), and the `--fail-fast` / 200-module
`poison_budget_exhausted()` cap (fresh copy each iteration, count stays 0) were all wrong.
Fix keeps the copy shape the native hardening chose and writes it back
(`self.ctx = poison_ctx`) right after `mark_module_poisoned`.

| Site | Mutated? | Status |
|---|---|---|
| `driver_hir_pipeline_passes.spl:169` `resolve_methods_impl` | yes (hir_modules, add_error) | read-only for driver: copy is returned in `(ctx, ok)`; no Simple callers |
| `driver_hir_pipeline_passes.spl:224` `type_check_impl` | no | read-only (no-op, returned) |
| `driver_hir_pipeline_lowering.spl:2609` `lower_to_hir_impl` | yes | read-only for driver: copy returned; no Simple callers |
| `driver_source_parse_retained.spl:234` rejected_ctx | yes (poison) | **fixed** (write-back) |
| `driver_source_parse_retained.spl:255` poison_ctx | yes (poison) | **fixed** |
| `driver_source_parse_retained.spl:470` rejected_ctx | yes (poison) | **fixed** |
| `driver_source_parse_retained.spl:473` boot_rejected_ctx | yes (modules) | ok: returned, `parse_all_committing_impl` assigns `self.ctx = parsed_ctx` |
| `driver_source_parse_retained.spl:485` poison_ctx | yes (poison) | **fixed** |
| `driver_source_parse_retained.spl:488` boot_poisoned_ctx | yes (modules) | ok: returned and assigned back |
| `driver_source_parse_retained.spl:569` rejected_ctx | yes (poison) | **fixed** |
| `driver_source_parse_retained.spl:572` provider_rejected_ctx | yes (modules) | ok: returned and assigned back |
| `driver_source_parse_retained.spl:594` poison_ctx | yes (poison) | **fixed** |
| `driver_source_parse_retained.spl:597` poisoned_ctx | yes (modules) | ok: returned and assigned back |
| `driver_source_parse_streaming.spl:350` poison_ctx | yes (poison) | **fixed** |
| `driver_hir_pipeline_lowering.spl:1290` poison_ctx | yes (poison) | **fixed** |
| `driver_hir_pipeline_lowering.spl:1408` poison_ctx | yes (poison) | **fixed** |
| `driver_hir_pipeline_lowering.spl:1466` poison_ctx | yes (poison) | **fixed** |
| `driver_hir_pipeline_lowering.spl:2199` poison_ctx | yes (poison) | **fixed** |
| `driver_aot_codegen_outputs.spl:40,64,113,137,162,196` | no (options/logger/mir_modules reads) | read-only |
| `driver_riscv_gen2_product.spl:260,301,339,374,419` | no (`gen2_product_config` and policy reads) | read-only |
| `driver_aot_smf_output.spl:123,155,181` | no (publish already uses `self.ctx`) | read-only |
| `driver_aot_native_output.spl:1963` `compile_to_native` (`_extract_driver_ctx`) | no | read-only |
| `driver_aot_native_output.spl:2026` (`_extract_driver_ctx`, #5562 function) | `freeze_storage_registry()` caches frozen rows on the copy | left: freeze is idempotent and recomputed from unchanged rows by later callers; noted as residual |

Regression: `test/01_unit/compiler/driver/driver_ctx_owner_writeback_spec.spl`
("driver poison-site write-back": budget stops at 2 and the driver sees both
poisoned modules; the unsaved-copy case visits all 4 and the driver sees 0).

## Fix rule
Pass `self.ctx` (not a local copy) to any helper that mutates it, or assign the copy back
explicitly. Regression shape: `test/01_unit/compiler/driver/driver_ctx_owner_writeback_spec.spl`.

# Representation Boundary (`E-MC-REP-001`) Phase 3 & Seed Blockers (2026-11-25)

## Summary

Mass-inserting `@representation_boundary(...)` across the 153 stdlib and compiler modules carrying `E-MC-REP-001` diagnostics (1,038 unique in `p3fix2_ll`) is currently blocked by three verified compiler/seed gaps. Adding `@representation_boundary(...)` to `src/lib/` or `src/compiler/` before these are resolved breaks pre-built Rust seed tooling and increases Phase 3 representation diagnostics instead of clearing them.

## Verified Blockers

### 1. Pre-built Rust seed binaries reject `@representation_boundary` at runtime
- **Locations:**
  - `src/compiler_rust/parser/src/parser_impl/attributes.rs:14-89` (`KNOWN_ATTRIBUTE_NAMES`)
  - `src/compiler_rust/compiler/src/decorator_apply.rs:37-76` (`is_directive_decorator`)
  - `src/compiler_rust/compiler/src/lint/checker_core.rs:539-633` (`KNOWN_DECORATORS`, `KNOWN_ATTRIBUTES`)
- **Observed errors:** When `@representation_boundary(...)` is present on imported `src/lib/` functions, `C:\dev\keep\seeds\simple-release-0354c53a8be.exe` aborts immediately on `test`, `run`, and `fix`:
  - `error: semantic: src/app/cli/lint_entry.spl:62:1: unknown decorator @representation_boundary on function volatile_read_u8`
  - `error: semantic: src/app/test_runner_new/test_runner_client.spl:26:1: unknown decorator @representation_boundary on function sosix_secure_temp_dir_set_parent`
  - `error: semantic: ...: unknown decorator @representation_boundary on function file_exists`
- **Status:** Source fix implemented in `work/fix-rust-seed-rep-boundary-attr-20261125`; pre-built seed binaries (`bin/simple.exe`, `C:\dev\keep\seeds\simple-release-0354c53a8be.exe`, CI seeds) must be rebuilt and promoted before `@representation_boundary` can live in `src/lib/` or `src/app/`.

### 2. `native-build` / `bootstrap_main` leaves `ctx.options.representation_sources = []`
- **Locations:**
  - `src/compiler/00.common/driver_compile_options.spl:75` (`representation_sources: [RepresentationSourceContextV1] = []`)
  - `src/compiler/80.driver/driver_hir_pipeline_passes.spl:445-447` (`if ctx.options.representation_sources.len() == 0`)
  - `src/compiler/35.semantics/representation_boundary/source_binding.spl:7-23` (`valid_context` check)
  - `src/compiler/35.semantics/representation_boundary/validation.spl:52,54` (`E-MC-REP-002`, `E-MC-REP-004`)
  - `src/compiler/10.frontend/core/representation_declarations_v1.spl:249` (disables AST/HIR body cache when `manifest != nil`)
- **Observed behavior:** Standalone compilation via `C:\dev\p3diag\p3fix2_ll\simple.exe compile ...` on `@representation_boundary`-annotated `src/lib/nogc_sync_mut/io/volatile_ops.spl` and `src/lib/nogc_sync_mut/sosix/secure_temp_dir.spl` still emitted `[WARN] [E-MC-REP-001]` (because without `representation_sources`, `source_binding.spl:22-23` refuses admission and `unsafe_observations.spl` falls back to unannotated observation), while explicit project-context binding via `representation_bind_hir_v1` in a synthetic harness succeeded with `RECEIPT msgs=0`.
- **Follow-up required:** Wire `representation_sources` population from `simple.sdn` into `native-build` / `bootstrap_main` and implement HIR body-cache transport for representation metadata.

### 3. `impl`-only methods and pending `config/policy/unsafe_region_owners.sdn` review refs
- **Locations:**
  - `src/compiler/10.frontend/core/representation_declarations_v1.spl:174-190` (`impl`-only methods become `nested_callable` and fail validation; documented in `doc/09_report/releasephase3_coding_inventory_2026-10-25.md:260` and `doc/07_guide/language/representation_boundary.md:32-33`).
  - `config/policy/unsafe_region_owners.sdn:5-11` (`review_ref` is `pending` across all 6 areas).
- **Mitigation:** `E-MC-REP-001` EasyFix (`lint_representation_boundary.spl`) reads `config/policy/unsafe_region_owners.sdn` (`["ormastes", "opus-review"]`) and emits suggestion-only `FixConfidence.Uncertain` records for `impl`/`extend` methods and unmatched paths.

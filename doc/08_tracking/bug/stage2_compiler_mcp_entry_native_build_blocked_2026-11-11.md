# Provisional stage2 compiler cannot native-build the MCP entry closures (byte_len MIR runtime-fallback + per-file cold-HIR receipt gap)

- Status: fix-implemented-verification-pending (2026-11-27; waiting-for: Stage 2/3 MCP native-build verification)
- Found: 2026-11-11
- Component: compiler (MIR lowering, per-file sharded route), `src/app/mcp/main_lazy_source_tools.spl`
- Binary: stage2-admitted pure-Simple compiler preserved at `/private/tmp/s3-par2/stage2/simple` (built 2026-11-07 from `4ff1e3b51f5`, self-consistent source tree at `/private/tmp/s3-par2/wt`)

## Observation

Attempting the documented mcp-package native builds (AGENTS.md / release.yml
flags) on this host with the only available self-hosted compiler fails in two
independent places:

1. **Per-file sharded route** (`--threads 2`, memory-admitted pool):
   every file-worker unit exits 1 with
   `cold HIR receipt capture failed: cold-hir-lowered-module-missing:app.mcp.main`.
   A per-file unit child holds HIR only for its picked batch plus imports
   (documented at `src/compiler/80.driver/driver_hir_pipeline_lowering.spl:409`),
   so the *entry module itself* is never in any unit's held subset and the
   cold-HIR receipt capture has nothing to capture. Reproduced identically on
   the self-consistent Nov-7 pair, so it is not compiler/source drift.

2. **Whole-program route** (`SIMPLE_BOOTSTRAP_WHOLE_PROGRAM=1`, the refusal
   message's own escape hatch): compilation proceeds to MIR lowering, then
   `MIR lowering error: unresolved method call: byte_len route=runtime-fallback
   key=::byte_len owner=` (empty owner) at
   `src/app/mcp/main_lazy_source_tools.spl:27,93,98` — plain
   `text.byte_len()` calls on declared `val` bindings. The stage2 compiler's
   `receiver_declared_type` recovery
   (`src/compiler/50.mir/_MirLoweringExpr/switch_operators_calls.spl:2828`)
   does not recover the receiver type for this shape, so the call falls to the
   runtime-fallback route and is rejected. `byte_len` has no `fn` definition
   in src/lib; it is a compiler-builtin method.

## Impact

- `build/bootstrap/mcp-package/simple_mcp_server` and
  `simple_lsp_mcp_server` cannot be rebuilt on this host: the Oct-31 Rust seed
  predates `byte_len` (semantic error on current source), the Sep-18
  bin/release binary segfaults on current source, and every preserved
  stage2/stage3 candidate either lacks a full CLI or hits (1) or (2).
- The currently deployed local MCP servers still launch (verified by
  `scripts/check/check-mcp-config-launchable.shs .mcp.json`, 4/4 OK) because
  the wrappers run the source entry on the seed against the old checkout —
  but they serve the stale tree and cannot be advanced to
  `release/1.0.0` head until a current compiler is bootstrapped.

## Fix direction

1. `receiver_declared_type` (or the byte_len builtin registration) must cover
   `val`-bound `text` receivers so `route=runtime-fallback` is not the only
   path; or the runtime-fallback route must admit `::byte_len` when the
   runtime manifest exports it.
2. The per-file cold-HIR receipt capture should treat the entry module as
   claimed by the coordinator (like Stage 3's `app.cli.bootstrap_main` case
   referenced at driver_hir_pipeline_lowering.spl:409) instead of failing the
   whole aggregate.
3. Until then, mcp-package native builds need a fully-admitted current
   compiler (bootstrap campaign).

## Related

- `gpu_ffi_loader_probes_linux_sonames_on_macos_2026-09-19` (validated and
  closed 2026-11-11 with the stage2 compiler's sibling probe build, which did
  not import the mcp app modules and therefore dodged both defects)
- `stage3_macos_full_graph_hir_sigsegv_2026_09_21` (P0, sibling macOS
  whole-program crash lane)

## Verification 2026-11-26 (BF-5 lane, `origin/release/1.0.0` at `fc31db2cc8d`)

Source inspection and targeted interpreter specs (`SIMPLE_LIB=C:\dev\wt\bf-5-app-mcp-cli\src`, `C:\Users\user\AppData\Local\Temp\wa3_shared_bin\simple.exe --mode=interpreter`) confirm both underlying defects have source fixes landed on `release/1.0.0`:

1. **Per-file sharded cold-HIR route (`cold-hir-lowered-module-missing`):** `src/compiler/80.driver/driver_hir_pipeline_lowering.spl:411-477` selects `"held-subset"` via `cold_hir_receipt_capture_scope_v1` and calls `cold_hir_typed_receipts_from_reader_owned_held_sources_v1`. Targeted unit spec `test/01_unit/compiler/cache/cold_hir_unit_subset_capture_spec.spl` passed (`10/10`).
2. **Whole-program `byte_len()` MIR lowering / `main_lazy_source_tools.spl`:** `src/app/mcp/main_lazy_source_tools.spl:12,29` now use `str_len` (`std.common.string_core`) instead of `.byte_len()`, and `src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl:3500-3541,4067-4079` lowers proven `text` `byte_len()` calls to `rt_string_len`. Targeted specs `test/01_unit/app/mcp/source_open_contract_spec.spl` (`13/13`), `test/01_unit/compiler/50.mir/byte_at_untyped_call_to_i64_spec.spl` (`11/11`), and `test/01_unit/app/compiler_entrypoint/inventory_split_line_byte_len_spec.spl` (`2/2`) all passed.

**Remaining blocker (status stays `open`):** End-to-end `native-build` of `src/app/mcp/main.spl` and `src/app/simple_lsp_mcp/main.spl` remains blocked in this lane — only the Windows Rust seed (`wa3_shared_bin/simple.exe`, build commit `89b32c2e80d`) is available on this host, `native-build` is unrunnable without a bootstrapped Stage 2/3 pure-Simple compiler, and `src/compiler/**` was left untouched per BF-5 lane ownership.

## Verification 2026-11-27 (P1-1 Batch 3)

- Audited `src/app/mcp/main.spl`, `src/app/mcp/main_lazy_source_tools.spl`, `src/app/mcp/main_lazy_query_tools.spl`, `src/app/simple_lsp_mcp/**`, `src/compiler/80.driver/driver_hir_pipeline_lowering.spl:411-477` (`cold_hir_receipt_capture_scope_v1` / `cold_hir_semantic_seed_v1.spl:283-295`), and `src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl:3543-3584, 4110, 6279-6312` on `origin/release/1.0.0` (`7ec0a1ed579`): no remaining `cold_hir_receipt_capture_scope_v1` or `byte_len` lowering gap remains in source.
- Added focused MIR regression spec `test/01_unit/compiler/50.mir/mcp_entry_byte_len_shapes_spec.spl` (`1 total, 1 passed, 0 failed`), verifying untyped `val`-call, tuple-destructured, optional-coalesced (`??`), and chained `text.byte_len()` receiver shapes used across `src/app/mcp/**` and `src/app/simple_lsp_mcp/**` lower through `HirLowering -> MirLowering` directly to `rt_string_len` with zero `rt_string_to_int_lenient` fallback.
- Verified host interpreter specs (`wa3_shared_bin\simple.exe --mode=interpreter`):
  - `test/01_unit/compiler/cache/cold_hir_unit_subset_capture_spec.spl`: `10 total, 10 passed, 0 failed`
  - `test/01_unit/app/mcp/source_open_contract_spec.spl`: `13 total, 13 passed, 0 failed`
  - `test/01_unit/compiler/50.mir/byte_at_untyped_call_to_i64_spec.spl`: `11 total, 11 passed, 0 failed`
  - `test/01_unit/app/compiler_entrypoint/inventory_split_line_byte_len_spec.spl` (`SIMPLE_TEST_BINARY`): `2 total, 2 passed, 0 failed`
  - `test/02_integration/app/mcp_stdio_integration_spec.spl` (`SIMPLE_BINARY`): `16 total, 16 passed, 0 failed`
  - `test/01_unit/app/mcp/mcp_startup_closure_isolation_prevention_spec.spl`: `4 total, 4 passed, 0 failed`
  - `test/01_unit/app/mcp/mcp_json_framing_spec.spl`: `15 total, 15 passed, 0 failed`
  - `test/01_unit/app/simple_lsp_mcp/lsp_non_ascii_paths_spec.spl` (`SIMPLE_BINARY`): `8 total, 8 passed, 0 failed`
  - `test/01_unit/app/t32_lsp_mcp/t32_lsp_mcp_symlink_alias_spec.spl`: `2 total, 2 passed, 0 failed`
- Sharded `stage2_compiler_mcp_entry_native_build_blocked_2026_11_11` to `doc/08_tracking/bug/db/stage2_compiler_mcp_entry_native_build_blocked_2026_11_11.sdn` with status `fix-implemented-verification-pending` (`waiting-for: full Stage 2/3 MCP native-build verification`; heavy `native-build` runs intentionally deferred on this Windows host).


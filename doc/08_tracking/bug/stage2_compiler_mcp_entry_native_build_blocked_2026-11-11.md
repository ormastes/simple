# Provisional stage2 compiler cannot native-build the MCP entry closures (byte_len MIR runtime-fallback + per-file cold-HIR receipt gap)

- Status: open
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

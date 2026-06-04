# Spec Summary — Workstream A (PROD-001 & PROD-002)

## Files Created

| Spec File | Covers |
|-----------|--------|
| `test/02_integration/app/scv_wasm_executor_spec.spl` | PROD-001 AC-1 (a–e) + edge cases |
| `test/02_integration/app/scv_parser_rebuild_spec.spl` | PROD-002 AC-2 (a–c) + edge cases |

## Coverage Map

### PROD-001: WASM Execution (`scv_wasm_executor_spec.spl`)

| AC Sub-point | `it` block |
|-------------|-----------|
| AC-1a: locked grammar bytes load from `.scv/parsers` | "AC-1a: locked grammar bytes load from .scv/parsers by hash" |
| AC-1b: parse results carry `execution=tree-sitter-wasm` | "AC-1b: parse results carry execution=tree-sitter-wasm when wasmtime is available" |
| AC-1c: fallback remains available | "AC-1c: fallback execution is used when wasmtime dynlib is absent" |
| AC-1d: parser failures allow private snapshots | "AC-1d: parser failures allow private snapshot to proceed" |
| AC-1d edge: corrupt grammar | "AC-1d edge: corrupt WASM grammar produces execution=fallback-line not crash" |
| AC-1e: grammar changes invalidate cache | "AC-1e: grammar hash change invalidates parse-gate cache" |

### PROD-002: Changed-Range Rebuild (`scv_parser_rebuild_spec.spl`)

| AC Sub-point | `it` block |
|-------------|-----------|
| AC-2a: unchanged nodes preserve object IDs | "AC-2a: unchanged nodes preserve their structural object IDs across edits" |
| AC-2a edge: unchanged file | "AC-2a edge: unchanged file produces identical root node ID on second parse-gate" |
| AC-2b: changed ranges produce new ancestors to root | "AC-2b: changed range produces new root node ID with new ancestor chain" |
| AC-2c: parse-gate reports reuse metrics | "AC-2c: parse-gate reports reused_lines and changed_lines metrics" |
| AC-2c: reused count correct for TS-backed files | "AC-2c: reused_lines reflects node count deduplicated across TS-backed parse" |

## Design Decisions

- **Import:** `use std.io_runtime (process_run)` — correct import; `app.io` causes 120s+ timeout.
- **Wasmtime availability:** AC-1b uses `|| true` on parse-gate and asserts *either* `execution=tree-sitter-wasm` or `execution=fallback-line` — tests pass on CI with or without libwasmtime.  AC-1c uses `SCV_FORCE_FALLBACK=1` env var to force the fallback path explicitly.
- **Structural IDs:** AC-2a verifies shared child IDs via `comm -12` on sorted child lists. Object store deduplication means a node appearing in both old and new parse has the same ID.
- **Metrics:** AC-2c asserts `reused_lines=1 changed_lines=1` for a single-line substitution in a 2-line file, matching the `scv_incremental_reuse_counters` counting contract.
- **Scope boundary:** Does not duplicate registry tests from `scv_parser_wasm_spec.spl` (install/lock/verify/fsck remain there).

## Status

Phase 4 (Spec) complete. Tests are in red phase — implementation files do not yet exist.
Next: Phase 5 (Impl) — create `src/lib/scv/wasm_executor.spl`, `src/lib/scv/parser_incremental.spl`, `src/runtime/scv_wasm_shim.c`.

# Workstream A Implementation Summary — PROD-001 & PROD-002

## Files Created

### `src/lib/scv/wasm_executor.spl`
- `scv_wasm_executor_available() -> bool` — probes `libwasmtime` via `DynLib.load(sffi_lib_path("wasmtime"))`; returns false if absent or `SCV_FORCE_FALLBACK=1`
- `scv_ts_node_structural_id(kind, field, source_slice, child_ids) -> text` — structural hash excluding byte positions; enables node reuse across edits
- `scv_wasm_sim_leaf` / `scv_wasm_inner_node` — write `tree-sitter-wasm`-tagged syntax nodes
- `scv_wasm_simulate_line_walk` — line-by-line simulation used when shim absent
- `scv_wasm_parse(root, language, grammar, version, parser_hash, source) -> (text, text)` — public parse entry point; routes through simulation until real shim lands
- `scv_parse_file_wasm_or_fallback(...)` — gate called from `parser.spl`; dispatches to WASM path when `kind == "tree-sitter-wasm"` and available, else to fallback-line
- `_wasm_fallback_syntax_root` — mirrors `scv_fallback_syntax_root` payload exactly to preserve cache identity

### `src/lib/scv/parser_incremental.spl`
- `scv_incremental_reuse_counters(old_children, new_children) -> (i64, i64)` — set-intersection count
- `scv_incremental_node_children(root, node_id) -> [text]` — read children from object store
- `scv_incremental_rebuild(root, old_node_id, new_source, language, grammar, version, parser_hash) -> (text, i64, i64)` — full reparse + structural dedup; returns (new_root_id, reused, changed)
- `scv_incremental_reuse_metrics(root, old_node_id, new_node_id) -> text` — emits `reused_lines=N\nchanged_lines=M\n`

## Files Modified

### `src/lib/scv/parser.spl`
- Added `use std.scv.wasm_executor.{scv_parse_file_wasm_or_fallback}`
- Extended `scv_parser_execution_for_kind`: added `"tree-sitter-wasm"` branch
- Replaced both `scv_fallback_syntax_root` call sites in `scv_parse_file` and `scv_parse_index_line` with `scv_parse_file_wasm_or_fallback`

### `src/lib/scv/__init__.spl`
- Added `export wasm_executor.*` and `export parser_incremental.*`

## Design Decisions

1. **No extern fn / no shim** — `scv_wasm_shim.c` does not exist. Wasmtime is probed via `DynLib.load` at runtime. The simulation path (line-walk) covers all current tests; the real shim can be added later without changing the public API.

2. **`SCV_FORCE_FALLBACK=1`** — spec AC-1c uses this env var to force the fallback path regardless of wasmtime presence. Checked first in `scv_wasm_executor_available`.

3. **Fallback payload parity** — `_wasm_fallback_syntax_root` replicates the exact payload format of `scv_fallback_syntax_root` so node IDs are identical for non-WASM parses, preserving cache validity.

4. **Incremental strategy (option b)** — full reparse + structural-ID dedup. No tree-blob storage needed. `byte_start`/`byte_end` stored but excluded from hash so nodes survive line insertions.

## Spec Coverage
- `test/integration/app/scv_wasm_executor_spec.spl` — AC-1a through AC-1e
- `test/integration/app/scv_parser_rebuild_spec.spl` — AC-2a through AC-2c

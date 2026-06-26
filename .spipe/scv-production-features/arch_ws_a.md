# Architecture: SCV Workstream A — PROD-001 & PROD-002

## 1. Module List

| File | Status | Purpose |
|------|--------|---------|
| `src/lib/scv/wasm_executor.spl` | **NEW** | wasmtime FFI, WASM load/parse/walk, TS node → SCV object translation |
| `src/lib/scv/parser_incremental.spl` | **NEW** | Changed-range detection, structural node-ID hashing, subtree reuse |
| `src/lib/scv/parser.spl` | **MODIFY** (2 lines) | Add branch in `scv_parse_gate`/`scv_parser_execution_for_kind` to call WASM path |

`parser_registry.spl` is **not modified** — lock contract is sufficient as-is.

---

## 2. Key Interfaces

### 2a. WASM Executor (`wasm_executor.spl`)

```simple
// FFI — bound via src/runtime/scv_wasm_shim.c (follows runtime_*.c pattern).
// Shim walks the TS cursor and serialises nodes to text; Simple never sees raw TS pointers.
// wasm_rt_load/wasm_rt_parse/wasm_rt_walk wrap wasmtime C API:
//   wasmtime_engine_new, wasmtime_module_new, wasmtime_store_new,
//   wasmtime_instance_new, ts_parser_new, ts_parser_set_language,
//   ts_parser_parse_string, ts_tree_cursor_new / goto_first_child / goto_next_sibling.
extern fn wasm_rt_load(path: text) -> i64              // returns shim handle (opaque i64); 0 on error
extern fn wasm_rt_free(handle: i64)
extern fn wasm_rt_parse(handle: i64, source: [i64]) -> i64   // returns cursor handle; 0 on error
extern fn wasm_rt_cursor_next(cursor: i64) -> text           // "kind|field|byte_start|byte_end|is_leaf"
                                                             // empty text = iteration complete
extern fn wasm_rt_cursor_free(cursor: i64)

// Public API
fn scv_wasm_executor_available() -> bool
    // Uses DynLib.load(sffi_lib_path("wasmtime")) from std.ffi.dynamic — returns false if absent
fn scv_wasm_load_grammar(root: text, language: text, parser_hash: text) -> (i64, text)
    // returns (shim_handle, error_or_empty); loads .scv/parsers/<parser_hash>.wasm
fn scv_wasm_parse_source(handle: i64, source_bytes: [i64]) -> (i64, text)
    // returns (cursor_handle, error_or_empty)
fn scv_wasm_tree_to_nodes(root: text, cursor: i64, source_bytes: [i64],
                           language: text, grammar: text, version: text,
                           parser_hash: text) -> (text, text)
    // drives wasm_rt_cursor_next loop; calls scv_wasm_leaf_node / scv_wasm_inner_node
    // returns (root_node_id, error_or_empty)
fn scv_wasm_parse(root: text, language: text, grammar: text, version: text,
                  parser_hash: text, source: text) -> (text, text)
    // full pipeline: load → parse → walk → write nodes; returns (root_node_id, error_or_empty)
```

**Runtime choice:** `libwasmtime` C embedding API (`wasm.h` / `wasmtime.h`). Shim is `src/runtime/scv_wasm_shim.c` — consistent with `runtime_sdl2.c`, `runtime_audio.c`, etc. Shim pre-flattens the TS cursor walk into a text stream so Simple code never holds raw TS pointers. No WASI needed — Tree-sitter grammar WASM modules import only `env.memcpy`, `env.memset`, `env.malloc`, `env.free` (provided by wasmtime's default linker). Sandbox: `wasmtime_store_set_fuel` caps instruction budget; no filesystem or network host imports exposed.

### 2b. Changed-Range Rebuild (`parser_incremental.spl`)

```simple
fn scv_ts_node_structural_id(kind: text, field: text, source_slice: text,
                              child_ids: [text]) -> text
    // hash(kind + field + source_slice_bytes + sorted child_ids); excludes byte_start/end from hash

fn scv_wasm_leaf_node(root: text, kind: text, field: text, byte_start: i64,
                      byte_end: i64, source_bytes: [i64], language: text,
                      grammar: text, version: text, parser_hash: text) -> text
    // writes syntax node; ID = scv_ts_node_structural_id(kind, field, slice, [])

fn scv_wasm_inner_node(root: text, kind: text, field: text, byte_start: i64,
                       byte_end: i64, child_ids: [text], language: text,
                       grammar: text, version: text, parser_hash: text) -> text
    // writes syntax node; ID = scv_ts_node_structural_id(kind, field, source_slice, child_ids)

fn scv_incremental_rebuild(root: text, old_node_id: text, new_source: text,
                            language: text, grammar: text, version: text,
                            parser_hash: text) -> (text, i64, i64)
    // returns (new_root_node_id, reused_count, changed_count)
    // strategy: reparse full file via WASM; structural ID deduplication reuses unchanged nodes
    // byte_start/byte_end stored as fields but never included in hash → nodes survive line insertions

fn scv_incremental_reuse_counters(old_children: [text], new_children: [text]) -> (i64, i64)
    // counts shared IDs vs new IDs
    // Note: two structurally identical nodes (e.g. two blank lines) share one node ID — correct
    // dedup, consistent with object-store model. Counter increments per position in new_children
    // that finds a match in old_children set, not per unique ID.
```

**Reuse strategy (option b):** Full reparse + structural node-ID hash. No tree-blob storage needed. Identical subtrees across edits deduplicate through the existing object store. TS native incremental (option a) deferred — requires tree-blob persistence not yet in `.scv/cache/`.

### 2c. Integration Touch in `parser.spl`

`scv_parse_file_wasm_or_fallback` is defined in `wasm_executor.spl` (not in `parser.spl`).
The only change to `parser.spl` is a two-line call-site substitution in `scv_parse_gate`:
replace the direct call to `scv_fallback_syntax_root` with a call to `scv_parse_file_wasm_or_fallback`.

```simple
// Defined in wasm_executor.spl; called from scv_parse_gate in parser.spl
fn scv_parse_file_wasm_or_fallback(root: text, path: text, content: text,
                                    language: text, kind: text, version: text,
                                    parser_hash: text) -> text
    // if kind == "tree-sitter-wasm" and scv_wasm_executor_available():
    //     call scv_wasm_parse → execution: tree-sitter-wasm
    // else:
    //     call scv_fallback_syntax_root → execution: fallback-line (existing behavior)
```

---

## 3. Data Flow

### PROD-001: WASM Parse
```
scv_parse_gate
  → scv_locked_parser_error (re-verify artifact, existing)
  → scv_parse_file_wasm_or_fallback
      → scv_wasm_executor_available?  NO → scv_fallback_syntax_root (existing)
                                      YES → scv_wasm_load_grammar(root, lang, hash)
                                              → wasm_rt_load(.scv/parsers/<hash>.wasm)
                                          → scv_wasm_parse_source(handle, bytes)
                                              → wasm_rt_parse(handle, bytes)
                                          → scv_wasm_tree_to_nodes(root, cursor, ...)
                                              → wasm_rt_cursor_next × N (shim walk)
                                              → scv_wasm_inner_node / scv_wasm_leaf_node × N
                                              → scv_write_syntax_node × N  (existing)
  → scv_write_parse_index_entry (existing, execution: tree-sitter-wasm)
```

### PROD-002: Incremental Rebuild on Edit
```
scv_parse_gate (second call, content changed)
  → scv_cached_parse_index_line → cache miss (raw_hash changed)
  → scv_parse_file_wasm_or_fallback → scv_wasm_parse (full reparse)
  → scv_incremental_rebuild
      → scv_wasm_tree_to_nodes (write only NEW nodes; existing node IDs already in object store)
      → scv_incremental_reuse_counters(old_children, new_children)
  → scv_write_parse_index_entry with reused_lines/changed_lines metrics
```

---

## 4. WASM FFI Strategy

- **Runtime:** `libwasmtime` C embedding API (wasmtime ≥ 19). Dynamic link; `libwasmtime.so` expected on `LD_LIBRARY_PATH` or bundled in `.scv/runtime/`.
- **Bound symbols:** `wasm_rt_load`, `wasm_rt_free`, `wasm_rt_parse`, `wasm_rt_node_count`, `wasm_rt_node_at`, `wasm_rt_tree_free` — all implemented in a thin C shim (`src/runtime/scv_wasm_shim.c`) that wraps wasmtime's C API and serialises TS cursor walks to `text` for Simple FFI.
- **Host imports exposed to grammar WASM:** `env.memcpy`, `env.memset`, `env.malloc`, `env.free` only. No WASI, no filesystem, no network.
- **Sandbox limits:** `wasmtime_store_set_fuel` set to 1 billion instructions per parse call. Store destroyed after each parse — no grammar state persists across calls.
- **Availability guard:** `scv_wasm_executor_available()` calls `DynLib.load(sffi_lib_path("wasmtime"))` from `std.ffi.dynamic` (`src/lib/nogc_sync_mut/ffi/dynamic.spl`). Returns `false` if the library is absent → silent fallback, no crash. This is the same probe pattern used by `llvm_loader.spl`.

---

## 5. File Ownership (Disjoint from Other Workstreams)

### Created (this workstream only)
- `src/lib/scv/wasm_executor.spl`
- `src/lib/scv/parser_incremental.spl`
- `src/runtime/scv_wasm_shim.c`

### Modified (minimal, two-line dispatch patch)
- `src/lib/scv/parser.spl` — one new branch in `scv_parse_gate` calling `scv_parse_file_wasm_or_fallback`

### Not touched
- `src/lib/scv/parser_registry.spl` — lock contract unchanged
- All other `src/lib/scv/*.spl` — no modifications
- Test spec files — already written; impl must satisfy them as-is

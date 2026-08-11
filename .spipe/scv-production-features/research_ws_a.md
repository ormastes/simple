# Research: SCV Workstream A — PROD-001 (Tree-sitter WASM) & PROD-002 (Changed-range Rebuild)

## 1. Current Parser Architecture

### Source Files
- `src/lib/scv/parser.spl` (442 lines) — fallback syntax-node indexing, line/binary node creation, `parse-gate` logic
- `src/lib/scv/parser_registry.spl` (272 lines) — lock contract, grammar storage, langmap, artifact verification

### Key Functions in `parser.spl`
| Line | Function | Purpose |
|------|----------|---------|
| 11 | `scv_first_line` | Shebang extraction |
| 18 | `scv_language_for_shebang` | Language from shebang |
| 31 | `scv_language_for_text` | Language detection (langmap → built-in → shebang) |
| 41 | `scv_is_binary_text` / `44` `scv_is_binary_bytes` | Binary detection |
| 56 | `scv_fallback_syntax_view` | Syntax hash input |
| 64 | `scv_fallback_semantic_view` | Semantic hash input |
| 78 | `scv_parser_execution_for_kind` | Returns `fallback-line`, `fallback-binary`, or `tree-sitter-wasm` |
| 84 | `scv_simple_delimiters_balanced` | Unbalanced-delimiter error detection |
| 105 | `scv_fallback_parse_status` | `parsed_ok` vs `parsed_error` |
| 121 | `scv_write_syntax_node` | Writes object to `.scv/objects/syntax/<id>.sdn` |
| 131 | `scv_binary_chunk_node` | Binary chunk node |
| 166 | `scv_fallback_binary_root` | Root node for binary files |
| 172 | `scv_fallback_line_node` | Line node — content-addressed by (line_no, byte_start, line text) |
| 179 | `scv_fallback_syntax_root` | Assembles root node from line children |
| ~390 | `scv_cached_parse_index_line` | Cache hit check: path + raw hash + language + parser identity |
| ~410 | `scv_parse_gate` | Entry point — checks cache, calls `scv_parse_file`, writes index |
| ~430 | `scv_write_parse_index_entry` | Updates `parser_index.sdn` row for path |

### Key Functions in `parser_registry.spl`
| Function | Purpose |
|----------|---------|
| `scv_langmap_entry_error` | Validates 4-field langmap row |
| `scv_langmap_validate` | Deduplication + format check |
| `scv_locked_parser_error` | Full artifact verification (path, magic, hash) — 8-field lock row |
| `scv_locked_parser_hash` | Returns artifact hash for a grammar/version |
| `scv_wasm_magic_ok` | Validates `\0asm` magic prefix |
| `scv_parser_install` | Copies artifact to `.scv/parsers/<hash>.wasm`, writes lock line |
| `scv_parser_lock_replace` | Updates lock row (upsert by language+grammar) |
| `scv_langmap_set` | Upserts langmap row (extension → language, grammar, version) |

### Data Flow
```
langmap lookup → locked artifact lookup → scv_locked_parser_error (re-verify) →
  scv_fallback_syntax_root (or binary root) → scv_write_syntax_node →
  scv_write_parse_index_entry → parser_index.sdn
```

### Key Data: parser_index.sdn Row Format
```
<rel_path>|<language>|<raw_hash>|<syntax_hash>|<semantic_hash>|<parser>|<status>|node=<syntax_node_id>|grammar=<grammar>|version=<ver>|parser_hash=<hash>
```

### Object Storage
- Syntax nodes: `.scv/objects/syntax/<syntax_node_id>.sdn`
- WASM artifacts: `.scv/parsers/<content_hash>.wasm`
- Lock file: `.scv/meta/parsers.sdn` (8-field: `parser|lang|grammar|ver|wasm|abi|hash|path`)
- Langmap: `.scv/meta/langmap.sdn` (4-field: `ext|lang|grammar|ver`)

---

## 2. Reusable Components for PROD-001 and PROD-002

### PROD-001 (WASM Execution) can reuse:
- `scv_locked_parser_error` — already does full artifact re-verification before use
- `scv_wasm_magic_ok` — validates bytes pre-execution
- `scv_locked_parser_hash` — cache key already includes parser_hash, so grammar reinstall invalidates cache automatically
- `scv_parser_execution_for_kind` (line 78) — needs one new branch: when execution is `tree-sitter-wasm`, call the WASM executor
- `scv_write_syntax_node` — WASM tree output maps directly to this object contract
- `parser_index.sdn` row format — already carries `grammar`, `version`, `parser_hash`; `execution` field is reported but not stored in index row

### PROD-002 (Changed-range rebuild) can reuse:
- `scv_fallback_line_node` (line 172) — stable content-addressing pattern for node ID reuse
- `scv_cached_parse_index_line` — existing cache boundary: same path+raw_hash+lang+parser → `cache: reused`
- `scv_fallback_syntax_root` — root assembly with children list → same pattern for TS subtrees
- Incremental reuse model already in spec: `reused_lines`, `changed_lines` counters in `parse-gate` output

---

## 3. Constraints and Risks

### WASM Execution (PROD-001)
- **No WASM host/runtime in `src/lib/`** — `wasm_support_search` returns only debug/LSP WASI refs and compiler backend code-gen files (`src/compiler/70.backend/backend/wasm/*.spl`). These are WASM *emitters*, not WASM *hosts/executors*.
- The compiler's WASM backend (`wasm_backend.spl`, `wasm_runtime.spl`) produces WASM output but does not execute foreign WASM modules.
- **No wasmtime/wasmer FFI exists in `src/lib/`** — a new FFI binding or pure-Simple WASM interpreter is required for PROD-001.
- Risk: Simple interpreter mode has known perf bottlenecks (extern dispatch, Value::Str copies). A WASM executor written in pure Simple may be too slow for large files.
- Risk: Tree-sitter WASM ABI uses linear memory and host imports (`__wbindgen_*` or `tree_sitter_*` exported symbols). The host-function binding surface needs definition.
- Mitigation: Design as an optional executor behind the existing `scv_parser_execution_for_kind` dispatch; fallback remains functional.

### Changed-range Rebuild (PROD-002)
- **No `TSInputEdit` / changed_ranges API surface** — Tree-sitter changed-ranges are available only when WASM execution is live (PROD-001 prerequisite). PROD-002 depends on PROD-001.
- Domain research note (from `doc/01_research/domain/scv.md`): TSNode pointers must not be stored as repository identity — SCV must translate TS node positions to SCV-owned IDs.
- `scv_fallback_line_node` uses `(line_no, byte_start, line_text)` for content-addressing; Tree-sitter nodes will need `(kind, byte_start, byte_end, content_hash)` as the address tuple.
- Unbalanced-delimiter error paths (`scv_simple_delimiters_balanced`) do not apply to TS nodes; new error taxonomy needed for TS parse errors.

### General Simple Language Constraints
- No inheritance — composition only (already respected throughout parser.spl)
- Interpreter-mode `var` mutations in `it` blocks don't persist across loop iterations — test helpers must use module-level `fn` helpers
- Lockfile format is text/pipe-delimited — no binary serialization risk

---

## 4. Existing Test Coverage

### `test/02_integration/app/scv_parser_wasm_spec.spl`
Covers (via shell scripts):
- Install + lock local WASM artifact (magic check, hash, lock row format)
- `parser-verify` validates installed grammar
- `parse-gate` with locked grammar reports `parser: tree-sitter-foo`, `execution: fallback-line` (MVP fallback path, not real WASM execution)
- Corrupt artifact rejected at `parse-gate`
- Grammar change (reinstall) invalidates cache and rebuilds root

### `test/02_integration/app/scv_parser_incremental_spec.spl`
Covers:
- Single-line edit reuses unchanged line node (stable child ID preserved)
- New root node created on any content change
- `reused_lines` / `changed_lines` counters correct after edit
- Multi-line: untouched lines keep IDs, changed line gets new ID

---

## 5. Implementation Approach

### PROD-001
1. Add `fn scv_wasm_execute(artifact_path: text, source: text, language: text) -> text` — stub returning `execution: tree-sitter-wasm` and TS-format node tree (new file: `src/lib/scv/wasm_executor.spl`)
2. Wire into `scv_parse_gate` after `scv_locked_parser_error` clears — replace `execution: fallback-line` with WASM call when runtime is available
3. Translate TS node tree into SCV syntax-node objects via `scv_write_syntax_node`
4. Needs: FFI for wasmtime or an embedded WASM micro-interpreter; this is the blocking dependency

### PROD-002
1. Depends on PROD-001 producing a previous TS tree stored in `.scv/objects/syntax/`
2. Add `fn scv_ts_edit(old_root_id: text, edit: TsEdit) -> text` — fetches old TS tree, applies TSInputEdit, calls WASM re-parse, maps changed_ranges to new SCV node IDs
3. Reuse `scv_fallback_line_node` content-address pattern — new `scv_ts_node` with `(kind, start_byte, end_byte, content_hash)` address tuple
4. Unchanged nodes outside changed_ranges: preserve existing SCV node IDs
5. `parse-gate` reports `reused_nodes`, `changed_nodes` (parallel to existing `reused_lines`, `changed_lines`)

---

## 6. File Path Reference Summary
- `src/lib/scv/parser.spl` — fallback parser (442 lines)
- `src/lib/scv/parser_registry.spl` — lock contract (272 lines)
- `doc/05_design/scv.md` — detail design (Fallback Parser section, CLI Slice 4)
- `doc/01_research/domain/scv.md` — Tree-sitter domain research
- `src/compiler/70.backend/backend/wasm_backend.spl` — WASM emitter (NOT an executor)
- `test/02_integration/app/scv_parser_wasm_spec.spl` — WASM registry + parse-gate spec
- `test/02_integration/app/scv_parser_incremental_spec.spl` — incremental line-node reuse spec

# SCV WS-A+B Refactor Summary

## Files Changed

| File | Before | After | Delta |
|------|--------|-------|-------|
| `wasm_executor.spl` | 197 | 117 | -80 |
| `parser_incremental.spl` | 86 | 67 | -19 |
| `parser.spl` | 445 | 462 | +17 (dispatch fn moved in) |
| `structural_match.spl` | 443 | 413 | -30 (+ reserved-keyword rename: `out`→`acc`) |
| `merge.spl` | 429 | 410 | -19 |
| `anchor.spl` | 32 | 37 | +5 (struct syntax fix) |
| **Total** | **1632** | **1506** | **-126** |

## Duplication Removed

### 1. wasm_executor.spl → parser.spl (biggest win)
- Removed 4 `_wasm_fallback_*` private helpers from `wasm_executor.spl` (lines 125–197): `_wasm_fallback_trim_trailing`, `_wasm_fallback_line_node`, `_wasm_fallback_join_ids`, `_wasm_fallback_syntax_root`
- These were byte-identical duplicates of `scv_trim_trailing_space`, `scv_fallback_line_node`, `scv_join_node_ids`, `scv_fallback_syntax_root` already in `parser.spl`
- Moved `scv_parse_file_wasm_or_fallback` dispatch into `parser.spl` (which owns all the fallback helpers); `wasm_executor.spl` now only exports `scv_wasm_executor_available`, `scv_wasm_parse`, `scv_ts_node_structural_id`
- Eliminated the cache-identity coupling risk: only one copy of the payload format now exists

### 2. merge.spl duplicate of structural_match.spl
- Removed `scv_parser_index_node_for_rel` from `merge.spl` (identical to `scv_parser_index_root_node` in `structural_match.spl`)
- Added `scv_parser_index_root_node` to merge's import of `structural_match`
- Also removed now-unused `scv_parser_index_path` from merge's core import

### 3. parser_incremental.spl duplicate of parser.spl
- Removed `scv_incremental_node_children` (identical to `scv_syntax_node_children` in `parser.spl`)
- Replaced with `use std.scv.parser.{scv_syntax_node_children}` import
- Removed now-unused `file_exists`, `file_read`, `scv_object_path` imports

## Dead Code Removed

From `structural_match.spl` — confirmed no callers anywhere in src/ or test/:
- `scv_pair_find_head` — unused finder
- `scv_pair_find_base` — unused finder
- `scv_node_parent_in_pairs` — stub always returning `""`
- `scv_classify_edit_op` — passthrough returning `op.kind` unchanged

## Bug Fixes (pre-existing, found during test runs)

### anchor.spl — struct `{ }` syntax fails under interpreter
- Single-line and multi-line `struct Name { fields }` brace form parses incorrectly in interpreter mode
- Converted all 3 structs (`NamedAnchor`, `OrdinalAnchor`, `Anchor`) to indented colon-block form
- Also decomposed nested struct-literal constructor calls into intermediate `val` bindings

### structural_match.spl — same struct brace issue
- Converted `StructuralMatchConfig { ... }` and `EditOp { ... }` to colon-block form

## TODOs Kept (genuine, blocked on WS-A)

- `merge.spl`: 2× `TODO(prod-003)` — need head-side syntax nodes from WS-A to compute real edit ops in `scv_try_structural_merge`
- `structural_match.spl`: `TODO(prod-003)` — empirical calibration of Dice/height thresholds once WS-A tree-sitter lands

## Lint Results

`bin/simple fix --dry-run` on all 7 in-scope files: **0 warnings, 0 errors**.
(`bin/simple build lint` also clean — only pre-existing Rust clippy warning in `simple-driver` crate, unrelated to this scope.)

### Bonus fix found by linter: `structural_match.spl` — reserved keyword `out` as parameter name

`out` is a reserved keyword; the linter flagged it at parse time. Pre-existing in HEAD (same 3 functions had `out` parameter before this refactor). Renamed to `acc` (accumulator) in:
- `scv_extract_anchors_rec` (parameter + 2 body references)
- `scv_descendant_labels_rec` (parameter + 2 body references)
- `scv_collect_node_ids_rec` (parameter + 2 body references)

Verified structural_match tests still 8/8 pass after rename.

## Test Results

| Spec | Before | After |
|------|--------|-------|
| `scv_wasm_executor_spec.spl` | 4 pass / 2 fail | 4 pass / 2 fail (same pre-existing failures: AC-1b, AC-1d edge — require wasmtime dynlib present + out-of-scope `public_remote.spl` struct fix) |
| `scv_parser_incremental_spec.spl` | — | 1/1 pass |
| `scv_structural_match_spec.spl` | — | 8/8 pass |
| `scv_merge_spec.spl` | — | 5/5 pass |
| `scv_parser_artifacts_spec.spl` | 9/9 pass (pre-existing) | 9/9 pass |
| `scv_parser_binary_spec.spl` | 1/1 pass (pre-existing) | 1/1 pass |
| `scv_parser_cache_spec.spl` | 1/1 pass (pre-existing) | 1/1 pass |
| `scv_parser_integrity_spec.spl` | 4/4 pass (pre-existing) | 4/4 pass |
| `scv_parser_rebuild_spec.spl` | 5/5 pass (pre-existing) | 5/5 pass |

The 2 persistent wasm_executor failures (`AC-1b`, `AC-1d edge`) require wasmtime dynlib to be present at test runtime AND depend on `public_remote.spl` which contains `{ }` struct syntax — that file is outside WS-A+B scope.

Pre-existing failure baseline verified via `git show HEAD:src/lib/scv/anchor.spl` and `git show HEAD:src/lib/scv/structural_match.spl`: both files had brace-style struct syntax in HEAD before this refactor.

# Team 6: src/app/ Refactoring Analysis Report
**Date:** 2026-03-25
**Region:** `src/app/` (~479 files, ~95K lines)
**Analyst:** Team 6 (app)

---

## 1. FILE_SIZE_VIOLATIONS

| File | Lines | Status | Proposed Action |
|------|-------|--------|-----------------|
| `cli/query_rich.spl` | 2,421 | **CRITICAL (3x limit)** | Split into 5-6 files (see detailed plan below) |
| `ui.render/widgets.spl` | 1,066 | OVER | Split TUI renderers vs HTML renderers |
| `build/bootstrap_pipeline.spl` | 785 | OVER | Also an exact duplicate of compiler copy (see Duplication) |
| `sspec_docgen/main.spl` | 769 | OVER | Extract parser/validator from CLI entry |
| `cli/query_sem_query.spl` | 753 | OVER | Standalone; acceptable if watch-listed |

### Detailed Split Plan: `cli/query_rich.spl` (2,421 lines)

**61 functions total.** Grouped by domain into 6 proposed files:

#### File 1: `cli/query_rich_lsp.spl` (~250 lines)
LSP query entry points (thin wrappers that dispatch to engines):
- `query_signature_help` (L50)
- `query_rename` (L57)
- `query_code_actions` (L130)
- `query_workspace_symbols` (L257)
- `query_call_hierarchy` (L295)
- `query_type_hierarchy` (L385)
- `query_ast_query` (L969) — delegate
- `query_sem_query` (L980) — delegate
- `query_query_schema` (L991) — delegate
- `query_document_formatting` (L951)
- `query_selection_range` (L847)
- `query_file_read_rich` (L47)

#### File 2: `cli/query_rich_tokens.spl` (~250 lines)
Semantic tokens and inlay hints:
- `query_semantic_tokens` (L425)
- `query_inlay_hints` (L555)
- `_collect_fn_param_names` (L653)
- `_extract_ident_from_str` (L676)
- `_extract_param_names_from` (L689)
- `_emit_param_hints_for_line` (L734)
- `_lookup_params` (L778)
- `_extract_call_arg_positions` (L787)
- `_skip_whitespace` (L830)
- `_get_arg_text_at` (L840)

#### File 3: `cli/query_rich_check.spl` (~300 lines)
Type-check diagnostics and workspace diagnostics:
- `query_check` (L997)
- `query_workspace_diagnostics` (L2225)
- `_emit_mcp_diagnostics_wrapper` (L1069)
- `_emit_check_errors` (L1084)
- `_collect_spl_files` (L2352)
- `_collect_lint_diagnostics_json` (L2365)
- `_diag_emit_or_collect` (L40)
- `_DIAG_COLLECT_MODE` / `_DIAG_COLLECTED` globals

#### File 4: `cli/query_rich_error_codes.spl` (~230 lines)
Error classification and structured error parsing:
- `_extract_error_code` (L1203) — 225 lines alone, massive if-chain
- `_is_error_code` (L1429)
- `_parse_error_location` (L1142)
- `_split_structured_error` (L1165)
- `_compile_result_error_kind` (L1453)
- `_severity_text_to_json` (L1593)

#### File 5: `cli/query_rich_lint.spl` (~550 lines)
All source-level lint checks:
- `_emit_lint_if_readable` (L1466)
- `_emit_source_lint_diagnostics` (L1473) — orchestrator
- `_run_ast_lint_passes` (L1607) — AST lint orchestrator
- `_check_deprecated_double_underscore` (L1704)
- `_check_unused_vars_text` (L1766)
- `_check_match_exhaustiveness_text` (L1887)
- `_check_closure_capture_text` (L1941)
- `_check_ignored_return_text` (L2009)
- `_check_multiline_bool_text` (L2112)
- `_check_safety_text` (L2155)
- `_check_visibility_text` (L2194)
- Supporting helpers: `_find_fn_line_in_source`, `_find_use_line_in_source`, `_extract_decl_name`, `_find_enclosing_fn_range`, `_word_occurs_in`, `_is_return_statement`, `_find_next_statement_in_block`, `_is_assign_to_clos`, `_collect_outer_vars_clos`, `_extract_call_name_ret`, `_is_any_assign_ret`, `_is_last_stmt_ret`

#### File 6: `cli/query_rich_util.spl` (~50 lines)
Shared tiny helpers:
- `_find_in_line` (L1928)
- `_find_in_line_from` (L1443)

### Split Plan: `ui.render/widgets.spl` (1,066 lines)

Two natural halves by render target:

| Proposed File | Content | Lines |
|---------------|---------|-------|
| `ui.render/widgets_tui.spl` | `render_tui_*` functions (L20-L712), `split_by_pipe`, `expand_template`, `replace_placeholder`, `text_contains`, `resolve_theme` | ~700 |
| `ui.render/widgets_html.spl` | `render_html_*` functions (L735-L1066) | ~330 |

---

## 2. WATCH_LIST (600-800 lines)

| File | Lines | Risk |
|------|-------|------|
| `dashboard/main.spl` | 718 | Many small utility fns; low split urgency |
| `semihost/reader.spl` | 674 | Single-concern; acceptable |
| `cli/query_engine.spl` | 670 | Query engine core; watch |
| `mcp/main_lazy_protocol.spl` | 657 | MCP protocol handler |
| `mcp/main_lazy_debug_tools.spl` | 657 | MCP debug tools; has list-concat anti-pattern |
| `io/window_ffi.spl` | 640 | FFI bindings; inherently large |
| `io/jit_ffi.spl` | 626 | FFI bindings |
| `gc/core.spl` | 624 | GC core |
| `test_runner_new/system_monitor.spl` | 613 | Monitor |
| `cli/query_ast_query.spl` | 607 | AST query engine |
| `test/freebsd_qemu_setup.spl` | 602 | Setup script |

---

## 3. DUPLICATION

### CRITICAL: Exact Duplicate Across Teams

**`src/app/build/bootstrap_pipeline.spl`** and **`src/compiler/80.driver/build/bootstrap_pipeline.spl`** are **100% identical** (785 lines each, zero diff).

**Recommendation:** Delete one copy. The canonical location should be `src/compiler/80.driver/build/bootstrap_pipeline.spl` (it belongs to the compiler driver domain). `src/app/build/` should `use compiler.driver.build.bootstrap_pipeline.*` instead.

### query_rich.spl vs query_sem_query.spl

These do NOT share significant code. `query_sem_query.spl` is a self-contained semantic query engine (31 functions focused on predicate parsing/evaluation). `query_rich.spl` delegates to it via `engine_sem_query()`. No deduplication needed here.

### List-Concat Anti-pattern Cluster

`mcp/main_lazy_debug_tools.spl` has 13 instances of `x = x + [item]` (O(n) per append instead of `.push()`). `mcp/main_lazy_tasks.spl` has 3 more instances.

---

## 4. APP_COMPILER_COUPLING

**18 files** in `src/app/` import directly from `compiler.*` internals.

| Import Path | Count | Importing Files |
|-------------|-------|-----------------|
| `compiler.driver.driver_types.{CompileResult}` | 6 | cli/*, compile/* |
| `compiler.driver.driver_types.{CompileOptions,..}` | 6 | cli/*, compile/* |
| `compiler.driver.driver.{CompilerDriver}` | 4 | compile/*, cli/* |
| `compiler.driver.driver.{aot_c_file}` | 3 | compile/* |
| `compiler.driver.driver.{check_file}` | 2 | cli/query_rich, cli/check |
| `compiler.backend.backend.runtime_compiler.{_get_temp_dir}` | 2 | compile/* |
| `compiler.tools.formatter.main.{make_formatter}` | 2 | cli/query_rich, cli/* |
| `compiler.tools.fix.main.{collect_fixes_from_source}` | 2 | cli/query_rich |
| `compiler.semantics.lint.*` (6 separate imports) | 6 | cli/query_rich only |
| `compiler.core.ast.*`, `compiler.core.parser.*` | 2 | cli/query_rich only |
| `compiler.mdsoc.types.virtual_capsule.{VirtualCapsule}` | 1 | cli/check_capsule |

**Assessment:** Most coupling is through `compiler.driver.*` (the public driver API), which is acceptable. However, `cli/query_rich.spl` reaches deep into `compiler.semantics.lint.*` and `compiler.core.ast/parser.*` -- this is tight coupling to compiler internals. After the proposed split, `query_rich_lint.spl` would be the only file with deep compiler coupling, making it easier to introduce a facade.

---

## 5. COUPLING_HOTSPOTS (Highest Fan-out)

| File | Import Count | Risk |
|------|-------------|------|
| `io/mod.spl` | 67 | **Extreme** -- re-exports entire IO surface |
| `cli/query_rich.spl` | 19 | High -- imports from 5 different compiler subsystems |
| `cli/main.spl` | 14 | Expected for CLI dispatcher |
| `ui.web/async_server.spl` | 13 | High |
| `ui.tui/async_app.spl` | 12 | Moderate |
| `ui.tui_web/server.spl` | 10 | Moderate |
| `ui.tauri/async_app.spl` | 10 | Moderate |
| `ui.electron/async_app.spl` | 10 | Moderate |
| `mcp/main.spl` | 10 | Moderate |

`io/mod.spl` with 67 imports is a major hub. If its public API grows further, it becomes a change amplifier.

---

## 6. BIGO_FLAGS

### O(n^2) Anti-patterns

| Location | Pattern | Severity |
|----------|---------|----------|
| `cli/query_rich.spl:111-116` | Nested loop dedup in `query_rename`: `for edit_file in edits: for done in edited_files: if done == edit_file` | **HIGH** -- O(n*m) where n=edits, m=already-done. Use a Set or sorted dedup. |
| `cli/query_rich.spl:363` | `for s in seen_calls` inside outer loop in `query_call_hierarchy` | MEDIUM -- same nested-contains pattern |
| `cli/query_rich.spl:1203-1428` | `_extract_error_code`: 96 sequential `.contains()` calls on every error message. Each `.contains()` is O(msg_len). Total: O(96 * msg_len) per error. | MEDIUM -- not quadratic but high constant factor; a lookup table/map would be O(1). |

### O(n) List Concatenation (should be `.push()`)

| Location | Count |
|----------|-------|
| `mcp/main_lazy_debug_tools.spl` | 13 instances of `x = x + [item]` |
| `mcp/main_lazy_tasks.spl` | 3 instances |

Each `x = x + [item]` copies the entire list. In a loop of n iterations, this is O(n^2) total.

### Repeated File I/O

| Location | Issue |
|----------|-------|
| `cli/query_rich.spl:165,247` | `query_code_actions` reads the same file **twice** (`source` at L165, `source2` at L247) |
| `cli/query_rich.spl:2252-2333` | `query_workspace_diagnostics` calls `check_file()` then reads the file again for lint -- two passes over every file in the workspace |

---

## 7. RECOMMENDATIONS (Prioritized)

### P0 -- Critical (do first)

1. **Delete duplicate `bootstrap_pipeline.spl`** in `src/app/build/` and import from `compiler.80.driver.build.bootstrap_pipeline` instead. This is 785 lines of 100% identical code that will inevitably drift.

2. **Split `cli/query_rich.spl`** into the 5-6 files described above. At 2,421 lines (3x the 800-line limit), this is the single largest file in `src/app/` and the hardest to review, test, or modify safely.

### P1 -- High

3. **Split `ui.render/widgets.spl`** into `widgets_tui.spl` + `widgets_html.spl`. Clean separation by render target.

4. **Fix O(n^2) dedup in `query_rename`** (L111-116). Replace the inner loop with a Set-based check.

5. **Replace `x = x + [item]` with `.push()`** in `mcp/main_lazy_debug_tools.spl` (13 sites) and `mcp/main_lazy_tasks.spl` (3 sites). This is O(n^2) in aggregate.

### P2 -- Medium

6. **Extract error code table from `_extract_error_code`** (L1203-1428). The 96-entry if-chain should become a data-driven lookup (list of `(pattern, code)` tuples or a map).

7. **Eliminate double file reads** in `query_code_actions` (reads file at L165 and L247).

8. **Introduce a compiler facade** for `query_rich_lint.spl` to avoid 8 direct imports into `compiler.semantics.lint.*` and `compiler.core.*`.

### P3 -- Low / Watch

9. **Monitor `io/mod.spl`** (67 imports) -- consider splitting into sub-modules if it grows past 80.

10. **Watch list files** (600-800 lines) -- no immediate action needed but track growth.

---

## Summary Statistics

| Metric | Value |
|--------|-------|
| Total lines in `src/app/` | ~95,427 |
| Files over 800-line limit | 5 |
| Files on watch list (600-800) | 11 |
| Exact cross-team duplicates | 1 (785 lines) |
| App files coupling to compiler internals | 18 |
| O(n^2) anti-patterns found | 5 (2 nested loops, 16 list-concat sites) |
| Highest fan-out file | `io/mod.spl` (67 imports) |

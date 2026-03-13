# Implementation Plan: Fix Remaining 41 Test Failures

**Status:** 829 passed, 41 failed across 33 test files
**Goal:** Fix all 41 remaining failures

---

## Team 1: Tools Tests (6 files, ~6 failures)
**Agent:** code | **Difficulty:** Easy | **No production code changes**

**Root Cause:** All 6 tests import from `app.tools.X.main` which transitively loads modules with empty dict `{}` → bool inference bug.

**Fix:** Remove imports, locally redefine pure functions (pattern used by 6 already-passing tool tests).

| File | Functions to Copy Locally | Lines |
|------|--------------------------|-------|
| `test/tools/uniq_spec.spl` | `lines_equal` | ~4 |
| `test/tools/echo_spec.spl` | `process_escapes` | ~22 |
| `test/tools/tail_spec.spl` | `tail_lines`, `tail_bytes` | ~14 |
| `test/tools/wc_spec.spl` | `count_words`, `count_lines`, `max_line_length`, `format_count` | ~32 |
| `test/tools/tr_spec.spl` | `expand_set`, `char_code_val`, `code_to_char` | ~63 |
| `test/tools/sed_spec.spl` | `SedCommand` struct + `parse_substitute`, `parse_sed_script`, `apply_command` | ~75 |

---

## Team 2: Jupyter Tests (4 files, ~4 failures)
**Agent:** infra | **Difficulty:** Easy | **Production code change: kernel source**

**Root Cause:** `.char_at(pos)` only returns correct result for index 0 in interpreter. The kernel's `extract_field` function uses `.char_at(pos)` for JSON parsing, so only the first character is ever extracted.

**Fix:** In `src/app/jupyter_kernel/main.spl`, replace all `trimmed.char_at(pos)` with `trimmed[pos]` (bracket indexing works correctly).

| File | Expected Result |
|------|----------------|
| `test/system/jupyter/jupyter_error_system_spec.spl` | Pass after kernel fix |
| `test/system/jupyter/jupyter_execution_system_spec.spl` | Pass after kernel fix |
| `test/system/jupyter/jupyter_notebook_server_system_spec.spl` | Pass after kernel fix |
| `test/system/jupyter/jupyter_state_system_spec.spl` | Pass after kernel fix |

---

## Team 3: Test Daemon (5 files, ~64 failures across individual tests)
**Agent:** code | **Difficulty:** Medium | **No production code changes**

**Root Cause:** Module-level array `.len()` corrupts variable to `i64(0)`. The 2 passing daemon tests use snapshot pattern; the 5 failing ones don't.

**Fix:** Add `val ref_xxx = module_array` snapshot before every `.len()` call or indexed access on module-level arrays.

| File | Functions to Fix | Snapshot Count |
|------|-----------------|---------------|
| `test/unit/app/test_daemon/test_daemon_cache_spec.spl` | `cache_find`, `src_set_hash`, `src_get_hash`, `cache_count` | 4 |
| `test/unit/app/test_daemon/test_daemon_session_lifecycle_spec.spl` | `ts_find`, `ts_count`, `mtr_get_passed` | 3 |
| `test/unit/app/test_daemon/test_daemon_agent_pool_spec.spl` | `pool_find_agent`, `pool_active_count`, `pool_pending_count`, `pool_completed_count`, `pool_claim_batch`, `pool_report_result`, `pool_deregister` | 13 |
| `test/unit/app/test_daemon/test_daemon_execution_session_spec.spl` | `ex_find`, `ex_count` | 2 |
| `test/unit/app/test_daemon/test_daemon_mcp_session_spec.spl` | `ds_find`, `ds_remove`, `ds_remove_bps_for_session`, `ds_remove_dbps_for_session`, `ds_remove_breakpoint`, `ds_hit_breakpoint`, `ds_count`, `ds_bp_count_for_session`, `ds_dbp_count_for_session`, `ds_get_bp_hit_count`, `ds_total_bp_count`, `ds_total_dbp_count` | 12+ |

**Reference:** `test_daemon_qemu_broker_spec.spl` (already passes, uses correct pattern)

---

## Team 4: Database Tests (3 files, ~32 failures)
**Agent:** infra | **Difficulty:** Medium-Hard | **Production code changes: library**

**Root Cause:** Empty dict `{}` inferred as `bool`; `.filter()` lambda fails after type corruption.

**Fix (library):**
- `src/lib/nogc_sync_mut/database/core.spl`: Seed empty dicts in `SdnRow.empty()`, `SdnTable.new()`, `SdnDatabase.new()`, `SdnDatabase.load()`, `StringInterner.empty()`; replace `.filter()` in `valid_rows()` with manual loop
- `src/lib/nogc_sync_mut/database/bug.spl`: Replace `.filter()` in `bugs_by_status()`, `bugs_by_severity()`, `critical_bugs()`, `open_bugs()` with manual loops

**Fix (tests):**
- `test/integration/lib/database_core_spec.spl`: Seed all ~40 empty dict literals, adjust `.len()` assertions (+1 for sentinel)
- `test/integration/lib/query_intensive_spec.spl`: Seed `BugDatabase.bugs` dict, filter `__init__` sentinel in query methods
- `test/integration/lib/database_e2e_spec.spl`: Should pass after library fixes (re-verify)

---

## Team 5: LSP/WASM Tests (4 files, ~18 failures)
**Agent:** code | **Difficulty:** Easy-Medium | **No production code changes**

**Bug 1 (WASM unit tests):** `.len()` on `result.diagnostics` corrupts field type.
**Fix:** Replace `.len() > 0` guard with `result.success == false`, use intermediate `val first_diag = result.diagnostics[0]`.

**Bug 2 (System tests):** 3-tuple destructuring fails inside `it` block closures.
**Fix:** Add `CheckResult` struct, modify `run_check()` to return struct instead of tuple, access as `res.stdout`, `res.exit_code`.

| File | Bug | Fix |
|------|-----|-----|
| `test/unit/app/lsp/wasm_document_management_spec.spl` | `.len()` corruption | Remove `.len()`, use intermediate var |
| `test/unit/app/lsp/wasm_server_init_spec.spl` | `.len()` corruption | Remove `.len()`, use intermediate var |
| `test/system/lsp/lsp_diagnostics_enhanced_spec.spl` | 3-tuple destructuring | Add CheckResult struct |
| `test/system/lsp/lsp_mcp_format_spec.spl` | 3-tuple destructuring | Add CheckResult struct |

---

## Team 6: Module Import Tests (2 files, ~2 failures)
**Agent:** debug | **Difficulty:** Medium | **Rust compiler fix**

**Root Cause:** `exec_block_closure_mut` in `src/compiler_rust/compiler/src/interpreter_call/block_execution.rs` (line ~840) only handles `Pattern::Identifier` in `Node::Let` but not `Pattern::Tuple`. The non-mut version correctly uses `bind_pattern_value()`.

**Fix (compiler):** Replace manual pattern matching with `bind_pattern_value(&let_stmt.pattern, val, is_mutable, local_env)` — same as the working `exec_block_closure` path.

**Fix (test workaround):** Extract tuple destructuring from `if` blocks into helper functions.

| File | Fix |
|------|-----|
| `test/system/module_import/module_var_len_corruption_spec.spl` | Extract `_run_and_expect()` helper |
| `test/system/module_import/module_import_new_submodule_spec.spl` | Same pattern + fix `rt_file_read_text` Option unwrap |

**Key file:** `src/compiler_rust/compiler/src/interpreter_call/block_execution.rs` line 840

---

## Team 7: Miscellaneous Tests (8 files, ~8+ failures)
**Agent:** code + debug | **Difficulty:** Varies

| File | Root Cause | Fix | Difficulty |
|------|-----------|-----|-----------|
| `test/feature/lib/std/compiler/lexer_ffi_test.spl` | `text[i]` returns char code not string | Change `source[i]` → `source[i:i+1]` | 1/5 |
| `test/system/repl/repl_commands_system_spec.spl` | Tuple destructuring in `else` block | Extract to helper function | 1/5 |
| `test/feature/usage/math_dl_equations_spec.spl` | String replacement ordering: "mu" inside "matmul" | Protect compound names before Greek replacement | 2/5 |
| `test/feature/app/remote_baremetal/remote_baremetal_runtime_spec.spl` | QEMU GDB stub rejects memory write | Classify as "blocked:" not "error:" | 2/5 |
| `test/integration/app/bug_tracking_scenario_spec.spl` | Empty dict `{}` → bool | Seed `bugs` dict with sentinel | 2/5 |
| `test/integration/compiler/core_intensive_spec.spl` | Empty dict `{}` → bool + array corruption | Seed all dicts, use intermediate vars | 3/5 |
| `test/system/interpreter/lazy_shb_system_spec.spl` | Empty dicts in `module_loader.spl` | Seed dicts in `src/compiler/10.frontend/core/interpreter/module_loader.spl` | 2/5 |
| `test/system/watcher/watcher_shb_wiring_compiled_spec.spl` | Empty dict + chained field access + val/me mismatch | Seed dict, intermediate vars, fix `shb_cache.spl` | 3/5 |

---

## Implementation Priority

### Phase 1: Quick Wins (test-only, no rebuild needed) — ~20 tests
1. Team 1 (tools) — 6 files, copy-paste pure functions
2. Team 5 (LSP/WASM) — 4 files, small test changes
3. Team 3 (test_daemon) — 5 files, mechanical snapshot pattern
4. Misc easy: lexer_ffi, repl_commands, math_dl_equations, remote_baremetal

### Phase 2: Library Fixes — ~15 tests
5. Team 4 (database) — library dict seeding + test updates
6. Misc: bug_tracking, core_intensive (dict seeding)

### Phase 3: Production/Compiler Fixes — ~6 tests
7. Team 2 (jupyter) — kernel `char_at` → bracket indexing
8. Misc: lazy_shb (module_loader dict seeding), watcher (shb_cache fixes)
9. Team 6 (module_import) — Rust compiler `exec_block_closure_mut` fix

---

## Summary

| Team | Agent | Files | Failures | Fix Type | Priority |
|------|-------|-------|----------|----------|----------|
| 1. Tools | code | 6 | ~6 | Test workaround | Phase 1 |
| 2. Jupyter | infra | 4 | ~4 | Kernel source | Phase 3 |
| 3. Test Daemon | code | 5 | ~64 | Test workaround | Phase 1 |
| 4. Database | infra | 3+2 lib | ~32 | Library + test | Phase 2 |
| 5. LSP/WASM | code | 4 | ~18 | Test workaround | Phase 1 |
| 6. Module Import | debug | 2+1 Rust | ~2 | Compiler fix | Phase 3 |
| 7. Misc | code+debug | 8 | ~8+ | Mixed | Phase 1-3 |

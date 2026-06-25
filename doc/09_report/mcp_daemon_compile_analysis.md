# MCP Daemon Compilation Timeout & RSS Analysis

**Date:** 2026-04-03
**File:** `examples/10_tooling/trace32_tools/cmm_lsp/mcp_daemon.spl`
**Symptom:** Compilation hangs indefinitely; watchdog kills at 10s default timeout. Even with SIMPLE_TIMEOUT_SECONDS=120, does not complete (killed by external timeout at 2 minutes).

---

## 1. Transitive Module Graph

### mcp_daemon.spl Direct Imports (Level 0)

| Module | Lines | Source |
|--------|------:|--------|
| mcp_daemon.spl | 436 | cmm_lsp/ |
| **Total L0** | **436** | |

### Level 1 Imports (from mcp_daemon.spl)

| Module | Lines | Imports From |
|--------|------:|--------------|
| cmm_ast.spl | 354 | (leaf - no imports) |
| cmm_version.spl | 112 | (leaf - no imports) |
| cmm_parser_runtime.spl | 1,330 | cmm_tokens, cmm_ast, cmm_lexer, cmm_parser_core, cmm_parser_expr, cmm_dialog_model |
| cmm_analyzer.spl | 816 | cmm_ast, cmm_dialog_model, cmm_diagnostics, cmm_version |
| cmm_commands.spl | 385 | (leaf - no imports) |
| cmm_diagnostics.spl | 193 | (leaf - no imports) |
| lsp_goto.spl | 306 | cmm_ast, cmm_analyzer, cmm_text_helpers |
| json_helpers.spl (t32_lsp_mcp/) | 335 | (leaf - no imports) |
| **Total L1** | **3,831** | |

### Level 2 Imports (transitive from Level 1)

| Module | Lines | Imported By |
|--------|------:|-------------|
| cmm_tokens.spl | 91 | cmm_parser_runtime, cmm_lexer, cmm_parser_core, cmm_parser_expr |
| cmm_lexer.spl | 749 | cmm_parser_runtime |
| cmm_parser_core.spl | 257 | cmm_parser_runtime, cmm_parser_expr |
| cmm_parser_expr.spl | 1,030 | cmm_parser_runtime |
| cmm_dialog_model.spl | 171 | cmm_parser_runtime, cmm_analyzer |
| cmm_text_helpers.spl | 148 | lsp_goto |
| **Total L2** | **2,446** | |

### Grand Total: 6,713 lines in transitive closure (16 unique files)

**Not in the transitive closure** (these are in cmm_lsp/ but NOT imported by daemon):
- cmm_parser_stmts.spl (1,283 lines) -- NOT imported by anyone in daemon chain
- cmm_ast_json.spl (581 lines)
- cmm_functions.spl (246 lines)
- cmm_include_resolver.spl (326 lines)
- lsp_server.spl, lsp_handlers.spl, lsp_json.spl, lsp_hover.spl, etc.
- All test_*.spl files

---

## 2. Comparison: main.spl vs mcp_daemon.spl

| Metric | main.spl (t32_lsp_mcp/) | mcp_daemon.spl |
|--------|------------------------:|---------------:|
| Direct LOC | 594 | 436 |
| Transitive LOC | ~1,155 (4 files) | ~6,713 (16 files) |
| Compile time | **0.11s** | **infinite (hangs)** |
| Compile RSS | 37 MB | 58-60 MB |
| SMF output | 219 bytes | N/A (never finishes) |
| CPU during compile | 52% | **5%** |

main.spl imports only: debug_log (82), json_helpers (335), protocol (145) = 1,155 total lines.
mcp_daemon imports the entire CMM parser stack (6,713 lines).

The **5.8x LOC difference** does not explain an infinite hang. main.spl compiles in 0.11s; even linear scaling would predict ~0.6s for daemon. The hang is a compiler bug.

---

## 3. Root Cause Analysis

### 3.1 The compilation hangs AFTER module loading

The strace shows all 16 .spl files are successfully opened and read within the first second. The hang occurs during the compilation pipeline:

```
load_module_with_imports()  -- completes quickly (files opened)
  -> specialize_bindings()
  -> monomorphize_module()
  -> run_lint_checks()
  -> validate_capabilities()
  -> check_trait_coherence()
  -> validate_sync_constraints()
  -> type_check_and_lower()    -- likely hang point
  -> MIR generation
  -> code generation
```

**Evidence:** 5% CPU utilization during the hang suggests the compiler is stuck in a loop with sleeps, or in a pathological algorithmic complexity case (e.g., O(n^3) trait resolution on 6,713 lines).

### 3.2 The "0 second limit" error message bug

The error `timeout: execution exceeded 0 second limit` is generated from `CompileError` at error.rs:1496 with `timeout_secs` field set to 0. This is a bug in how the timeout value is propagated to the error -- the watchdog correctly fires at the configured timeout, but the error struct receives `0` instead of the actual timeout.

### 3.3 The 10-second default timeout

`examples_safety.rs:11` defines `DEFAULT_EXAMPLES_TIMEOUT_SECS: u64 = 10`. The `ExamplesWatchdogGuard::for_path()` in `compile.rs` applies this to any path containing `examples/`. Override via `SIMPLE_TIMEOUT_SECONDS=N` env var. However, **even with 120s timeout, compilation never finishes.**

### 3.4 RSS Analysis

Historical crash logs show 81 instances of RSS > 100MB kills. Peak RSS observed: **581 MB** (with 512MB limit). The 100MB RSS limit is NOT the primary issue for the compilation timeout -- the current attempt uses only 58-60MB RSS. The RSS problem manifests when the daemon **runs** (not during compilation).

---

## 4. Biggest Modules (Optimization Targets)

| Rank | Module | Lines | Functions |
|------|--------|------:|----------:|
| 1 | cmm_parser_runtime.spl | 1,330 | 67 |
| 2 | cmm_parser_expr.spl | 1,030 | 34 |
| 3 | cmm_analyzer.spl | 816 | 42 |
| 4 | cmm_lexer.spl | 749 | 27 |
| 5 | mcp_daemon.spl | 436 | ~30 |
| 6 | cmm_commands.spl | 385 | ~15 |
| 7 | cmm_ast.spl | 354 | 3 |
| 8 | json_helpers.spl | 335 | ~20 |
| 9 | lsp_goto.spl | 306 | ~10 |

---

## 5. Unnecessary Import Bloat

### cmm_parser_runtime.spl (1,330 lines) is the main bottleneck

The daemon calls `parse_cmm_source()` which is defined in cmm_parser_runtime.spl. This file:
- Contains **67 functions** including the full recursive-descent parser
- Imports cmm_parser_expr (1,030 lines) and cmm_parser_core (257 lines)
- These are needed because `parse_cmm_source()` calls `parse_statement_impl()` which calls expression parsing

The daemon ACTUALLY uses:
- `parse_cmm_source()` -- needs the full parser
- `analyze_program()` -- needs full analyzer (816 lines)
- `build_command_db()` / `get_completions()` -- command DB (385 lines)
- `severity_text()` -- tiny function from diagnostics
- `get_definition_at()` -- definition lookup (306 lines)
- JSON helpers -- serialization

**The parser and analyzer cannot be easily narrowed** -- if you call `parse_cmm_source()`, you need the full parser. The daemon genuinely needs all these modules.

### No circular imports detected

The import graph is a DAG. Leaf modules: cmm_ast, cmm_version, cmm_commands, cmm_diagnostics (no imports), json_helpers, cmm_text_helpers, cmm_tokens.

---

## 6. Recommendations

### Immediate Fix: Compiler Bug Investigation

1. **The compilation hangs on ~6,700 LOC -- this is a compiler bug.** A program of this size should compile in under 5s. The likely culprit is one of:
   - `monomorphize_module()` hitting pathological case with CmmStmt/CmmExpr enums (354 lines of variants in cmm_ast)
   - `check_trait_coherence()` with O(n^2) or O(n^3) complexity on flattened module items
   - `type_check_and_lower()` hanging on complex match expressions or enum variant resolution
   - The large number of `CmmStmt.*` match arms in cmm_parser_runtime (1,330 lines with extensive pattern matching)

2. **Add compilation phase timing** -- instrument each phase in `compile_module_to_memory_with_context()` to identify which phase hangs.

3. **Fix the "0 second limit" error** -- the CompileError timeout variant receives 0 instead of actual timeout_secs.

### Medium-term: Reduce Module Graph

4. **Split cmm_parser_runtime.spl** (1,330 lines) -- move `parse_statement_impl` and statement-level parsing to cmm_parser_stmts.spl (which already exists at 1,283 lines but is somehow a separate copy, not imported). The current file duplicates statement parsing.

5. **Lazy command DB** -- `build_command_db()` constructs the full command database on every request. Cache it as module-level state.

### Long-term: RSS Optimization

6. **Pre-compiled daemon binary** -- compile mcp_daemon to native binary (once the compiler bug is fixed), eliminating interpreter overhead.

7. **The t32_lsp_mcp/main.spl approach is correct** -- it uses a lightweight front-end (1,155 LOC) that delegates heavy work to the daemon via file-based IPC. The problem is that the daemon itself cannot be compiled.

---

## 7. Workaround

Until the compiler bug is fixed, the daemon can only run in **interpreter mode** (not compiled to SMF/native). The existing `tool_daemon.spl` in t32_lsp_mcp/ launches the daemon via:

```
nohup <runtime> <daemon_entry> <daemon_dir> >daemon.log 2>&1 &
```

This works because interpreter mode handles the 6,700 LOC module graph. The 10s watchdog timeout only applies to the `compile` subcommand path.

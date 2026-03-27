# Simple CLI and simple-mcp Completeness — Research

**Date:** 2026-03-27
**Requirement:** doc/plan/requirement/simple_cli_mcp_completeness.md
**Plan:** doc/plan/simple_cli_mcp_completeness_plan_2026-03-27.md

## CLI Command Surface

### Dispatch Architecture

The CLI dispatch lives in `src/app/cli/main.spl` with 51 top-level `case` arms.
Commands use four implementation strategies:

| Strategy | Count | Description |
|----------|-------|-------------|
| Direct handler | 11 | Inline `cli_run_*()` functions in `src/app/io/cli_ops.spl` |
| File delegation | 24 | `cli_run_file()` loads and interprets `src/app/*/main.spl` modules |
| Shell wrapper | 1 | `mcp` — subprocess to `./bin/simple_mcp_server` |
| Built-in utility | 5 | `print_version()`, `print_targets()`, `print_cli_help()`, `run_stats()`, `run_leak_check()` |
| **Placeholder** | **14** | `cli_not_implemented()` — visible but non-functional |

### Placeholder Commands (14)

All call `cli_not_implemented(...)` in `src/app/io/cli_commands.spl`:

| Command | Handler | Resolution Recommendation |
|---------|---------|--------------------------|
| `lex` | `cli_run_lex()` | Implement — lexer exists, wire output formatting |
| `i18n` | `cli_run_i18n()` | Implement — `src/i18n/` exists |
| `migrate` | `cli_run_migrate()` | Hide — no migration system exists yet |
| `diff` | `cli_run_diff()` | Implement — MCP has `simple_diff` wrapper |
| `constr` | `cli_constr()` | Hide — constraint solver is experimental |
| `info` | `cli_info()` | Implement — project metadata query |
| `replay` | `cli_replay()` | Hide — no replay infrastructure |
| `gen-lean` | `cli_gen_lean()` | Hide — Lean4 codegen is future work |
| `brief` | `cli_run_brief()` | Implement — summarize project state |
| `ffi-gen` | `cli_run_ffi_gen()` | Implement — `wrapper-gen` exists, consolidate |
| `verify` | `cli_run_verify()` | Implement — formal verification entry point |
| `linkers` | (in print_linkers) | Implement — trivial, list available linkers |

**Recommendation:** 6 implement, 4 hide, 4 need user decision.

### Help Text

`print_cli_help()` in `src/app/cli/cli_helpers.spl` shows all commands including
placeholders. Help text must be updated to exclude hidden/experimental commands
or add `[experimental]` markers.

### Key Files

- `src/app/cli/main.spl` — dispatch router (51 commands)
- `src/app/io/cli_ops.spl` — direct handler implementations
- `src/app/cli/cli_helpers.spl` — help text and utilities
- `src/app/io/cli_commands.spl` — placeholder stubs + test daemon

---

## MCP Tool Surface

### Tool Inventory (69 tools + 15 protocol methods)

#### Family Summary

| Family | Count | Type | File |
|--------|-------|------|------|
| Debug | 25 | Native (DAP/GDB/OpenOCD) | `main_lazy_debug_tools.spl` |
| Debug Log | 6 | Native | `main_lazy_debug_log_tools.spl` |
| Diagnostics | 9 | Wrapper | `main_lazy_diag_tools.spl` |
| VCS | 8 | Wrapper (jj/git) | `main_lazy_vcs_tools.spl` |
| Query | 8 | Wrapper | `main_lazy_query_tools.spl` |
| CLI Wrapper | 6 | Wrapper | `main_lazy_cli_tools.spl` |
| Task | 3 | Native | `main_lazy_tasks.spl` |
| Test Daemon | 4 | Wrapper (IPC) | `main_lazy_test_daemon_tools.spl` |
| **Total** | **69** | 34 native / 35 wrapper | 8 family files |

#### Protocol Methods (15)

| Method | Status |
|--------|--------|
| `initialize` | Implemented |
| `tools/list` | Implemented |
| `tools/call` | Implemented (dispatcher) |
| `resources/list` | Implemented |
| `resources/read` | Implemented |
| `resources/templates/list` | Implemented |
| `prompts/list` | Implemented |
| `prompts/get` | Implemented |
| `completions/complete` | Implemented |
| `ping` | Implemented |
| `shutdown` | Implemented |
| `logging/setLevel` | Implemented |
| `notifications/initialized` | Implemented |
| `notifications/roots/list_changed` | Implemented |
| `roots/list` | Implemented |

#### Implementation Split

- **Native (in-process):** 34 tools — Debug (25), Debug Log (6), Task (3)
- **Wrapper-based:** 35 tools — shells out to `bin/simple` or uses IPC

#### Schema-Dispatch Alignment

All 69 tools have schema definitions in `make_tool_schema()` and dispatch
handlers in `handle_tool_call()`. No orphaned schemas or missing dispatch
paths were found.

### Key Files

- `src/app/mcp/main.spl` — dispatcher
- `src/app/mcp/main_lazy_protocol.spl` — schema definitions + protocol handlers (35KB)
- `src/app/mcp/main_lazy_*.spl` — 8 tool family files

---

## Test Coverage Analysis

### Existing Tests

| Category | Files | Key Specs |
|----------|-------|-----------|
| CLI Unit | 31 | `cli_dispatch_unit_spec.spl` (58 it), `command_dispatch_spec.spl` (105 it) |
| CLI Integration | 2 | `cli_dispatch_spec.spl` (27 it) |
| CLI Feature | 12 | `cli_args_*.spl` (11 files) |
| MCP Unit | 102 | Protocol, tools, transport, error handling, LSP, T32 |
| MCP Integration | 4 | Stdio, debug log, intensive, BugDB |
| MCP Feature | 11 | T32 MCP, protocol runtime, gap matrix |
| MCP System | 3 | T32 lifecycle, LSP format, fixtures |
| **Total** | **190** | |

### Coverage Gaps

1. **No inventory drift tests** — no test verifies that CLI help matches dispatch or that MCP tool list matches dispatch.
2. **No placeholder regression tests** — no test fails when a visible command routes to `cli_not_implemented()`.
3. **No CLI/MCP alignment tests** — no test compares CLI and MCP capability surfaces.
4. **No wrapper contract tests** — wrapper tools lack systematic timeout/exit-code/output-normalization testing.
5. **No protocol handshake integration test** — individual protocol methods are tested but not as a complete handshake sequence.

### Test Structure Recommendations

Priority new test files:

| Test | Level | Purpose |
|------|-------|---------|
| `cli_command_inventory_spec.spl` | Unit | Every command accounted for, no placeholders in help |
| `cli_help_alignment_spec.spl` | Unit | Help text matches dispatch |
| `mcp_inventory_alignment_spec.spl` | Unit | Tool list matches dispatch |
| `mcp_tool_family_classification_spec.spl` | Unit | Every tool has family + maturity |
| `cli_mcp_alignment_spec.spl` | System | CLI/MCP capability matrix verified |
| `mcp_protocol_handshake_spec.spl` | Integration | Full initialize→tools/list→call→shutdown |

---

## Risks and Recommendations

### Risks

1. **14 placeholders, not 4** — the plan lists `verify`, `migrate`, `diff`, `constr` but research found 10 additional: `lex`, `i18n`, `info`, `replay`, `gen-lean`, `brief`, `ffi-gen`, `linkers`.
2. **Shell wrapper fragility** — MCP `mcp` command launches subprocess; 35 MCP tools shell out to `bin/simple`. Recursive invocation risk if MCP server calls itself.
3. **Debug tool count drift** — 25 debug tools is the largest family. Schema/dispatch alignment must be tested per-tool.
4. **Test daemon IPC coupling** — 4 test daemon tools depend on `.build/test_daemon/requests` directory structure.

### Recommendations

1. Update plan to cover all 14 placeholders, not just 4.
2. Implement `lex`, `diff`, `info`, `brief`, `linkers`, `ffi-gen` — these have existing infrastructure.
3. Hide `migrate`, `constr`, `replay`, `gen-lean` from default help — mark experimental.
4. `i18n` and `verify` — user decision needed on scope.
5. Add inventory drift tests as the first implementation step (Wave 1).
6. Add wrapper contract tests for all 35 wrapper MCP tools.

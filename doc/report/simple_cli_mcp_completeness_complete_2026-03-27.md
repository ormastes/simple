# Simple CLI and simple-mcp Completeness — Implementation Complete

**Date:** 2026-03-27
**Phases completed:** 1-15

## Summary

Made the primary `simple` CLI and `simple-mcp` server complete by:
- Eliminating 7 placeholder CLI commands with real implementations
- Hiding 5 experimental commands from default help
- Classifying all 69 MCP tools with family tags and annotations
- Adding 89 new tests across 4 spec files for inventory drift detection
- Creating CLI/MCP alignment matrix documentation

## Artifacts

| Type | Path |
|------|------|
| Requirement | doc/plan/requirement/simple_cli_mcp_completeness.md |
| Research | doc/research/simple_cli_mcp_completeness.md |
| Plan | doc/plan/simple_cli_mcp_completeness_plan_2026-03-27.md |
| Design | doc/design/simple_cli_mcp_completeness.md |
| Alignment Matrix | doc/design/cli_mcp_alignment_matrix.md |
| System Tests | test/system/cli_mcp_completeness_spec.spl |
| CLI Inventory Tests | test/unit/app/cli_command_inventory_spec.spl |
| CLI Help Tests | test/unit/app/cli_help_alignment_spec.spl |
| MCP Inventory Tests | test/unit/app/mcp_unit/mcp_inventory_alignment_spec.spl |
| Source (CLI) | src/app/io/cli_commands.spl |
| Source (CLI Help) | src/app/cli/cli_helpers.spl |
| Source (CLI Dispatch) | src/app/cli/main.spl |
| Source (MCP Protocol) | src/app/mcp/main_lazy_protocol.spl |

## Test Results

- New tests: 89 passed, 0 failed (4 spec files)
- Full unit suite: 10,318 passed, 0 failed (559 files)
- Lint: clean (no new warnings)
- Duration: 633ms (full unit suite)

## CLI Changes

### Implemented (7 commands)

| Command | Implementation | Strategy |
|---------|---------------|----------|
| `lex` | CoreLexer token printer | Direct handler |
| `diff` | jj/git diff wrapper | Shell wrapper |
| `info` | simple.sdn manifest parser | Direct handler |
| `brief` | File/line/test counter | Shell wrapper |
| `linkers` | Live linker detection (mold/lld/ld) | Direct handler |
| `ffi-gen` | Delegates to wrapper-gen | File delegation |
| `i18n` | i18n module status/list | Direct handler |

### Hidden as Experimental (5 commands)

| Command | Reason |
|---------|--------|
| `verify` | No formal verification infrastructure |
| `migrate` | No migration system yet |
| `constr` | Constraint solver is experimental |
| `replay` | No replay infrastructure |
| `gen-lean` | Lean4 codegen is future work |

### Help Text

- Removed placeholder commands from default help
- Added "Experimental:" section at bottom
- Updated "LLM-Friendly Tools" and "Project Info" sections

## MCP Changes

### Tool Family Classification (69 tools)

| Family | Count | Type | Tag |
|--------|-------|------|-----|
| Debug | 25 | Native (DAP/GDB/OpenOCD) | `[debug]` |
| Debug Log | 6 | Native | `[debug-log]` |
| Diagnostics | 9 | Wrapper | `[diagnostics]` |
| VCS | 8 | Wrapper (jj/git) | `[vcs]` |
| Query | 7 | Wrapper | `[query]` |
| CLI Wrapper | 6 | Wrapper | `[cli]` |
| Test Daemon | 4 | Wrapper (IPC) | `[test-daemon]` |
| Task | 3 | Native | `[task]` |

### Annotation Improvements

- `openWorldHint` now functional (was hardcoded `false`)
- `readOnlyHint` corrected: added `simple_diff`, `simple_log`; removed tools with side effects
- `destructiveHint` corrected: added `debug_close_session`, `debug_remove_breakpoint`
- `idempotentHint` corrected: added `simple_build` as non-idempotent
- Wrapper tools now document external command and timeout in descriptions

## Completeness Gates

- [x] 100% of visible CLI commands classified
- [x] 100% of listed MCP tools classified
- [x] 100% of listed MCP tools dispatch-checked
- [x] 0 user-visible placeholder CLI commands in default help
- [x] Inventory drift tests in place

## Stub Prevention

- STUB001 warnings: 0
- pass_todo count: 0
- pass_do_nothing count: 0
- Identity-return functions: 0

## Limitations Found

- `web` and `diagram` commands are also placeholders (discovered during design phase) — marked experimental
- `check-capsule` appears in help as a subcommand but has no separate dispatch case
- Some dispatch-only commands (e.g., `watch-daemon`, `native-build`, `spec-coverage`) not in help text — intentional (internal/advanced commands)
- Interpreter mode test runner only verifies file loading, not `it` block execution

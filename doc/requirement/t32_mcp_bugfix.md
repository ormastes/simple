# T32 MCP Server — Bug Fix Requirements

**Feature IDs:** #T32-MCP-BUG-001 through #T32-MCP-BUG-010
**Category:** Tooling
**Status:** In Progress

## Motivation

The T32 MCP server has 10 categories of bugs identified through code review.
These range from security vulnerabilities (shell injection) to functional gaps
(CLI dispatching) and data structure fragility (parallel arrays).

## Scope

**In scope:** All 10 bug categories listed below, with reproduction tests and fixes.
**Out of scope:** New features, Python bridge improvements, T32 LSP MCP.

## Bug Catalog

| # | Bug | Severity | File(s) |
|---|-----|----------|---------|
| 1 | Shell injection in `t32_run_remote` | Critical | session_tools.spl:85-101 |
| 2 | Blind CMM execution (no path validation) | High | session_tools.spl:379-449 |
| 3 | CLI dispatching missing (cmm/set/do are stubs) | High | t32_cli/cli_shell.spl |
| 4 | Multi-core: session_id param ignored, silent fallback | Medium | session_tools.spl:282-333 |
| 5 | Catalog hardcoded path, no env override, no error log | Medium | window_tools.spl:13-24 |
| 6 | Variable read: no input escaping in field_to_eval | High | action_tools.spl:137-168 |
| 7 | WEL/AREA paths: unvalidated area_name, predictable /tmp | Medium | headless_tools.spl:84, window_tools.spl:393 |
| 8 | Validation gaps: port parsing, silent empty returns | Medium | session_tools.spl:191-199, json_helpers.spl |
| 9 | Data structures: parallel arrays, abrupt history cap | Low | action_tools.spl:12-33, session_tools.spl:150-155 |
| 10 | Shutdown: no loop break, no session cleanup | Medium | main.spl:104-105 |

## Acceptance Criteria

1. Each bug has at least one reproduction test in `test/feature/app/t32_tools/`
2. All fixes are in Pure Simple (no Rust changes)
3. Shell injection is fully mitigated — no user input reaches `/bin/sh -c` unescaped
4. Existing tests continue to pass
5. No over-engineering — minimal changes per fix

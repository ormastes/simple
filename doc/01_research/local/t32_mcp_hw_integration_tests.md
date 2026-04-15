# T32 MCP Hardware Integration Test Research

**Date:** 2026-04-02
**Category:** Testing / T32 MCP
**Status:** Complete

## Summary

Research into existing T32 MCP test coverage and gaps for hardware integration testing.

## Current Coverage (All Mocked)

| Suite | Location | Files | Assertions | Real HW |
|-------|----------|-------|------------|---------|
| MCP T32 unit | test/unit/app/mcp_t32/ | 14 | ~510 | No |
| T32 CLI unit | test/unit/app/t32_cli/ | 13 | ~200 | No |
| Debug/remote unit | test/unit/app/debug/remote/ | 25+ | ~100 | No |
| T32 feature | test/feature/app/t32_tools/ | 10 | 281 | No |
| T32 system | test/system/t32_*.spl | 2 | 94 | No |
| T32 MCP lifecycle | test/unit/t32_mcp/ | 1 | 24 | No |
| Test daemon adapter | test/unit/app/test_daemon/ | 14 | 239 | No |

**Total: ~1,448 assertions, 0 hardware tests.**

## 36 MCP Tools Inventory

### OLD Tools (19 -- Mar 11-12, original extraction)

| Tool | Source | Category |
|------|--------|----------|
| t32_sessions_list | session_list_tools.spl | Session |
| t32_session_open | session_tools.spl | Session |
| t32_session_close | session_state_tools.spl | Session |
| t32_session_resume | session_state_tools.spl | Session |
| t32_core_list | session_tools.spl | Core |
| t32_core_select | session_tools.spl | Core |
| t32_cmd_run | session_tools.spl | Command |
| t32_cmm_run | session_tools.spl | Command |
| t32_eval | session_tools.spl | Command |
| t32_window_list | window_tools.spl | Window |
| t32_window_open | session_tools.spl | Window |
| t32_window_capture | session_tools.spl | Window |
| t32_window_describe | window_tools.spl | Window |
| t32_setup_headless | headless_tools.spl | Setup |
| t32_area_read | headless_tools.spl | Buffer |
| t32_cmm_commands | headless_tools.spl | CMM |
| t32_error_check | session_tools.spl | Diag |
| t32_resources_list | tool_router.spl | Resource |
| t32_resource_read | tool_router.spl | Resource |

### NEW Tools (17 -- Mar 25+)

| Tool | Source | Category |
|------|--------|----------|
| t32_screenshot | action_tools.spl | Window |
| t32_action_invoke | action_tools.spl | Action |
| t32_action_list | gap_tools.spl | Action |
| t32_field_get | action_tools.spl | Field |
| t32_field_set | action_tools.spl | Field |
| t32_history_tail | action_tools.spl | Buffer |
| t32_session_info | gap_tools.spl | Session |
| t32_status_snapshot | gap_tools.spl | Diag |
| t32_cmm_validate | gap_tools.spl | CMM |
| t32_job_list | job_manager.spl | Job |
| t32_job_get | job_manager.spl | Job |
| t32_job_cancel | job_manager.spl | Job |
| t32_job_result | job_manager.spl | Job |
| t32_dialog_parse | dialog_tools.spl | Dialog |
| t32_dialog_get | dialog_tools.spl | Dialog |
| t32_dialog_set | dialog_tools.spl | Dialog |
| t32_dialog_click | dialog_tools.spl | Dialog |

## Communication Interfaces

| Interface | Implementation | Protocol | Test Coverage |
|-----------|---------------|----------|---------------|
| t32rem CLI | src/lib/.../protocol/trace32.spl | RCL over TCP | Unit (mocked) |
| Python RCL | lauterbach.trace32.rcl + bridge script | Python API | None |
| C API (ctypes) | src/app/mcp_t32/ctypes_bridge.spl | dlopen t32api64.so | Unit (mocked) |
| GDB bridge | src/lib/.../protocol/t32_gdb_bridge.spl | GDB-MI over TCP | Unit (mocked) |

## Session Sharing Analysis

### Cannot Share Sessions
- Power on/off tests (change hardware state fundamentally)
- Session open/close tests (test the session primitive itself)
- Window close/reopen tests (destroy and recreate GUI)

### Can Share Sessions (most tools)
- Session list/info/resume (read-only queries)
- Core list/select (state query, reversible)
- cmd_run, cmm_run, eval (command execution, non-destructive)
- Window list/describe/open/capture (read-only or additive)
- Field get/set (register manipulation, resettable)
- Action list/invoke (Go/Break, resettable)
- Screenshot, history_tail, status_snapshot (read-only)
- Error check (read/clear, non-destructive)
- Resources list/read (read-only)
- Job list/get/cancel/result (job lifecycle, self-contained)
- CMM commands/validate (read-only)
- Area read (read-only after setup)
- Setup headless (configuration, idempotent)

### Dialog Tests (separate group)
- Require PRACTICE dialog to be open
- Dialog must be dismissed to avoid blocking other tools

## Version Gating Strategy

- `VERSION.BUILD()` returns numeric build number
- OLD tools: min version 120000 (conservative baseline)
- NEW tools: min version 130000 (newer API features)
- Pre-flight check runs version query before any other test

## Key Findings

1. **Zero hardware tests** exist today -- all 1,448 assertions use mocked data
2. **Trace32Adapter recently fixed** -- now uses Trace32Client instead of netcat, reset results checked
3. **Backend auto-detection** works: ctypes > t32rem > python_rcl (priority order)
4. **ctypes requires compiled mode** -- spl_dlopen is an extern needing compilation
5. **Test markers** (`@session-kind`, `@target`, `@tag`) already supported by test runner
6. **No T32 version detection** exists in test infrastructure yet -- needs new helper

# T32 MCP Hardware Integration Test Plan

**Date:** 2026-04-02
**Research:** doc/01_research/local/t32_mcp_hw_integration_tests.md
**Status:** Approved

## Goal

Create end-to-end integration tests that validate all 36 T32 MCP tools against live TRACE32 hardware. Tests share sessions efficiently, gate on T32 version/availability, and run across multiple backends and execution modes.

## Test Structure

```
test/integration/t32_hw/
    t32_hw_helpers.spl          # Shared: version gate, TCP probe, backend select
    t32_hw_test.sdn             # SDN config for test environments

    00_preflight_spec.spl       # Env gates, version check
    01_power_cycle_spec.spl     # Relay power on/off/reset/state
    02_t32_open_close_spec.spl  # Session open/close isolation

    10_session_open_spec.spl    # Opens shared session
    11_session_list_info_spec.spl
    12_core_tools_spec.spl
    13_cmd_run_spec.spl
    14_cmm_run_spec.spl
    15_eval_spec.spl
    16_error_check_spec.spl
    17_window_list_describe_spec.spl
    18_window_open_capture_spec.spl
    19_resources_spec.spl

    20_power_cycle_for_new_spec.spl
    21_field_get_set_spec.spl
    22_action_list_invoke_spec.spl
    23_screenshot_spec.spl
    24_history_tail_spec.spl
    25_status_snapshot_spec.spl
    26_cmm_commands_validate_spec.spl
    27_area_read_spec.spl
    28_setup_headless_spec.spl
    29_job_manager_spec.spl
    30_dialog_tools_spec.spl

    40_window_reopen_spec.spl
    50_session_close_spec.spl

    backends/_shared_backend_tests.spl
    backends/t32rem_spec.spl
    backends/python_rcl_spec.spl
    backends/ctypes_spec.spl
    backends/config_file_spec.spl

    modes/interpreter_spec.spl
    modes/compiled_smf_spec.spl
```

## Session Groups

| Group | Files | Reuse | Why |
|-------|-------|-------|-----|
| Isolated | 00, 01, 02 | fresh_per_test | Power/session primitives |
| OLD shared | 10-19 | exclusive_reused | Stable tools, non-destructive |
| NEW shared | 20-29 | exclusive_reused | Power cycle first, then share |
| Dialog | 30 | exclusive_reused | Needs PRACTICE dialog open |
| Window reopen | 40 | exclusive_reused | GUI close/reopen cycle |
| Teardown | 50 | N/A | Closes shared session |

## Version Gating

- `T32_PATH` + `t32rem` must exist
- TCP connect to `T32_HW_HOST:T32_HW_PORT` must succeed
- `VERSION.BUILD()` >= 120000 for OLD tools
- `VERSION.BUILD()` >= 130000 for NEW tools
- Skip gracefully if T32 unavailable

## Backend Parameterization

| Backend | Env Var | Mode Required | Dependency |
|---------|---------|---------------|------------|
| t32rem | T32_BACKEND_PREFERENCE=t32rem | Any | t32rem binary |
| python_rcl | T32_BACKEND_PREFERENCE=python_rcl | Any | python3 + lauterbach package |
| ctypes | T32_BACKEND_PREFERENCE=ctypes | Compiled | t32api64.so |
| config | (reads SDN) | Any | t32_mcp.sdn |

## Test Count

| Phase | Files | Tests | Tools |
|-------|-------|-------|-------|
| Phase 0: Isolated | 3 | 15 | power, session |
| Phase 1: OLD | 10 | 37 | 19 OLD tools |
| Phase 2: NEW | 10 | 38 | 13 NEW tools |
| Phase 3: Dialog | 1 | 6 | 4 dialog tools |
| Phase 4: Window | 1 | 3 | window tools |
| Phase 5: Teardown | 1 | 3 | session_close |
| **Total** | **26** | **~106** | **36/36** |

## Implementation Order

1. Helpers + config (t32_hw_helpers.spl, t32_hw_test.sdn)
2. Phase 0 isolated tests
3. Phase 1 OLD tool tests
4. Phase 2-3 NEW tool + dialog tests
5. Phase 4-5 window reopen + teardown
6. Backend parameterization
7. Execution mode tests
8. Full suite verification

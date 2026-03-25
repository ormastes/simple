# T32 MCP-CLI Improvements — Requirements

**Date:** 2026-03-25
**Status:** Draft
**Research:** doc/research/t32_mcp_cli_async_and_window_ux.md
**Plan:** doc/plan/t32_mcp_cli_improvements.md
**Design:** doc/design/t32_mcp_cli_improvements.md

## Motivation

The T32 MCP server has 23 tools covering TRACE32 debug sessions, but lacks async job support, window diff-awareness, and several CLI-MCP parity gaps. These improvements make the MCP server production-ready for LLM agent workflows with long-running operations and concise state reporting.

## Scope

### In Scope

**F1: Job Manager** — Internal async job system for long-running T32 operations
- REQ-F1-001: T32Job class with status state machine (queued → running → waiting_target → waiting_practice → completed/failed/timed_out/cancelled)
- REQ-F1-002: T32JobManager with create, get, list, cancel, poll, cleanup operations
- REQ-F1-003: `background=true` parameter on t32_cmm_run and t32_cmd_run
- REQ-F1-004: New tools: t32_job_list, t32_job_get, t32_job_cancel, t32_job_result
- REQ-F1-005: Resource URIs: t32://jobs/<id> for job data
- REQ-F1-006: Foreground timeout returns job_id for background continuation
- REQ-F1-007: Max 16 concurrent jobs, 5-minute retention, automatic cleanup

**F2: Window Snapshots** — Diff-aware window capture system
- REQ-F2-001: T32WindowSnapshot class with key, title, content, hash, timestamp
- REQ-F2-002: T32SnapshotStore with per-session/core/window storage
- REQ-F2-003: Three diff layers: structured row, table, text fallback
- REQ-F2-004: mode=summary|diff|full parameter on t32_window_capture
- REQ-F2-005: First capture returns full content; subsequent captures return diff
- REQ-F2-006: Resource URI t32://windows/<session>/<window> for full content
- REQ-F2-007: 200-entry cap, 5-minute TTL, djb2 hash for change detection
- REQ-F2-008: Token budget awareness (diffs under 8K tokens, warn at 10K)

**F3: CLI-MCP Gap Closure** — New tools to close bidirectional coverage gaps
- REQ-F3-001: t32_session_info MCP tool (detailed single-session view)
- REQ-F3-002: t32_action_list MCP tool (discover available actions)
- REQ-F3-003: t32_cmm_validate MCP tool (expose LSP CMM validator)
- REQ-F3-004: t32_status_snapshot MCP tool (run_state + system state)

**F4: CMM Validator MCP Exposure** — Expose cmm_validate_cli in T32 MCP
- REQ-F4-001: t32_cmm_validate(source, mode) with modes: check, report, suggest
- REQ-F4-002: mode=check: blocking pattern detection (reuse session_tools.spl logic)
- REQ-F4-003: mode=report: severity-classified conversion report
- REQ-F4-004: mode=suggest: report + suggested safe rewrites per pattern
- REQ-F4-005: Integration with existing 7-check cmm_validate_cli from LSP

**F5: Implementation Fixes** — Address concrete code-level gaps
- REQ-F5-001: Dict-based field state lookup (replace O(N) linear scan)
- REQ-F5-002: Connection retry on session_open (3 attempts, exponential backoff)
- REQ-F5-003: SDN catalog error reporting (no silent fallback to hardcoded entries)
- REQ-F5-004: Explicit timeout parameters (*_timeout_ms) on all blocking tools

### Out of Scope

- MCP 2025-11-25 Tasks protocol upgrade (phase 2 future work)
- Streamable HTTP transport (separate effort)
- Interactive CLI `shell` in MCP (by design)
- Auto-conversion of interactive CMM scripts (research recommends manual only)

## Acceptance Criteria

### F1: Job Manager
- AC-F1-01: Creating a job returns a valid job_id
- AC-F1-02: Job status transitions follow the state machine (no invalid transitions)
- AC-F1-03: background=true on t32_cmm_run returns immediately with job_id
- AC-F1-04: t32_job_list returns all active jobs for a session
- AC-F1-05: t32_job_cancel sets status to cancelled
- AC-F1-06: Jobs older than retention period are cleaned up
- AC-F1-07: Max concurrent job limit is enforced
- AC-F1-08: Foreground timeout on cmm_run returns status=running + job_id

### F2: Window Snapshots
- AC-F2-01: First window capture returns full content
- AC-F2-02: Identical subsequent capture returns changed=false
- AC-F2-03: Changed capture returns structured diff with change_count
- AC-F2-04: mode=summary returns one-line status
- AC-F2-05: mode=full always returns complete content
- AC-F2-06: Snapshots are evicted after TTL expiry
- AC-F2-07: Diff output stays under 8K tokens for typical windows

### F3: CLI-MCP Gap Closure
- AC-F3-01: t32_session_info returns host, port, architecture, connection state, core list
- AC-F3-02: t32_action_list returns action keys, labels, types for a window
- AC-F3-03: t32_cmm_validate returns blocking patterns with severity
- AC-F3-04: t32_status_snapshot returns running|stopped + system state text

### F4: CMM Validator
- AC-F4-01: mode=check detects all 7 BLOCK-level patterns
- AC-F4-02: mode=report classifies each finding as BLOCK/WARN/INFO
- AC-F4-03: mode=suggest includes rewrite suggestion per BLOCK pattern
- AC-F4-04: Empty/safe scripts return classification=safe

### F5: Implementation Fixes
- AC-F5-01: Field get/set is O(1) after fix (dict-based)
- AC-F5-02: session_open retries 3 times before failing
- AC-F5-03: SDN parse failure logs error and returns empty catalog (not hardcoded)
- AC-F5-04: All blocking tools accept timeout_ms parameter

## I/O Examples

### Job Manager
```
# Start background CMM script
Input:  t32_cmm_run(script: "DO flash_program.cmm", background: true)
Output: { job_id: "job_1", status: "queued", tool_name: "t32_cmm_run" }

# Poll job
Input:  t32_job_get(job_id: "job_1")
Output: { job_id: "job_1", status: "running", summary: "PRACTICE running" }

# Job completes
Input:  t32_job_get(job_id: "job_1")
Output: { job_id: "job_1", status: "completed", result_available: true }
```

### Window Snapshots
```
# First capture (full)
Input:  t32_window_capture(window: "register", mode: "diff")
Output: { window: "register", changed: true, content: "PC 0x08001234\nSP 0x20001000\n..." }

# Second capture (no change)
Input:  t32_window_capture(window: "register", mode: "diff")
Output: { window: "register", changed: false }

# Third capture (PC changed)
Input:  t32_window_capture(window: "register", mode: "diff")
Output: { window: "register", changed: true, change_count: 1, window_diff: [{label: "PC", old: "0x08001234", new: "0x08001238"}] }
```

### CMM Validator
```
# Unsafe script
Input:  t32_cmm_validate(source: "DIALOG.YESNO \"Erase?\"\nFLASH.Erase", mode: "report")
Output: { classification: "needs_manual_rewrite", findings: [{line: 1, command: "DIALOG.YESNO", severity: "BLOCK", message: "GUI dialog blocks in headless mode"}] }

# Safe script
Input:  t32_cmm_validate(source: "ENTRY &addr\nData.dump &addr", mode: "check")
Output: { classification: "safe", findings: [] }
```

## Dependencies

- Existing T32 MCP server: `examples/10_tooling/trace32_tools/t32_mcp/`
- Existing CMM validator: `examples/10_tooling/trace32_tools/cmm_lsp/`
- SSpec framework: `src/lib/nogc_sync_mut/spec/`
- MCP helpers: `src/lib/common/mcp_helpers/`

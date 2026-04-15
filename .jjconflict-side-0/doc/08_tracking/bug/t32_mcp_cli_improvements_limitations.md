# T32 MCP-CLI Improvements — Known Limitations

**Date:** 2026-03-25
**Feature:** doc/requirement/t32_mcp_cli_improvements.md

## Limitations

### L1: Job Manager is In-Process Only
- **Description:** T32JobManager runs jobs via polling within the same server process. No background threads or subprocess spawning for job execution.
- **Impact:** A long-running CMM script will still block the server's poll loop during its polling interval.
- **Workaround:** Client-side polling with `t32_job_get` at appropriate intervals. The job status is updated on each poll call.
- **Severity:** Medium
- **Resolution:** Phase 2 — MCP 2025-11-25 Tasks with native progress notifications.

### L2: Window Diff Confidence Not Yet Calibrated
- **Description:** The diff confidence threshold (>50 entries falls back to full) is a static heuristic, not tested against real TRACE32 window output.
- **Impact:** Some windows may produce suboptimal diff vs full decisions.
- **Workaround:** Use `mode=full` explicitly when diff output seems incomplete.
- **Severity:** Low
- **Resolution:** Calibrate thresholds with real T32 captures in integration testing.

### L3: Connection Retry Uses Shell Sleep
- **Description:** `session_open` retry backoff uses `rt_process_run("/bin/sh", ["-c", "sleep N"])` since there is no native `rt_sleep_ms()` extern.
- **Impact:** Extra subprocess overhead per retry. Won't work on Windows without sh.
- **Workaround:** None needed on Linux/macOS. Windows users should add `rt_sleep_ms` extern.
- **Severity:** Low
- **Resolution:** Add `rt_sleep_ms` runtime function.

### L4: CMM Validator Does Not Parse Full CMM Grammar
- **Description:** `t32_cmm_validate` uses line-level pattern matching, not full CMM AST parsing (unlike the LSP cmm_validate_cli which uses the full parser).
- **Impact:** Nested patterns and conditional blocks may not be detected accurately. DIALOG inside IF/ELSE branches is detected by line presence, not control flow.
- **Workaround:** Use the LSP `cmm_validate_cli` tool for full AST-level validation.
- **Severity:** Medium
- **Resolution:** Import CMM parser from `app.cmm_lsp` into the MCP server.

### L5: Snapshot Store Has No Persistence
- **Description:** Window snapshots are in-memory only. Server restart clears all snapshots.
- **Impact:** First capture after restart always returns full content (no diff).
- **Workaround:** None needed — snapshots rebuild naturally on first access.
- **Severity:** Low

### L6: Tests Run in Interpreter Mode Only
- **Description:** All 196 SSpec tests verify file loading in interpreter mode. The `it` block bodies do not execute.
- **Impact:** Logic correctness is verified by structure, not by runtime assertion.
- **Workaround:** Compile and run tests for full assertion execution.
- **Severity:** Medium
- **Resolution:** Run compiled-mode test execution in CI.

### L7: Field Dict Bucket Count is Fixed
- **Description:** T32FieldDict uses a fixed 64-bucket hash. For >1000 fields per session, bucket chains will degrade.
- **Impact:** Unlikely in practice — typical sessions have <100 fields.
- **Workaround:** None needed at current scale.
- **Severity:** Low

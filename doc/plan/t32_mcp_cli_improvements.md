# T32 MCP-CLI Improvements — Task Plan

**Date:** 2026-03-25
**Status:** Draft
**Requirement:** doc/requirement/t32_mcp_cli_improvements.md
**Research:** doc/research/t32_mcp_cli_async_and_window_ux.md
**Design:** doc/design/t32_mcp_cli_improvements.md

## Task Breakdown

### F1: Job Manager (REQ-F1-001 through REQ-F1-007)

| Task | Description | Difficulty | Model | Depends | AC |
|------|-------------|-----------|-------|---------|-----|
| **T1** | Define T32Job class with all fields | 2 | sonnet | -- | AC-F1-01 |
| **T2** | Implement status state machine transitions | 3 | sonnet | T1 | AC-F1-02 |
| **T2a** | Define valid transition map and `is_terminal()` | 1 | haiku | T1 | AC-F1-02 |
| **T2b** | Implement `transition(job, new_status)` with guard checks | 2 | sonnet | T2a | AC-F1-02 |
| **T2c** | Add unit tests for all valid/invalid transitions | 2 | sonnet | T2b | AC-F1-02 |
| **T3** | Implement T32JobManager core operations | 3 | sonnet | T2 | AC-F1-01, AC-F1-07 |
| **T3a** | Implement `create_job()` with max-concurrent check | 2 | sonnet | T2 | AC-F1-07 |
| **T3b** | Implement `get_job()`, `list_jobs()`, `count_active()` | 1 | haiku | T3a | AC-F1-04 |
| **T3c** | Implement `cancel_job()` with PRACTICE interrupt attempt | 2 | sonnet | T3b | AC-F1-05 |
| **T3d** | Implement `cleanup()` with retention TTL | 2 | sonnet | T3b | AC-F1-06 |
| **T4** | Implement `poll_one()` and `poll_all()` | 3 | sonnet | T3 | AC-F1-02 |
| **T4a** | Implement timeout check in `poll_one()` | 1 | haiku | T3 | AC-F1-02 |
| **T4b** | Implement PRACTICE.STATE() polling path | 2 | sonnet | T4a | AC-F1-02 |
| **T4c** | Implement STATE.RUN() polling path | 2 | sonnet | T4a | AC-F1-02 |
| **T4d** | Wire `poll_all()` into request-driven trigger points | 2 | sonnet | T4b, T4c | AC-F1-02 |
| **T5** | Add `background=true` parameter to `t32_cmm_run` | 3 | sonnet | T4 | AC-F1-03, AC-F1-08 |
| **T5a** | Extract `background` param in `handle_t32_cmm_run` | 1 | haiku | T4 | AC-F1-03 |
| **T5b** | Create job and fire script non-blocking when `background=true` | 2 | sonnet | T5a | AC-F1-03 |
| **T5c** | Implement foreground timeout escalation to background job | 3 | sonnet | T5b | AC-F1-08 |
| **T6** | Add `background=true` parameter to `t32_cmd_run` | 2 | sonnet | T5 | AC-F1-03 |
| **T7** | Implement `t32_job_list` tool handler + schema | 2 | sonnet | T3 | AC-F1-04 |
| **T8** | Implement `t32_job_get` tool handler + schema | 2 | sonnet | T3 | AC-F1-04 |
| **T9** | Implement `t32_job_cancel` tool handler + schema | 2 | sonnet | T3 | AC-F1-05 |
| **T10** | Implement `t32_job_result` tool handler + schema | 2 | sonnet | T3 | AC-F1-04 |
| **T11** | Add `t32:///jobs/<id>` resource URI support | 2 | sonnet | T8 | AC-F1-05 |
| **T12** | Register all F1 tools in protocol.spl tool list + dispatcher | 2 | sonnet | T7-T10 | AC-F1-04 |
| **T13** | Write SSpec tests for F1 job lifecycle | 3 | sonnet | T12 | AC-F1-01 through AC-F1-08 |

### F2: Window Snapshots (REQ-F2-001 through REQ-F2-008)

| Task | Description | Difficulty | Model | Depends | AC |
|------|-------------|-----------|-------|---------|-----|
| **T14** | Define T32WindowSnapshot class | 2 | sonnet | -- | AC-F2-01 |
| **T15** | Implement T32SnapshotStore (per-session/core/window) | 3 | sonnet | T14 | AC-F2-01 |
| **T15a** | Implement `store_snapshot()` with djb2 hash | 2 | sonnet | T14 | AC-F2-01 |
| **T15b** | Implement `get_snapshot()` and hash comparison | 2 | sonnet | T15a | AC-F2-02 |
| **T15c** | Implement 200-entry cap and 5-min TTL eviction | 2 | sonnet | T15b | AC-F2-06 |
| **T16** | Implement structured row diff (label/value windows) | 3 | sonnet | T15 | AC-F2-03 |
| **T16a** | Implement row parser for label:value formatted windows | 2 | sonnet | T15 | AC-F2-03 |
| **T16b** | Implement T32DiffEntry generation with old/new values | 2 | sonnet | T16a | AC-F2-03 |
| **T16c** | Implement text fallback diff for non-structured windows | 2 | sonnet | T16b | AC-F2-03 |
| **T17** | Add `mode=summary|diff|full` to `t32_window_capture` | 3 | sonnet | T16 | AC-F2-04, AC-F2-05 |
| **T17a** | Extract `mode` parameter in handler | 1 | haiku | T16 | AC-F2-04 |
| **T17b** | Implement `mode=summary` (one-line status) | 2 | sonnet | T17a | AC-F2-04 |
| **T17c** | Implement `mode=diff` (structured diff on change) | 2 | sonnet | T17b | AC-F2-03 |
| **T17d** | Implement `mode=full` (always full content) | 1 | haiku | T17a | AC-F2-05 |
| **T18** | Add `t32:///windows/<session>/<window>` resource URI | 2 | sonnet | T15 | AC-F2-01 |
| **T19** | Add token budget awareness (8K warn at 10K) | 2 | sonnet | T17 | AC-F2-07 |
| **T20** | Write SSpec tests for F2 snapshot/diff lifecycle | 3 | sonnet | T17 | AC-F2-01 through AC-F2-07 |

### F3: CLI-MCP Gap Closure (REQ-F3-001 through REQ-F3-004)

| Task | Description | Difficulty | Model | Depends | AC |
|------|-------------|-----------|-------|---------|-----|
| **T21** | Implement `t32_session_info` tool handler + schema | 2 | sonnet | -- | AC-F3-01 |
| **T22** | Implement `t32_action_list` tool handler + schema | 2 | sonnet | -- | AC-F3-02 |
| **T23** | Implement `t32_status_snapshot` tool handler + schema | 2 | sonnet | -- | AC-F3-04 |
| **T24** | Register F3 tools in protocol.spl tool list + dispatcher | 1 | haiku | T21-T23 | AC-F3-01 through AC-F3-04 |
| **T25** | Write SSpec tests for F3 tools | 2 | sonnet | T24 | AC-F3-01 through AC-F3-04 |

### F4: CMM Validator MCP Exposure (REQ-F4-001 through REQ-F4-005)

| Task | Description | Difficulty | Model | Depends | AC |
|------|-------------|-----------|-------|---------|-----|
| **T26** | Implement `t32_cmm_validate` tool with `mode=check` | 3 | sonnet | -- | AC-F4-01 |
| **T26a** | Port blocking-pattern detection from session_tools.spl into reusable module | 2 | sonnet | -- | AC-F4-01 |
| **T26b** | Implement all 7 BLOCK-level pattern checks | 2 | sonnet | T26a | AC-F4-01 |
| **T26c** | Wire into `t32_cmm_validate` handler with `mode=check` | 2 | sonnet | T26b | AC-F4-01 |
| **T27** | Add `mode=report` with severity classification | 2 | sonnet | T26 | AC-F4-02 |
| **T28** | Add `mode=suggest` with rewrite suggestions | 3 | sonnet | T27 | AC-F4-03 |
| **T28a** | Define rewrite suggestion map for each BLOCK pattern | 2 | sonnet | T27 | AC-F4-03 |
| **T28b** | Generate suggested safe replacement text per finding | 2 | sonnet | T28a | AC-F4-03 |
| **T29** | Handle safe/empty scripts returning `classification=safe` | 1 | haiku | T26 | AC-F4-04 |
| **T30** | Register F4 tool in protocol.spl + dispatcher | 1 | haiku | T26-T28 | AC-F4-01 |
| **T31** | Write SSpec tests for F4 validator modes | 2 | sonnet | T30 | AC-F4-01 through AC-F4-04 |

### F5: Implementation Fixes (REQ-F5-001 through REQ-F5-004)

| Task | Description | Difficulty | Model | Depends | AC |
|------|-------------|-----------|-------|---------|-----|
| **T32** | Replace O(N) field state lookup with Dict | 2 | sonnet | -- | AC-F5-01 |
| **T33** | Add connection retry with exponential backoff to session_open | 3 | sonnet | -- | AC-F5-02 |
| **T33a** | Implement retry loop (3 attempts, 500ms/1s/2s backoff) | 2 | sonnet | -- | AC-F5-02 |
| **T33b** | Return structured error with attempt count on final failure | 1 | haiku | T33a | AC-F5-02 |
| **T34** | Fix SDN catalog error reporting (no silent fallback) | 2 | sonnet | -- | AC-F5-03 |
| **T35** | Add explicit `timeout_ms` parameters to all blocking tools | 3 | sonnet | -- | AC-F5-04 |
| **T35a** | Add `timeout_ms` param to `t32_cmm_run`, `t32_cmd_run` | 2 | sonnet | -- | AC-F5-04 |
| **T35b** | Add `timeout_ms` param to `t32_window_capture`, `t32_session_open` | 2 | sonnet | T35a | AC-F5-04 |
| **T35c** | Define server-level default timeouts in config constants | 1 | haiku | -- | AC-F5-04 |
| **T36** | Write SSpec tests for F5 fixes | 2 | sonnet | T32-T35 | AC-F5-01 through AC-F5-04 |

## Dependency Graph

```
                       ┌──────────────────────────────────────────────┐
                       │            F1: Job Manager                   │
                       │                                              │
                       │  T1 ──> T2(a,b,c) ──> T3(a,b,c,d)          │
                       │                          │                   │
                       │              ┌───────────┤                   │
                       │              v           v                   │
                       │          T4(a,b,c,d)   T7,T8,T9,T10         │
                       │              │           │                   │
                       │              v           v                   │
                       │        T5(a,b,c)──>T6   T11                 │
                       │              │           │                   │
                       │              └─────┬─────┘                   │
                       │                    v                         │
                       │                  T12 ──> T13                 │
                       └──────────────────────────────────────────────┘

                       ┌──────────────────────────────────────────────┐
                       │          F2: Window Snapshots                │
                       │                                              │
                       │  T14 ──> T15(a,b,c) ──> T16(a,b,c)         │
                       │                           │                  │
                       │                           v                  │
                       │                     T17(a,b,c,d) ──> T19    │
                       │                           │                  │
                       │            T18 ───────────┘                  │
                       │                           │                  │
                       │                           v                  │
                       │                          T20                 │
                       └──────────────────────────────────────────────┘

                       ┌──────────────────────────────────────────────┐
                       │        F3: CLI-MCP Gap Closure               │
                       │                                              │
                       │  T21, T22, T23  (parallel) ──> T24 ──> T25  │
                       └──────────────────────────────────────────────┘

                       ┌──────────────────────────────────────────────┐
                       │       F4: CMM Validator Exposure             │
                       │                                              │
                       │  T26(a,b,c) ──> T27 ──> T28(a,b)           │
                       │       │                    │                 │
                       │       v                    v                 │
                       │      T29              T30 ──> T31           │
                       └──────────────────────────────────────────────┘

                       ┌──────────────────────────────────────────────┐
                       │       F5: Implementation Fixes               │
                       │                                              │
                       │  T32, T33(a,b), T34, T35(a,b,c)  (parallel)│
                       │              │                               │
                       │              v                               │
                       │            T36                               │
                       └──────────────────────────────────────────────┘
```

### Cross-Feature Dependencies

- F5.T35 (timeout params) should land before F1.T5 (background mode) to share the `timeout_ms` parameter pattern.
- F5.T32 (dict-based field lookup) is independent; can land first as a quick win.
- F2.T17 (window capture modes) enhances F1 job result reporting but is not a hard dependency.
- F4.T26a (reusable blocking detection) extracts logic currently in session_tools.spl, which F1.T5/T6 also use; land T26a early.

## Implementation Order (Recommended)

**Wave 1 — Foundation (parallel tracks)**
- F5: T32, T33, T34, T35 (quick fixes, low risk)
- F1: T1, T2 (class + state machine definition)
- F4: T26a (extract reusable blocking detection)

**Wave 2 — Core features**
- F1: T3, T4 (job manager operations)
- F2: T14, T15 (snapshot classes and store)
- F3: T21, T22, T23 (new tool handlers — independent)

**Wave 3 — Integration**
- F1: T5, T6, T7-T12 (background params, tool handlers, dispatcher)
- F2: T16, T17, T18, T19 (diff engine, capture modes, resources)
- F4: T26b-c, T27, T28, T29, T30 (validator modes)

**Wave 4 — Testing**
- F1: T13, F2: T20, F3: T24-T25, F4: T31, F5: T36

## Summary

| Feature | Tasks | Subtasks | Total Work Items | Est. Effort |
|---------|-------|----------|-----------------|-------------|
| F1: Job Manager | 13 | 13 | 26 | L (1-2 weeks) |
| F2: Window Snapshots | 7 | 10 | 17 | L (1-2 weeks) |
| F3: CLI-MCP Gap Closure | 5 | 0 | 5 | M (3-5 days) |
| F4: CMM Validator | 6 | 4 | 10 | M (3-5 days) |
| F5: Implementation Fixes | 5 | 5 | 10 | M (3-5 days) |
| **Total** | **36** | **32** | **68** | **~4-6 weeks** |

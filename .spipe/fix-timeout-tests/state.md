# SStack State: fix-timeout-tests

## User Request
> fix all fail tests

## Task Type
bug

## Refined Goal
> Fix all 15 test specs that fail with 120s timeout in the full test suite run. All failures are interpreter-mode timeout hangs, not logic errors. Root-cause each timeout and fix the test or the code it exercises so that `bin/simple test` exits cleanly with 0 failures.

## Failing Tests (all 120011-120069ms timeouts)
1. wiki_tool_spec.spl
2. github_release_spec.spl
3. run_diagnostics_contract_spec.spl
4. simple_portal_content_db_spec.spl
5. simple_portal_server_spec.spl
6. approval_broker_spec.spl
7. spm_service_spec.spl
8. winfs_shim_host_spec.spl
9. core_spec.spl (svim)
10. language_port_spec.spl
11. multi_buffer_split_spec.spl
12. simpleos_adapter_spec.spl
13. svim_ext_spec.spl
14. tui_shell_spec.spl
15. test_lens_spec.spl

## Acceptance Criteria
- [ ] AC-1: All 15 timeout tests either pass or are properly skipped with documented reason
- [ ] AC-2: No new test failures introduced
- [ ] AC-3: Root cause documented for each timeout (missing import, infinite loop, blocking I/O, etc.)
- [ ] AC-4: Fixes use interpreter-safe patterns (no named args, no chained methods, etc.)

## Cooperative Providers
- Codex: unavailable
- Gemini: unavailable

## Phase Checklist
- [x] 1-dev (Developer Lead) — 2026-05-20
- [ ] 2-research (Analyst)
- [ ] 3-arch (Architect)
- [ ] 4-spec (QA Lead)
- [ ] 5-implement (Engineer)
- [ ] 6-refactor (Tech Lead)
- [ ] 7-verify (QA)
- [ ] 8-ship (Release Mgr)

## Phase Outputs

### 1-dev
Task type: bug. 15 test specs all timeout at exactly 120s during `bin/simple test`. All are integration/service tests (editor, portal, VCS tools, OS adapters). No logic failures — pure timeout hangs. Need to research root causes (likely: blocking I/O waits, missing service dependencies, import loops, or interpreter hangs on specific patterns).

### 2-research
<pending>

### 3-arch
<pending>

### 4-spec
<pending>

### 5-implement
<pending>

### 6-refactor
<pending>

### 7-verify
<pending>

### 8-ship
<pending>

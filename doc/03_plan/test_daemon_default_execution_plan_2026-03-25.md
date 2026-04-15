# Test Daemon Default Execution Plan

**Date:** 2026-03-25
**Status:** Plan
**Depends on:** `doc/05_design/test_daemon_default_execution_design_2026-03-25.md`

---

## 1. Objective

Make daemon-backed execution the default `simple test` path, with exact-request merging inside the same folder scope and no merging across different folder scopes.

---

## 2. Acceptance Criteria

- `simple test` submits normalized requests to the daemon by default
- daemon deduplicates exact duplicate in-flight requests
- same-folder exact duplicates merge
- different-folder requests never merge
- daemon remains the owner of cache and dependency analysis
- direct execution remains available via explicit override or fallback

---

## 3. Phase Breakdown

### Phase 1: Request normalization and daemon routing

Deliverables:

- add daemon-default flags to test runner args
- add request normalization in client path
- add folder scope derivation
- make `simple test` use daemon by default

Files:

- `src/lib/nogc_sync_mut/test_runner/test_runner_args.spl`
- `src/lib/nogc_sync_mut/test_runner/test_runner_types.spl`
- `src/lib/nogc_sync_mut/test_runner/test_runner_main.spl`
- `src/app/test_daemon/client.spl`

Acceptance:

- request reaches daemon for normal `simple test`
- `--no-daemon` still runs direct path

### Phase 2: Exact request merge table

Deliverables:

- add normalized request key type
- add active execution table keyed by normalized request key
- add waiter tracking and fanout

Files:

- `src/app/test_daemon/types.spl`
- `src/app/test_daemon/daemon.spl`
- new merge-related modules if needed

Acceptance:

- identical same-scope requests merge
- result is fanned out correctly to all waiters

### Phase 3: Enforce folder-scope boundary

Deliverables:

- normalize folder scope for file and directory requests
- reject cross-scope merge candidates
- add status/debug output for scope-based merge decisions

Acceptance:

- `test/unit/` and `test/system/` never merge
- `test/unit/app/` and `test/unit/app/` may merge
- `test/unit/app/foo_spec.spl` and `test/unit/app/bar_spec.spl` do not merge unless full normalized key matches

### Phase 4: Move cache and dep-graph ownership fully to daemon

Deliverables:

- daemon performs freshness checks before scheduling
- client does not precompute standalone cache decisions
- remove duplicate decision-making from direct path when daemon is enabled

Acceptance:

- repeated daemon-backed requests do not duplicate cache analysis work

### Phase 5: Integrate session broker behind daemon-backed default

Deliverables:

- plug session-aware execution behind daemon scheduling
- first target: QEMU
- later targets: containers, services, hardware

Acceptance:

- daemon-backed execution is the single control plane for shared sessions

---

## 4. Detailed Work Items

### 4.1 Request key model

Add fields:

- `folder_scope`
- `requested_path`
- `mode`
- `filter`
- `tag`
- `level`
- `clean`
- `no_cache`
- `fail_fast`
- `execution_mode`
- `session_share`

Need helpers:

- normalize request path
- derive folder scope
- serialize request key

### 4.2 Client changes

Client should:

- build normalized request
- ensure daemon running
- submit request with folder scope and normalized options
- poll result

Client should not:

- decide merge locally
- own cache logic in daemon-backed mode

### 4.3 Daemon changes

Daemon should:

- receive normalized request
- compute request key
- check active execution table
- merge or enqueue
- run discovery/cache/dependency analysis once
- fan out result to all request ids

### 4.4 CLI changes

Add:

- `--no-daemon`
- `--daemon-only`
- `--no-merge`
- `--merge-debug`

Update help text accordingly.

---

## 5. Tests

### 5.1 Unit tests

Add unit coverage for:

- folder scope normalization
- request key equality
- exact merge decision
- cross-scope non-merge
- file path to parent-folder scope mapping

Suggested file:

- `test/unit/app/test_daemon/test_daemon_request_merge_spec.spl`

### 5.2 System tests

Add system coverage for:

- same command submitted twice merges
- same folder same options merges
- same folder different options does not merge
- different folder requests do not merge
- direct fallback path works when daemon startup fails

Suggested file:

- `test/system/test_daemon/test_daemon_default_execution_system_spec.spl`

---

## 6. Suggested Execution Order

1. Add request key and folder scope helpers
2. Wire `simple test` client path to daemon by default
3. Add exact in-flight merge table
4. Add cross-scope merge guard
5. Add tests
6. Move cache/dependency analysis fully under daemon ownership
7. Integrate session broker after daemon-default path is stable

---

## 7. Risks

### Risk: over-merging

Mitigation:

- exact normalized key only
- exact folder scope equality only

### Risk: result routing confusion

Mitigation:

- keep one execution id with multiple waiter request ids
- write individual response artifacts per waiter

### Risk: divergence between direct and daemon paths

Mitigation:

- keep direct path as fallback only
- move shared logic down into daemon-owned modules over time

---

## 8. Success Metrics

- concurrent duplicate requests cause one execution, not many
- repeated CLI runs from same folder stop duplicating startup work
- no accidental merge across `test/unit/` and `test/system/`
- daemon-backed path becomes normal behavior for developers

---

## 9. Immediate Next Step

Implement Phase 1 and Phase 2 together:

- add request normalization
- make daemon-backed mode default
- add exact same-scope in-flight request merge

That yields a useful behavior change immediately without waiting for session broker work.

# Test Daemon Default Execution Design

**Date:** 2026-03-25
**Status:** Design
**Scope:** Make daemon-backed execution the default path for `simple test`

---

## 1. Goal

Make `simple test` use the test daemon by default so repeated test requests can share:

- discovery work
- dependency graph work
- result cache state
- long-lived sessions such as QEMU, containers, services, and hardware adapters

At the same time, request merging must be conservative:

- duplicate or overlapping requests inside the same folder scope may merge
- requests from different folder scopes must not merge

Example:

- `simple test test/unit/app/`
- `simple test test/unit/app/test_daemon/foo_spec.spl`

These may merge under the `test/unit/app` scope.

But:

- `simple test test/unit/app/`
- `simple test test/system/`

These must not merge.

---

## 2. Current Problem

Today the codebase has:

- a test daemon
- standalone runner cache and dep-graph logic
- partial session-sharing support

But the default `simple test` path still runs directly in the standalone runner instead of delegating to the daemon.

That causes:

- duplicated discovery and dependency analysis across concurrent invocations
- no central request scheduling
- no real session ownership boundary
- no reliable place to merge repeated requests

---

## 3. Desired Behavior

### 3.1 Default user model

`simple test ...` should behave as:

1. parse CLI args
2. compute a normalized request
3. ensure daemon is running
4. submit request to daemon
5. daemon decides whether to:
   - serve from cache
   - merge onto an equivalent in-flight request
   - schedule new execution
6. client waits for final result or streamed progress

Direct in-process execution should remain available only as:

- fallback mode when daemon startup fails
- explicit override such as `--no-daemon`

### 3.2 Merge rule

Requests can merge only when all of these are true:

- same folder scope
- same normalized execution mode
- same filter/tag selection
- same clean/cache policy
- same sharing-sensitive options

Requests must not merge when folder scopes differ, even if one path lexically overlaps another.

Reason:

- folder path is the execution ownership boundary
- different folders often represent different intent, different runtime categories, and different cache invalidation domains

---

## 4. Folder Scope Model

### 4.1 Scope definition

Every request gets a `folder_scope`.

Rules:

- if request path is a directory, `folder_scope = normalized directory path`
- if request path is a file, `folder_scope = parent directory of file`
- if request path is omitted, `folder_scope = test/`

Examples:

- `test/` -> `test/`
- `test/unit/` -> `test/unit/`
- `test/unit/app/foo_spec.spl` -> `test/unit/app/`
- `test/system/test_daemon/` -> `test/system/test_daemon/`

### 4.2 Merge safety rule

Use exact normalized folder scope equality.

Do not merge by ancestor/descendant containment.

Examples:

- `test/unit/app/` and `test/unit/app/` -> merge allowed
- `test/unit/app/foo_spec.spl` and `test/unit/app/bar_spec.spl` -> merge allowed only if normalized request shape matches and both resolve to `test/unit/app/`
- `test/unit/app/` and `test/unit/` -> do not merge
- `test/unit/` and `test/system/` -> do not merge

This is intentionally conservative.

---

## 5. Request Model

Add a normalized request type in the daemon layer.

```text
TestRequestKey
- folder_scope
- requested_path
- request_kind
- mode
- filter
- tag
- level
- clean
- no_cache
- fail_fast
- session_share
- execution_mode
```

Important distinction:

- `requested_path` is what the user asked for
- `folder_scope` is the merge boundary

Two requests may share a `folder_scope` but still not merge if their normalized options differ.

---

## 6. Merge Semantics

### 6.1 Types of merging

#### Exact merge

If two requests have the same `TestRequestKey`, the second request attaches to the first in-flight execution.

Use case:

- two terminals run `simple test test/unit/app/ --mode=interpreter`

#### Superset merge

Not in phase 1.

Example:

- request A: `test/unit/app/`
- request B: `test/unit/app/foo_spec.spl`

Even though B is contained inside A's scope, do not merge automatically in phase 1. Exact-merge only is safer.

This keeps the implementation simple and avoids partial-result routing complexity.

### 6.2 Result fanout

If multiple clients attach to the same in-flight request:

- daemon stores one execution record
- daemon tracks multiple waiters
- final result is written once per request id, or derived fanout responses are generated from the shared execution result

### 6.3 No cross-scope merge

The daemon must reject merge candidates when:

```text
candidate.folder_scope != request.folder_scope
```

This rule is absolute.

---

## 7. Daemon-Owned Execution

### 7.1 Responsibilities moved into daemon

The daemon should own:

- test discovery
- dependency graph analysis
- result cache access
- in-flight deduplication and merging
- session broker access
- execution scheduling

The thin client path should own:

- CLI argument parsing
- request normalization
- daemon bootstrap
- progress display

### 7.2 Why daemon must own cache and merge

If the runner process owns discovery and cache before daemon submission, then:

- repeated requests still duplicate work
- request merging happens too late
- two clients may both decide to run the same request

So the daemon must be the first owner of normalized test requests.

---

## 8. Scheduling Model

### 8.1 Request table

Daemon keeps:

```text
active_requests: {request_key -> execution_id}
executions: {execution_id -> execution_state}
waiters: {execution_id -> [request_id]}
```

### 8.2 Execution state

```text
ExecutionState
- execution_id
- request_key
- status
- started_at
- finished_at
- result_summary
- output_log
- session_refs
```

### 8.3 Queue policy

Per folder scope:

- allow one active execution per exact request key
- allow multiple unrelated requests in same scope only if scheduler policy permits
- merge exact duplicates

Global:

- normal tests may run in parallel
- session-bound tests may be constrained by adapter limits

---

## 9. CLI Model

Default:

- `simple test ...` uses daemon

Explicit controls:

- `--no-daemon` forces direct execution
- `--daemon-only` fails if daemon path unavailable
- `--no-merge` disables request merge for that invocation
- `--merge-debug` prints merge decision

Keep:

- `simple test-daemon start`
- `simple test-daemon stop`
- `simple test-daemon status`

Extend status to report:

- active executions
- merged waiter counts
- executions by folder scope

---

## 10. Config Model

Add to `config/simple.test.sdn`:

```sdn
daemon_default: true
daemon_fallback_direct: true
merge_exact_requests: true
merge_cross_scope: false
```

Recommended hard invariant:

- `merge_cross_scope` must remain false

This should not become a permissive toggle without a stronger scheduler and proof that result routing stays correct.

---

## 11. Failure Handling

### 11.1 Daemon unavailable

If daemon startup fails:

- if fallback enabled, run direct and print warning
- if `--daemon-only`, fail fast

### 11.2 Merged execution fails

All attached waiters receive the same failure result for that normalized request.

### 11.3 Client disconnect

Client disconnect must not kill the shared execution unless:

- it is the last waiter
- and policy says orphaned executions should be cancelled

Phase 1 recommendation:

- execution continues to completion once started

---

## 12. Implementation Shape

### 12.1 New daemon concepts

Proposed files:

- `src/app/test_daemon/request_key.spl`
- `src/app/test_daemon/request_merge.spl`
- `src/app/test_daemon/execution_table.spl`

### 12.2 Existing files to update

- `src/app/test_daemon/types.spl`
- `src/app/test_daemon/daemon.spl`
- `src/app/test_daemon/client.spl`
- `src/app/io/cli_commands.spl`
- `src/lib/nogc_sync_mut/test_runner/test_runner_args.spl`
- `src/lib/nogc_sync_mut/test_runner/test_runner_main.spl`

### 12.3 Non-goal for phase 1

Do not implement:

- hierarchical subset merge
- partial result reuse across parent/child folder requests
- speculative shared discovery across unrelated scopes

---

## 13. Decision

Make the test daemon the default execution backend for `simple test`.

Merge only exact normalized requests inside the same normalized folder scope.

Do not merge requests across different folder scopes.

This gives:

- predictable semantics
- a single control point for cache and sessions
- a safe foundation for future session-sharing and execution pooling


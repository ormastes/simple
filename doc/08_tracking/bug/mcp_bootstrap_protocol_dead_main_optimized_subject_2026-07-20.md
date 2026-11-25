# `bootstrap_protocol_test.spl` shells out to a deleted file: `src/app/mcp/bootstrap/main_optimized.spl`
## Open 2026-09-16 — needs owner triage

Reviewed in the 2026-09-16 bug-ledger normalization pass; no resolution
evidence found in the body. This is bookkeeping, not verification.

**Date:** 2026-07-20
**Component:** `test/feature/lib/mcp/bootstrap_protocol_test.spl` (test subject,
not the interpreter/compiler)
**Severity:** Low — the test's subject file no longer exists in the tree; the
test cannot exercise anything until a maintainer decides its replacement.

## Symptom

Running the spec on the deployed binary:

```
SIMPLE_RUST_SEED_WARNING=0 timeout 90 \
  bin/release/x86_64-unknown-linux-gnu/simple test \
  test/feature/lib/mcp/bootstrap_protocol_test.spl --no-session-daemon
```

fails both protocol checks with:

```
Exit code: 1
✗ Bootstrap failed
Output: error: compile failed: io: Cannot read "src/app/mcp/bootstrap/main_optimized.spl": No such file or directory (os error 2)
```

## Root cause

The spec's entire mechanism is:

```simple
val result = shell("bin/simple run src/app/mcp/bootstrap/main_optimized.spl < /tmp/mcp_test_input.txt 2>&1")
```

`src/app/mcp/bootstrap/` does not exist at all in the current tree (verified:
`ls src/app/mcp/bootstrap/` → "No such file or directory"), and no file named
`main_optimized.spl` exists anywhere in `src/` (`find src -iname
'*main_optimized*'` → empty). The bootstrap-optimization subject this spec was
written against has been deleted/renamed away with no direct successor file;
`src/app/mcp/` now ships `main.spl`, `main_dispatch.spl`,
`main_lazy_protocol.spl`, `main_static_tools.spl`, etc., none of which is a
drop-in rename of `main_optimized.spl`.

Note: `app.io.mod`'s `shell()`/`file_write()` used by the spec DO still exist
and resolved/executed correctly here (the subprocess ran, returned exit code
1, and `result.stdout`/`result.exit_code` were read fine via `??`) — so this
is not an API-drift issue on the harness side, only a missing subject file.

## Why this is not fixed as a stale-test rename

There is no single current file that is an unambiguous successor to
`main_optimized.spl`'s subprocess-level "start the optimized bootstrap
server and feed it real JSON-RPC over stdin" behavior. Picking one of
`main.spl`/`main_dispatch.spl`/`main_lazy_protocol.spl` and rewriting the
test around it would materially change what the test verifies (and could
silently drop coverage), which is out of scope for a mechanical
import-path-rename triage pass. Left RED, not weakened.

## Suggested next step

A maintainer familiar with the MCP bootstrap consolidation should either:
- point the spec at the correct current stdio-protocol entry point (likely
  `src/app/mcp/main.spl` or `main_lazy_protocol.spl`), or
- retire the spec if subprocess-level JSON-RPC protocol coverage is now
  provided by `test/feature/lib/mcp/working_check.spl` /
  `integration_spec.spl` (in-process, no missing subject).

Affected: `test/feature/lib/mcp/bootstrap_protocol_test.spl` only.

## Resolution 2026-11-25 — FIXED (Option A: repoint at the live stdio entry point)

**Option chosen: A.** The spec keeps its unique subprocess-level JSON-RPC
coverage (real server process, framed requests on stdin, framed responses on
stdout); `working_check.spl` / `integration_spec.spl` are in-process and do
not replace that surface, so retiring the spec (Option B) would have dropped
coverage.

**Findings during the fix (branch `release/1.0.0` state):**

- The spec had already been repointed from the dead
  `src/app/mcp/bootstrap/main_optimized.spl` to the live stdio entry point
  `src/app/mcp/main.spl` (both copies: `test/feature/lib/mcp/` and
  `test/03_system/feature/lib/mcp/`). `src/app/mcp/bootstrap/` also exists
  again in this branch, so the literal dead-subject condition no longer held.
- The spec was still RED on a Windows host for two harness-drift reasons,
  verified by replaying the inner command by hand:
  1. `file_write("/tmp/mcp_test_input.txt", ...)` is a native call and wrote
     `C:\tmp\mcp_test_input.txt`, while `shell()` resolves to MSYS `sh` on
     Windows, whose `< /tmp/mcp_test_input.txt` reads the MSYS temp dir —
     `sh: line 1: /tmp/mcp_test_input.txt: No such file or directory`,
     exit 1, empty stdout. (On Linux both views agree, which is why the
     original failure there was only the dead subject.)
  2. Even with the file reachable, `2>&1` merged compiler-runner stderr
     diagnostics (`[engine-demotion] ... Module error: unresolved external
     symbol ...`, JIT fallback) into the asserted output, tripping the
     `output.contains("error: ") == false` check without any server error.

**Fix applied to both spec copies** (no assertion weakened):

- Requests are fed via a stdin heredoc inside the single `shell()` call —
  the write and the read now always share one shell's path view; the `/tmp`
  temp file is gone entirely.
- The server binary is the tracked per-OS entry point: `bin/simple.exe` on
  Windows, `bin/simple` elsewhere (forward slashes are correct because
  `shell()` resolves to a POSIX sh on Windows whenever one is installed).
- Streams are asserted separately: stdout must contain all three
  `"id":"N","result"` responses, `protocolVersion`, `capabilities`, `tools`,
  and no `error: ` line; stderr must contain no `[error]` (the server's own
  `_mcp_error` marker — this keeps the stderr error coverage the old `2>&1`
  merge provided, without failing on compiler-runner noise).

**Evidence** (`SIMPLE_LIB=src bin/simple.exe test <spec> --mode=interpreter`,
self-hosted tracked binary, worktree root):

- BEFORE: `outcome=ERROR declared>=1 executed=1 passed=0 failed=1` —
  `expected 1 to equal 0` (exit code) plus all seven content checks false.
- Manual replay of the live server (`bin/simple.exe run src/app/mcp/main.spl`
  with the spec's framed input): exit 0, `"id":"1","result"` with
  `protocolVersion`, `"id":"2","result"` with the tools array,
  `"id":"3","result"` with the `simple_status` content — the protocol surface
  the spec checks is genuinely answered by the current server.
- AFTER: both copies
  `outcome=OK declared>=1 executed=1 passed=1 failed=0`.

Files changed: `test/feature/lib/mcp/bootstrap_protocol_test.spl`,
`test/03_system/feature/lib/mcp/bootstrap_protocol_test.spl`.

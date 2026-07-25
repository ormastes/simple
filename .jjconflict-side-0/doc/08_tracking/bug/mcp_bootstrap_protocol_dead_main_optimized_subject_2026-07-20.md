# `bootstrap_protocol_test.spl` shells out to a deleted file: `src/app/mcp/bootstrap/main_optimized.spl`

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

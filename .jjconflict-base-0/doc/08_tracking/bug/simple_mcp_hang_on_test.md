# Bug: simple-mcp hangs on simple_test tool call

Status: **RESOLVED** (2026-05-29) — Fixed in `src/app/mcp/cli_passthrough.spl` by

**Date:** 2026-05-27
**Severity:** medium
**Component:** simple-mcp server

## Symptom

Calling `mcp__simple-mcp__simple_test` with a `path` parameter causes the MCP
server to hang indefinitely. The tool never returns a response.

## Reproduction

```
mcp__simple-mcp__simple_test(path: "test/05_perf/bench/fat32_vs_cfat_bench.spl")
```

The call blocks until the client-side timeout fires.

## Context

- `bin/simple --version` reports `Simple v0.9.8`
- `bin/simple test --list` returns exit code 0 (no output)
- `bin/simple <file.spl>` returns exit code 3 with no stdout/stderr for any file
- The interpreter exit-code-3 issue is pre-existing (not caused by source edits)
- Log at `.simple/logs/simple.log.2026-05-26` shows module parse warnings but
  no fatal errors; no new log entries are written on the exit-code-3 runs

## Root Cause

`rt_process_run` in the compiled binary (`runtime_native.c`) is implemented via
`popen()`, which reads from the child's stdout pipe until EOF. `bin/simple test`
spawns async test worker processes (`spawn_tracked_process` in
`test_runner_async.spl`). These workers inherit the stdout of their ancestor
shell (which holds the popen pipe's write end). Even after `timeout` kills the
top-level `bin/simple` process, the surviving worker children keep the pipe
write end open. `popen`'s `fgets` loop never sees EOF, so the MCP server hangs
indefinitely.

The previous "fix" (120s timeout + `--timeout 60`) only masked the symptom —
the server would still hang for 120s on every `simple_test` call that runs real
tests. It did not address the pipe-inheritance cause.

## Fix

In `cli_passthrough.spl`, the `simple_test` dispatch now wraps the command to
redirect its output to a `mktemp` temp file instead of the popen pipe:

```shell
tmp=$(mktemp /tmp/simple_mcp_test_XXXXXX)
{ timeout 120 bin/simple test <args> < /dev/null; } > "$tmp" 2>&1
EC=$?; cat "$tmp"; rm -f "$tmp"; exit $EC
```

Async test worker children now inherit a **file fd** for stdout/stderr, not the
popen pipe. When `timeout` kills `bin/simple`, workers may linger but they hold
a temp file open — not the popen read pipe. `cat` runs after the command group
finishes, popen reads only `cat`'s output (brief), and `pclose` returns
immediately. The MCP server is unblocked.

`mktemp` ensures concurrent `simple_test` calls use distinct temp files.

## Status

**RESOLVED** (2026-05-29) — Fixed in `src/app/mcp/cli_passthrough.spl` by
redirecting `simple_test` subprocess output to a temp file, breaking the
popen-pipe inheritance chain.

# Bug: simple-mcp hangs on simple_test tool call

**Date:** 2026-05-27
**Severity:** medium
**Component:** simple-mcp server

## Symptom

Calling `mcp__simple-mcp__simple_test` with a `path` parameter causes the MCP
server to hang indefinitely. The tool never returns a response.

## Reproduction

```
mcp__simple-mcp__simple_test(path: "test/perf/bench/fat32_vs_cfat_bench.spl")
```

The call blocks until the client-side timeout fires.

## Context

- `bin/simple --version` reports `Simple v0.9.8`
- `bin/simple test --list` returns exit code 0 (no output)
- `bin/simple <file.spl>` returns exit code 3 with no stdout/stderr for any file
- The interpreter exit-code-3 issue is pre-existing (not caused by source edits)
- Log at `.simple/logs/simple.log.2026-05-26` shows module parse warnings but
  no fatal errors; no new log entries are written on the exit-code-3 runs

## Likely Root Cause

The MCP server dispatches to `bin/simple test` internally. The interpreter
silently exits with code 3 before producing output, but the MCP server does not
detect the early exit and keeps waiting for stdout.

## Status

**RESOLVED** — `simple_test` now has a 120 second MCP wrapper timeout and passes
`--timeout 60` to the Simple test runner by default. The tool schema also
accepts an explicit `timeout` parameter for callers that need a different
per-test budget.

This makes hung test subprocesses return a timeout result to the MCP client
instead of waiting for the previous 600 second wrapper budget.

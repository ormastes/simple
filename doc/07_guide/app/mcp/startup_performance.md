# MCP / Tool-Server Startup Performance Guide

Date: 2026-06-10. Measurements taken on linux x86_64 at commit `b2b4cff6e4`.

## Why this guide

`bin/simple_mcp_server` answered a framed `initialize` + `tools/list`
handshake in **2722 ms** while `bin/simple_lsp_mcp_server` did it in **51 ms**.
Both are native servers behind the same wrapper pattern. The gap is not the
language or the runtime — it is *how much work happens before the first
response* and *how many times that work happens*.

## Measured breakdown (2026-06-10)

| Path | Handshake time | Note |
|------|---------------|------|
| `build/bootstrap/mcp-package/simple_mcp_server` (direct) | 1361 ms | chosen candidate, 151 tools, 38 KB tools/list |
| `bin/release/<triple>/simple_mcp_server` (direct) | 5 ms | stale: fails probe (missing wm-text tools) |
| `bin/simple_mcp_server` (wrapper) | 2722 ms | = probe handshake (1361) + real exec (1361) |

The wrapper **probes the native candidate with a full handshake on every
start** (`mcp_probe_native`), then execs the same binary again. Cold startup
is paid twice. That is the single largest cost today, ahead of anything the
library layering can save.

## The startup-reduction ladder (apply in this order)

1. **Measure before changing anything.** `scripts/check/check-mcp-native-smoke.shs`
   prints `mcp_startup_ms`; `scripts/check/check-startup-size-performance-audit.shs`
   gives cold-start, size, deps, RSS. Time the binary *directly* and through
   the wrapper — if the two differ ~2×, the wrapper is re-doing work.
2. **Don't start twice.** Probe/health-check results must be cached, keyed by
   binary path + mtime + size (a stamp file under `.simple/cache/`). Re-probe
   only when the binary changes. Expected win here: ~50% of wrapper startup.
3. **Execute compiled artifacts, not raw source.** Production wrappers exec
   cached native/SMF artifacts (`.claude/rules/code-style.md` rule). The
   native-vs-interpreted gap is 10–100×. Fail closed: if no valid artifact,
   that is a deploy bug, not a reason to silently interpret.
4. **Defer everything the first response does not need.** `initialize` needs
   no tool schemas; build the tool registry lazily on first `tools/list`, or
   serve it from a build-time-generated static table. Module-level init that
   touches files/process/env at import time is a startup tax on every run.
5. **Load interfaces, not bodies.** The SHB interface cache with source-mtime
   validity (landed via rt-forward-interface-cache-mcp-startup) lets imports
   resolve from cached interfaces and defer full module bodies until called.
6. **Shrink the import graph (lib layering).** Importing one helper must not
   drag in a subsystem. The core / thin-host / full split
   (`doc/03_plan/lib/host_io_layering/plan.md`) keeps app entrypoints on
   `std.io_runtime`-class thin facades so the eager graph stays small.
7. **Background-compile for script paths.** dynSMF
   (`src/os/smf/dynsmf_session.spl`, autoload policy spec) starts interpreted
   *now* and compiles SMF in the background for the *next* run.
8. **Keep-warm / daemon mode (last resort).** If cold start cannot shrink
   further, keep the server resident and reconnect. Adds lifecycle complexity;
   only after 1–7 are exhausted.

Rules of thumb: fixes that *remove* work (2, 4, 5, 6) beat fixes that *move*
work (7, 8); and a wrapper-level duplication (2) can negate every server-side
win, so always re-measure through the wrapper.

## Where the lib layering fits

The thin host-wrapper layer is the *prevention* mechanism, not the headline
cure: it keeps new code from re-growing the eager import graph and makes the
deferred-body fast path (step 5) effective, because interfaces of thin
wrappers are tiny and stable. The immediate cures for the current 2.7 s are
step 2 (probe cache) and step 4 (lazy tool registry).

## No-timeout policy

Startup gates (5000 ms in `check-mcp-native-smoke.shs`) bound *startup*, never
*idle*. MCP stdio servers block forever waiting for the next message; never
add read timeouts to transport reads, and never route script startup through
compile/JIT as a workaround for a slow fast path — fix the fast path or file
a bug.

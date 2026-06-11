# MCP / Tool-Server Startup Performance Guide

Date: 2026-06-11. Latest re-verification taken on linux x86_64 in the shared
repo worktree after the rt-forward/interface-cache MCP fixes were pushed on
2026-06-10.

## Why this guide

`bin/simple_mcp_server` now answers a framed `initialize` + `tools/list`
handshake in **1366 ms** while `bin/simple_lsp_mcp_server` does it in **50 ms**
on the current local deploy. Both are native servers behind the same wrapper
pattern. The remaining gap is not the language or the runtime — it is *how
much work happens before the first response* and *how many times that work
happens*.

## Measured breakdown (2026-06-11)

| Path | Handshake time | Note |
|------|---------------|------|
| `build/bootstrap/mcp-package/simple_mcp_server` (direct) | about 1360 ms | chosen candidate, 151 tools, 38 KB tools/list |
| `bin/release/<triple>/simple_mcp_server` (direct) | 5 ms | stale: fails probe (missing wm-text tools) |
| `bin/simple_mcp_server` (wrapper, cold stale-stamp re-probe) | about 2720 ms | = probe handshake + real exec |
| `bin/simple_mcp_server` (wrapper, warm cached stamp) | 1366 ms | current steady-state local deploy |

The wrapper used to probe the native candidate with a full handshake on every
start. The rt-forward/interface-cache startup fix changed that to a
**probe-stamp cache keyed by binary path + mtime + size + wrapper version**.
Cold stale-stamp starts still pay the double cost once; warm starts now skip
the extra handshake. That remains the single biggest wrapper-level win, ahead
of anything library layering can save.

## The startup-reduction ladder (apply in this order)

1. **Measure before changing anything.** `scripts/check/check-mcp-native-smoke.shs`
   prints `mcp_startup_ms`; `scripts/check/check-startup-size-performance-audit.shs`
   gives cold-start, size, deps, RSS. Time the binary *directly* and through
   the wrapper — if the two differ ~2×, the wrapper is re-doing work.
2. **Don't start twice.** Probe/health-check results must be cached, keyed by
   binary path + mtime + size plus wrapper version (a stamp file under
   `.simple/cache/`). Re-probe only when the binary or wrapper contract
   changes. Expected win here: about 50% of wrapper startup on warm runs.
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
   The executable regression for this is now
   `test/01_unit/compiler/interpreter/module_loader_lazy_spec.spl`, backed by
   `test/01_unit/compiler/cache/shb_mtime_spec.spl` and
   `test/02_integration/watcher/watcher_shb_integration_spec.spl`.
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

## Wave-1 results (2026-06-10)

Completed W1-C (primitive json perf) and W1-D (mcp import reduction).

**W1-C — json hot-loop fix.**
`mcp_sdk/core/json.spl` `find_text` delegated to native `index_of` (was
O(n·m) per-char substring slices). Benchmark:
`test/05_perf/mcp_json_perf_spec.spl` — 85× on 2 KB payload.

**W1-D — mcp import narrowing.**
`src/app/mcp/` narrowed `common.ui.access` hub → direct submodule imports;
dead `dap_bridge` re-import removed.
Result: loaded modules 61 → 49, module-load time 130 ms → 72 ms.
Interpreter handshake: ~0.52 s (was ~0.55 s).

Remaining handshake cost is mostly native process startup plus MCP app import
and tool-table work. Current local evidence from
`scripts/check/check-mcp-native-smoke.shs`:

- `mcp_startup_ms=1366`
- `lsp_mcp_startup_ms=50`
- `mcp_second_start_ok=true`
- `mcp_stale_stamp_reprobe_ok=true`
- `rt_forward_cache_valid=true`

That is the baseline to preserve when touching `src/app/mcp`,
`src/app/simple_lsp_mcp`, `src/compiler/**`, or `src/lib/**`.

**Diagnosis knobs:**

```bash
SIMPLE_LOADER_TRACE=1 bin/simple run src/app/mcp/main.spl   # module load trace
SIMPLE_PROFILE=1      bin/simple run src/app/mcp/main.spl   # interpreter profile
bin/simple deps normal src/app/mcp/main.spl                 # exclusive/shared per import
```

`bin/simple deps` (`doc/07_guide/compiler/deps_tool.md`) is now the primary
tool for diagnosing import graph costs before and after narrowing refactors.

## Wave-2 results (2026-06-10, W2-B2 closure reductions)

Three import reductions landed on the `src/app/mcp/main.spl` handshake
closure, found and verified with `bin/simple deps deep`:

1. `std.log` (659 code lines for 3 `error()` calls) → local `_mcp_error`
   over the new `std.nogc_sync_mut.io.stderr_ops` facade (12 lines; keeps
   the direct-rt gate clean — apps must not declare `rt_*` externs).
2. `std.cli.log_modes` (174 lines) → local `src/app/mcp/mcp_log_options.spl`.
3. `dap_bridge → std.nogc_sync_mut.debug.remote.session_model` (561 lines,
   planned in Wave 1 but never landed) → local `src/app/mcp/dap_types.spl`.

Closure: 39 → 38 files, 9,031 → ~8,350 code lines, ~309 → ~276 KB est.
native. Measured via `scripts/check/check-mcp-native-smoke.shs`:
`mcp_startup_ms` 2707 → **1309–1314** (warm, exit 0, all six direct-rt
gates true, framing valid, 151 tools). The pattern generalizes: run
`bin/simple deps deep <entry>` on any tool-server entry and inline or
localize single-consumer subtrees before reaching for caching.

## No-timeout policy

Startup gates (5000 ms in `check-mcp-native-smoke.shs`) bound *startup*, never
*idle*. MCP stdio servers block forever waiting for the next message; never
add read timeouts to transport reads, and never route script startup through
compile/JIT as a workaround for a slow fast path — fix the fast path or file
a bug.

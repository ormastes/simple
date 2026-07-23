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

## 2026-06-12 update — the hotspot is tools/list construction, not load

Direct phase-timing of `build/bootstrap/mcp-package/simple_mcp_server` corrected
the earlier attribution:

| Phase | Time |
|-------|------|
| start → `initialize` response | ~0 ms (262 B, 9 file opens, no .spl/.smf reads) |
| `initialize` → `tools/list` response | ~1.5 s, 100% user CPU, 11.5 MB RSS |

gdb stack samples (0.4/0.8/1.2 s) all land in one function with
`__memcpy_avx_unaligned_erms` underneath: repeated full-buffer string copies plus a
per-character loop — the O(n²) concat/escape pattern building the 38 KB tools/list
JSON. 38 KB should cost ~10 ms, not 1500 ms. "Before the first response" in the
old framing is really "before the first *tools/list* response".

Landed since (plan `doc/03_plan/app/mcp/mcp_startup_perf_small_tasks_2026-06-12.md`):
`--probe` self-check flag (version/tool-count/manifest-hash, no handshake), wrapper
cheap-probe fast path with full-handshake fallback, table-driven
`_mcp_static_tools_result()` (byte-identical output), 11 redundant startup imports
dropped, `mcp_sdk/core` no longer pulls `shell.spl` into every consumer.

Next steps, no interface change: (a) build-time pre-escaped literal tools/list
manifest — expected ~1.5 s → tens of ms; (b) parts-array + single join where JSON
must be built at runtime; (c) fix rt string primitives (concat realloc-copy, O(i)
char_at in escape loops) — a general script-perf win; (d) rebuild mcp-package with
the above and re-measure.

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

## 2026-07-01 — script-mode parity gate

Codex, Claude, and Gemini should launch the repo MCP scripts, but the scripts
must not force `SIMPLE_MCP_TOOL_SET=all`; `auto` is the fast default and keeps
dispatch callable. The focused diagnostic is:

```bash
sh scripts/check/check-mcp-script-mode-perf.shs
MCP_SCRIPT_PERF_STRICT=1 sh scripts/check/check-mcp-script-mode-perf.shs
```

Current local result is still a fail against Python/Bun cold-stdio comparators:
`simple_mcp` source/script median ~365 ms, `simple_lsp_mcp` ~60 ms, Python3
~26 ms, Bun ~34 ms. Track the remaining gap in
`doc/08_tracking/bug/mcp_script_mode_python_bun_parity_2026-07-01.md`.

## 2026-06-13 — core-default + dynload upgrade

The tools list now defaults to an `auto` mode that cuts handshake time by
erasing the tools/list JSON build from the critical path. The initialize
response declares `"tools":{"listChanged":true}`, then the first tools/list
serves only the 20-tool core set (~0.07 s), and the server emits a single
`notifications/tools/list_changed` once that notification is flushed.
Clients respecting the notification upgrade to the full 151-tool list on
the next tools/list call, which now returns a cached result (built once per
process in `main_static_tools.spl`).

Three tool-set modes are choosable via `--tool-set=` flag or env
`SIMPLE_MCP_TOOL_SET` (note: env path currently broken in the native binary;
see `doc/08_tracking/bug/native_env_get_raw_pointer_2026-06-12.md`):

| Mode | First tools/list | Behavior | Use case |
|------|------------------|----------|----------|
| `auto` (default) | core 20 tools | upgrades to full 151 after emit list_changed | MCP clients that handle dynamic list updates |
| `all` | full 151 tools | static; no list_changed | simplifies client stubs, pays full JSON cost upfront |
| `core` | core 20 tools | never upgrades | minimal surface, e.g., lightweight embedded clients |

Dispatch remains unfiltered: all 151 tools stay callable by name in every
mode, so stale clients are still safe. Invalid set values default to `auto`.

Measured on 2026-06-13 (`build/bootstrap/mcp-package/simple_mcp_server`):
`auto` = 0.067 s handshake, `all` = 1.504 s (dominated by native rt-call
overhead per `doc/08_tracking/bug/rt_string_concat_quadratic_2026-06-12.md`),
`core` = 0.067 s. The full-list JSON cache and one-shot list_changed
notification combine to save the 1.4 s tools/list JSON build on warm clients
that upgrade.

### Smoke verification of the core-first protocol

`scripts/check/check-mcp-native-smoke.shs` validates this two-phase behaviour
without conflating it with the timing gate:

- The **timed** run pipes `initialize` + one `tools/list` and measures only the
  fast core handshake (`mcp_startup_ms`, gated `<= 5000 ms`).
- A separate **untimed functional** run pipes `initialize` + **two** `tools/list`
  calls so the server emits `notifications/tools/list_changed` and serves the
  full set on the second call. It runs *after* both timed start runs so it never
  perturbs the start-timing gates.
- `scripts/check/validate_mcp_native_smoke.spl` selects the **last frame
  containing `"tools":`** (`last_tools_payload`) rather than the final frame, so
  the trailing `list_changed` notification does not hide the full tool list. The
  full-set assertions (`mcp_tools_count` = 151, schema valid, `play_wm_text_*`
  present) and the stale-stamp re-probe check all read this functional capture.

A validator that assumes the tools/list response is the final frame reports
`mcp_tools_count=0` against a core-first server even though the output is valid;
the content-based frame selection above is the robust fix.

## 2026-07-23 — local pure-Simple recovery deployment

The locally deployed
`bin/release/x86_64-unknown-linux-gnu/simple_mcp_server` passed a bounded framed
`initialize`/`tools/list` sanity check as a compiled pure-Simple artifact. Its
SHA-256 is
`e189b71947d0ceaa29c6a0a2dac65c6e11a75f37403d2fe1ae19577da1a24212`.
Keep production launch native-first with no silent source or Rust-seed fallback.

The temporarily deployed Stage 2 compiler is recovery-only: it can rebuild
native artifacts, but it does not provide the Stage 4 `run`, `test`, or SPipe
docgen surface and is not full-CLI or release evidence. Promotion still requires
the fresh Stage 4 essential-tools smoke and the bootstrap MCP acceptance gate.

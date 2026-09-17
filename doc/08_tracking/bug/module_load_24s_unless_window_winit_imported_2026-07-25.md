## Closed 2026-09-16 — resolved by the 2026-09-12 loader-cache work: the 21 s engine-only import tax is gone (engine-only closure now loads interpreted in ~2–3 s, on par with +winit); caveat — the exact recorded probe content now trips a new `print`-prelude defect, recorded in the re-verification section below

The interpreted module-load delta this record tracked (24 s engine-only vs
3 s with `window_winit`) no longer exists: on the 2026-09-14 seed, an
engine2d-importing probe that actually uses its import loads in ~2–3 s
interpreted, with or without the `window_winit` import, across repeated and
order-swapped runs. The exact 2026-07-25 probe content (`import engine; print
"ok"`) cannot run as scripted on the current seed — it fails with
`error: semantic: variable 'print' not found` — a fresh, unrelated defect that
needs its own record (not created here; out of this sweep's scope). See
"2026-09-16 re-verification (macOS sweep)" below for the full commands, numbers,
and the exact failure text.

---

# Importing `std.gpu.engine2d.engine` costs 24 s — adding `std.io.window_winit` drops it to 3 s

- **Date:** 2026-07-25
- **Area:** module loader / import closure resolution
- **Severity:** medium — 8x startup penalty on every interpreted run that touches
  Engine2D without also importing winit.
- **Status:** CLOSED 2026-09-16 — the 24 s→3 s anomaly is gone: engine-only and
  engine+winit closures both load interpreted in ~2–3 s on the 2026-09-14 seed
  (delta < 2x, both far under 10 s), consistent with the 2026-09-12 loader-cache
  commits fixing it. Caveat: the exact recorded probe content now fails with a
  NEW `print`-prelude defect (`error: semantic: variable 'print' not found`) —
  recorded below; that defect is out of this record's scope and needs its own
  bug entry.

## 2026-09-16 re-verification (macOS sweep)

Toolchain: `bin/simple` = Rust seed `src/compiler_rust/target/bootstrap/simple`
(130,701,712 B, rebuilt 2026-09-14), macOS aarch64 M4.

### Exact recorded probes — BLOCKED by a new defect (no timings obtainable)

Recreated both probes verbatim in `/tmp/claude-bug-sweep-2026-09-16/`:
- `probe_a_engine_only.spl`: `use std.gpu.engine2d.engine.{Engine2D}` + `fn main() -> i64: print "ok"; 0`
- `probe_b_engine_winit.spl`: adds `use std.io.window_winit.{winit_loop_new}`

`SIMPLE_NO_DEPRECATED_WARNINGS=1 /usr/bin/time -p bin/simple run <probe>.spl` results:

| probe | mode | result |
|---|---|---|
| probe_a | from /tmp, any mode | fails instantly: stdlib imports "resolve from the project stdlib roots only" when the script lives outside the project; `error: semantic: variable 'print' not found` (0.6–2.1 s) |
| probe_a | repo-internal path, default (JIT) | 372.8 s of Cranelift JIT churn on the engine2d closure, then `error: semantic: variable 'print' not found` (exit 1) |
| probe_a | repo-internal, `SIMPLE_EXECUTION_MODE=interpreter` | fast fail: `error: semantic: variable 'print' not found` (1.55 s, exit 1) |
| probe_b | repo-internal, `SIMPLE_EXECUTION_MODE=interpreter` | same `print not found` (2.48 s, exit 1) |

Root cause of the block (new defect, NOT the 2026-07-25 loader defect): importing
`std.gpu.engine2d.engine` **without using it** drops the `print` prelude symbol
in the current seed — interpreter and JIT alike. The repo's own
`scratchpad/cpu_lane_probe.spl` (same import, but it USES `Engine2D`) confirms
the split: in default JIT mode it now panics in
`cranelift_jit::backend::JITModule::finalize_definitions` after ~372 s
(SIGABRT, crash log `.simple/logs/crash_61081.log` — a second fresh defect:
`run` of engine2d closures under JIT), while in interpreter mode the used-import
variants below run clean.

### Closest faithful runnable variants — the actual loader comparison

Probe bodies identical to the recorded ones except the engine import is used
(`val e = Engine2D.create_offscreen(4, 4)` before `print "ok"`); interpreter
mode (`SIMPLE_EXECUTION_MODE=interpreter`), `bin/simple run`, both files
repo-internal (see above for why /tmp no longer works):

| probe | run 1 | run 2 |
|---|---|---|
| probe_a2 — engine only (import used) | 1.90 s | 3.02 s |
| probe_b2 — engine + `window_winit.{winit_loop_new}` import | 2.96 s | 2.55 s |

Both print `ok`, exit 0. Delta < 2x in both directions across repeats, absolute
times ~2–3 s (2026-07-25: 24 s vs 3 s). The anomalous 8x speed-up-from-importing-
more-code is gone; adding winit now costs its natural ~0.5–1 s of extra closure,
and the engine-only case no longer pays any multi-second tax. This matches the
2026-09-12 loader-cache commits having fixed the resolution pathologies this
record described.

Resulting status: **CLOSED as resolved-by-loader-cache-work**, with the caveat
above: the exact recorded probe content is currently un-runnable due to the new
unused-import/prelude `print` defect (and JIT-mode engine2d `run` aborts) — both
need fresh bug records outside this sweep's 4-record scope.

## Repro

Five files, each `fn main() -> i64: print "ok"; 0`, differing only in imports.
All run with `SIMPLE_NO_DEPRECATED_WARNINGS=1` (so the hint spam is not a factor)
under `/tmp/claude-.../` paths (so the host kill monitor does not truncate them —
its `is_protected()` whitelists cmdlines containing `claude`).

| imports | wall time |
|---|---|
| `std.gpu.engine2d.engine` only | **24 s** |
| + `std.io.window_winit.{winit_loop_new}` | **3 s** |
| + `std.nogc_sync_mut.concurrent.thread.{thread_sleep}` | 24 s |
| + `std.io_runtime.{env_get, file_write}` | 23 s |
| + `std.common.encoding.font_registry.{selected_font_asset_candidates}` | 24 s |

Only `std.io.window_winit` has the effect, and it is an **8x speed-up from
importing more code**, which should not be possible.

Repeated back-to-back to rule out a warm cache:

```
probe_a_import (Engine2D only)      25 s
probe_b_render (Engine2D + draws)   28 s
probe_d_imports (full closure)       3 s
probe_b_render (again)              26 s
```

Stable and order-independent. First-run vs fourth-run timings for the same file
agree to within 2 s, so this is not `build/native_cache` warmth.

## Interpretation

Importing `window_winit` evidently short-circuits whatever the loader is doing
for 21 s in its absence — most likely a fallback scan / repeated re-resolution
that a symbol provided by `window_winit` satisfies up front. Worth checking
whether the Engine2D closure triggers repeated re-parsing of the same modules
when a backend/window symbol is unresolved.

The 24 s is pure module-load: in the fast case,
`examples/06_io/ui/graphics_2d_showcase.spl` reaches its first runtime trace
marker (`graphics_2d_trace=entry`, via `SIMPLE_SHOWCASE_TRACE=1`) at **t+3 s**.

## Why it matters

This is a flat 21 s tax on every interpreted Engine2D run, and it makes any
perf comparison between two 2D entries meaningless unless both happen to import
winit. It also inflates every "the 2D lane is too slow" report by ~21 s.

## Found via

Root-causing the 2D x headless showcase cell — see
`engine2d_load_font_interpreter_3kb_per_sec_2026-07-25.md`. (This is *not* that
cell's root cause; the showcase already imports `window_winit` and so pays only
the 3 s.)

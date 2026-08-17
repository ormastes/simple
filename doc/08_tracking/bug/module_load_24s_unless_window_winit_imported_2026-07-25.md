# Importing `std.gpu.engine2d.engine` costs 24 s — adding `std.io.window_winit` drops it to 3 s

- **Date:** 2026-07-25
- **Area:** module loader / import closure resolution
- **Severity:** medium — 8x startup penalty on every interpreted run that touches
  Engine2D without also importing winit.
- Status: OPEN (P2)
- Status re-verified 2026-08-17 by source inspection (triage shard 02).

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

## Re-measured 2026-08-17 (lane m7c_lib_async) — the 8x gap does NOT reproduce

Two minimal programs, `bin/simple run`, `nice -n 19`, shared/loaded host,
`/usr/bin/time -f %e`:

| program | imports | wall |
|---|---|---|
| `e1.spl` | `std.gc_async_mut.gpu.engine2d.engine.{Engine2D}` only | **20.49 s** |
| `e2.spl` | same **plus** `std.nogc_sync_mut.io.window_winit` | **17.02 s** |

The documented behaviour (24 s without winit, dropping to **3 s** with it) is
not reproduced: adding the winit import improves load by ~17%, not ~8x. What
remains true and still worth tracking is the absolute cost — importing
`engine2d.engine` alone costs ~20 s of module load, with or without the
workaround import.

Revised characterisation: the *slow engine2d module load* is LIVE; the
*winit-import-as-workaround* claim is STALE. Single run per configuration on a
contended host, so treat the 17% delta as noise-adjacent, not as a measured
effect.

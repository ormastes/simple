# Bug: `--open` window startup regressed 51s → >18min after `app.spl` gained host-WM imports (module-closure growth)

- **Status:** FIXED — `use lazy` on `app.spl:17-18` host-WM/compositor imports; measured `--open` window in 14s (2026-07-07), down from >18m28s, restoring parity with the 51s pre-regression baseline.
- **Discovered:** 2026-07-07
- **Domain:** app / ui.browser
- **Related:** `doc/08_tracking/bug/bootstrap_stage4_graph_load_timeout` (task #21, interpreted-frontend architecture)

## Summary

`bin/simple src/app/ui.browser/main.spl examples/06_io/ui/hello_web.ui.sdn --open --backend=metal`
(env: `SIMPLE_GUI=1`, `SIMPLE_EXECUTION_MODE=interpret`, `SIMPLE_LIB=src`) previously
reached a visible window in **~51s** (task #25 evidence, captured 2026-07-06 in a
pre-merge worktree). On current `main` (commit `92184eb687e8`) the identical
command ran **>18m28s with no window ever appearing**.

This is **not a hang**. Two `sample` captures taken minutes apart show the
process actively executing different interpreter leaf frames each time
(`exec_node`, `eval_call_expr`, `security_metadata_id`, hash-map operations),
CPU pinned at ~97-98%, and RSS flat (no growth, no swelling/thrashing
signature). This is consistent with genuine forward progress through a much
larger interpreted module-load/eval closure, not a deadlock or infinite loop
on a fixed frame. Raw `sample` evidence is saved in the session scratchpad
under `headline_evidence/`.

## Suspected Root Cause

Between the task #25 pre-merge worktree and current `main`, `src/app/ui.browser/app.spl`
gained additional imports as part of the rebase onto `main`:

- `use std.diag` (`dbg_stage`)
- `common.window_protocol.geometry`
- `os.compositor.host_compositor_entry`
- `browser_shared_wm_config` / `init_host_wm`

These pull the host-WM/compositor and web-renderer module closure into the
`--open` startup path. Because the frontend still runs **interpreted** (see
task #21: `native-build` → `cli_run_file`, ~0.8ms/char linear parse cost), any
increase in the transitively-imported module graph directly multiplies
startup-path interpretation cost. The growth in imported surface area (host
compositor entry + window protocol geometry + shared WM config/init) is the
most likely driver of the 51s → >18min regression — i.e., a module-closure
size regression, not an algorithmic hang.

## Verification of "not a hang"

- Two `sample`/perf snapshots taken several minutes apart during the same run
  show **different** interpreter leaf frames (`exec_node`, `eval_call_expr`,
  `security_metadata_id`, hash-map insert/lookup) — a true hang would show the
  same frame repeatedly.
- CPU usage stayed at ~97-98% throughout (actively computing, not blocked/idle).
- RSS stayed flat across the run (ruling out unbounded allocation/leak as the
  driver; this is compute-bound, not memory-bound).

## Fix Directions

1. **Lazy/conditional import of host-WM wiring** — only pull in
   `os.compositor.host_compositor_entry` / `browser_shared_wm_config` /
   `init_host_wm` when actually running under a host WM session, instead of
   unconditionally at module load of `app.spl`.
2. **Measure and bisect the closure growth** — use `dbg_stage` module-load
   stage logs (already imported via `std.diag`) to quantify how much of the
   >18min is attributable to the new imports specifically, vs. other main
   drift since 2026-07-06.
3. **Compiled-frontend redeploy (task #21)** — the durable fix is moving the
   frontend off the interpreted `cli_run_file` path per the task #21
   architecture note; that removes the ~0.8ms/char linear multiplier entirely
   so closure-size growth stops being startup-latency-critical.

## Verification Criteria

`--open` reaches a visible window in ~1 minute again on the `metal` backend,
i.e. restoring parity with the task #25 pre-merge measurement (~51s), for:

```
bin/simple src/app/ui.browser/main.spl examples/06_io/ui/hello_web.ui.sdn --open --backend=metal
```

with `SIMPLE_GUI=1 SIMPLE_EXECUTION_MODE=interpret SIMPLE_LIB=src`.

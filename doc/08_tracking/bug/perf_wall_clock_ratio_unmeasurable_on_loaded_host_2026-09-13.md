# Wall-clock perf ratios are not measurable on this host; use child CPU time

- Status: OPEN (2026-09-13)
- Found by: PERF-6, host load 27-40, 90 users, 20 cores

## Evidence

PERF-1 filed a ~25% single-sample flake rate for ratio probes
(`perf_ratio_specs_single_sample_flake_2026-09-12.md`) and fixed one spec with
`best_of_two`. PERF-6 measured the problem to be substantially worse than that.

**Across processes.** Interleaved A/B, 8 reps, one unchanged binary, n = 2,000,000:
the same fixture measured 2,549,572 us and 5,656,327 us -- a **2.2x spread**.
Minima across 8 samples still put a strictly-cheaper shape *above* a
strictly-more-expensive one.

**Within one process.** A fixture that times both shapes back to back, three
rounds each, reporting the best round of each, on ONE unchanged seed, four runs:

    ratio (declaring / hoisted) = 0.846, 0.963, 1.370, 1.346

The declaring shape does strictly more work than the hoisted one, so a ratio
below 1.0 is physically impossible. Two of four samples produced one.

**Child CPU time.** `/usr/bin/time -f '%U %S'`, interleaved A/B, 6 reps, same
two binaries and fixtures: a coherent, repeatable signal (medians 2,340 / 1,840
ms and 1,985 / 1,680 ms), and the two independent estimators (medians, minima)
agreed on the effect size to within 10 percentage points.

## Consequence for specs

A perf spec on this host must not pin a wall-clock RATIO. Two things do work:

1. **Pin a count.** `test/05_perf/interp/block_scope_shadow_parity_spec.spl`
   pins how many times the block-scope path runs, via `BLOCK_SHADOW_NAMES` /
   `BLOCK_SHADOW_OWNER_PROBES`, which is deterministic.
2. **Pin a loose absolute ceiling** that catches a catastrophic regression
   without flaking on a 2x load swing.

The three sibling perf specs named by PERF-1 and PERF-3 still take one sample
per point and still pin ratios; `interpreter_component_scaling_spec.spl`'s
`closure_capture` row was already shown by PERF-3 to fail on BOTH seeds at a
comparable rate. They should move to counts or to CPU time, not to more samples.

## Not attempted

`perf_event_paranoid=4` and `ptrace_scope=1` block `perf record` and `gdb -p`
attach. Launching under `gdb -batch` and interrupting works (a tracer must be an
ancestor here), but yielded 9 usable leaf samples in ~2 minutes -- too lossy to
attribute cost. There is no `valgrind` on this host and no process-CPU-time
`rt_*` extern to let a fixture measure its own CPU time in-program.

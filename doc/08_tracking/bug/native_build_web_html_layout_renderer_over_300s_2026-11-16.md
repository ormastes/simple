# Perf: native-build of simple_web_html_layout_renderer.spl exceeds 300 s

- Date: 2026-11-16
- Status: open
- Area: compiler / native-build per-file compile time (Rust seed lane)

## Symptom

Full K1 CLI native build (`native-build src/app/cli/main.spl ... --source
src/compositions/kernel_llvm --source src/compositions/cuda_disabled --source
src/compiler --source src/app --source src/lib --source src/plugins
--entry-closure`) failed twice with the default per-file limit:

```
src\lib\gc_async_mut\gpu\browser_engine\simple_web_html_layout_renderer.spl: timeout (300s)
```

The second run had a warm cache (`compiled=904 reused=2863 failed=1`), so this
is a real single-file cost, not a cold-cache artifact. The first timeout also
cascaded into 904 `NOT_ATTEMPTED: previous native worker timed out` files.

## Measurement

Rerun with `--timeout 900` succeeded:

```
Build complete: 4 compiled, 3764 cached, 0 failed
Time: 558.3s compile + 63.5s link = 621.8s total
```

The renderer was the only file that had not compiled before; the 558.3 s
compile phase covered 4 files. native-build prints no per-file time, so the
renderer cost is >300 s (measured twice) and at most 558 s. The file has 3083
lines. Host: shared Windows box, seed
`C:/dev/wt/sqlcov-20261114/build/nb/seed-vtable.exe`.

Against the "first object in 10 s" target this is roughly 30-55x over.

## Next

- Add a per-file timing line to native-build output so the cost is measurable.
- Profile which HIR/MIR phase dominates for this file (size alone does not
  explain it; other 3k-line files compile far faster).
- Workaround for full-CLI lanes: pass `--timeout 900`.

## Update 2026-11-16 (renderer-compile-perf lane)

Status: open (partial; step 1 landed, steps 2-3 not done)

- Step 1 done: `SIMPLE_NATIVE_FILE_TIMING=1` makes the Rust seed print
  `[native-file-phase] <phase>=<secs>s <file>` to stderr after each phase of
  `compile_file_to_object` (parse, pre_hir, hir, mir, mir_qualify, mangle,
  codegen). Lines print immediately, so a timed-out file still shows its last
  finished phase. Needs a seed rebuild to take effect. Unit tests:
  `file_phase_timing_line_names_phase_seconds_and_file`,
  `file_phase_timer_only_advances_when_enabled` (not yet executed, see below).
- Not done: dominant-phase measurement, bisect, fix. Blocked by disk: C: had
  9-13 GB free (below the 15 GB lane floor) so no cargo seed rebuild was run.
- Open check: confirm worker-process stderr is forwarded to the parent (the
  per-file worker may swallow it); verify with a trivial 1-file native-build.
- Plan: rebuild seed, run the renderer with the flag and `--timeout 900`, then
  add per-function timing inside the dominant phase to find the outlier.

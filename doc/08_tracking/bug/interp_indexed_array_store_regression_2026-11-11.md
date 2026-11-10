# Interpreter `[u32]` indexed store throughput regressed ~75–130× vs the 2026-08-14 seed (2026-11-11)

- **Status:** OPEN
- **Severity:** perf (engine2d fill-row lane surfaces it; JIT lane unaffected)
- **Found:** 2026-11-11, P3 lane `work/p3-interp7-20261111`, while re-measuring
  `engine2d_interpreter_span_kernel_marshalling_perf_gap_2026-08-14.md`
- **Area:** seed interpreter element-store path (`src/compiler_rust`
  interpreter; owned by the compiler-seed lane)

## Symptom

On the fresh Windows seed (worktree `bin/simple.exe`, build-commit
`46fe8f6b6def`, 2026-11-10 21:53), a tight interpreted loop of indexed stores
into a boxed `[u32]` runs at ~2.4 µs per store:

```
STORE_LOOP ms=613   # 640 stores × 400 iters = 256000 stores, interpreter
STORE_LOOP ms=0     # identical program, SIMPLE_EXECUTION_MODE=jit
```

Fixture (`build/p3fix-interp7/store_loop_bench.spl`, uncommitted build
fixture — source reproduced here for permanence):

```spl
extern fn rt_time_now_nanos() -> i64

fn now_millis() -> i64:
    rt_time_now_nanos() / 1000000

fn main():
    val W: i64 = 640
    val ITERS: i64 = 400
    var buf: [u32] = [0; 640]
    var t0 = now_millis()
    var it: i64 = 0
    while it < ITERS:
        var i: i64 = 0
        while i < W:
            buf[i.to_i32()] = 0xFF112233 as u32
            i = i + 1
        it = it + 1
    print("STORE_LOOP ms=" + (now_millis() - t0).to_text())
```

## Why this is a regression, not a measurement artifact

The 2026-08-14 measurement in
`engine2d_interpreter_span_kernel_marshalling_perf_gap_2026-08-14.md` ran the
SAME scalar store loop (`_scalar_fill_row`, which has deliberately had no
native branch since 2026-08-20) at ~31 ns/px (`8 ms / 400×640 px`) on that
date's seed. On the fresh seed the identical loop measures ~4074 ns/px
(`1042 ms` for the same 256000 stores via the
`test/perf/graphics_2d/bench_span_kernels.spl` rig) — ~130× slower than the
2026-08-14 interpreted baseline. The JIT lane compiles the identical loop to
native speed (`0 ms`), so the loop shape, constants, and host are fine; the
cost is interpreter-only, per indexed store.

Concretely, on the fresh seed (`native_rows=true`, 640 px × 400 iters, two
fresh-process samples, parity checksum `832951345` identical across samples):

| kernel | interp ns/px (fresh seed 2026-11-11) | JIT lane | C SIMD 2026-08-14 |
|--------|--------------------------------------|----------|-------------------|
| fill   | ~4074 (scalar store loop)            | native   | 0.17 |
| copy   | ~0.16                                | native   | 0.19 |
| blend  | ~0.24                                | native   | 0.83 |
| blit   | ~0.09                                | native   | — |

copy/blend/blit route through the bulk `write_span` mutating-method channel
plus native row kernels and sit at C parity — the documented per-element
gather/scatter marshalling cliff stays closed. Only the pure-interpreted
indexed-store loop carries the regression.

## Suspected mechanism (route, don't re-diagnose)

Per-access work in the seed interpreter's array element store grew massively
between the 2026-08-14-era seed and `46fe8f6b6def`. Prime suspects in that
window: the 2026-11-07 module-qualified class registry
(`resolve_class_in_scope` / `resolve_class_for_instance`, see
`engine_specs_spec_runner_interpreter_divergence_2026-09-16.md`) adding
per-access resolution cost, or the 2026-11-10 seedfix A/B touchpoints
(`35dbdfdd852a` tuple-destructure unbox, `46fe8f6b6def` flat Option array
get/at) sharing the element-access path with stores. Confining diagnosis and
fix to the compiler-seed lane; this lane is forbidden cargo/rustc, so no seed
rebuild or `src/compiler_rust` edit was possible here.

## Unblock condition

Bisect the seed interpreter element-store path between the 2026-08-14-era
seed and `46fe8f6b6def` (store-loop micro-fixture above is the probe), fix in
`src/compiler_rust`, rebuild the seed, and re-run
`test/perf/graphics_2d/bench_span_kernels.spl` expecting the fill row back in
the ~31 ns/px interpreted neighborhood. Also re-run the
`engine2d_interpreter_span_kernel_marshalling_perf_gap_2026-08-14.md` table
afterwards.

Side observations filed with this record (not blocking):

- The tracked rig `test/perf/graphics_2d/bench_span_kernels.spl` currently
  fails on the fresh seed with `error: semantic: unknown extern function:
  rt_println` — a prelude-shadowing local `println` in the import closure is
  called instead of the builtin. The triage copy used for the numbers above
  replaces `println(` with `print(`.
- The rig's leading `"""` docstring is a top-level statement, so the JIT
  entry path demotes the whole module to the interpreter
  (`module has 1 top-level statement(s) that the JIT entry path would silently
  skip`); bench numbers are therefore interpreter numbers unless the
  docstring is removed.

# Bug: graphics_2d full runner could not JIT/native lower framebuffer mutation

## Date

2026-05-31

## Symptom

Running:

```sh
bin/simple test/05_perf/graphics_2d/simple_runner.spl
```

falls back from JIT to interpreter with:

```text
HIR lowering error: Memory safety error [W1006]: mutation without mut capability: mutation requires `mut` capability at 79:35
```

The smoke-mode interpreter run still produces benchmark rows, but this blocks
the Phase 6 full-mode native measurement for the 1920x1080 fill, blit, and
clipped-scroll scenes.

## Impact

- Prevents credible native/SMF scalar CPU throughput numbers.
- Prevents comparing CPU-SIMD/native performance against C for the same runner.
- Keeps `doc/09_report/engine2d_compute_dispatch_benchmark_2026-05-31.md`
  limited to smoke evidence and report structure.

## Expected Behavior

The runner should either:

1. express framebuffer mutation with the correct mutable capability so JIT/native
   lowering succeeds, or
2. route hot loops through an accepted mutable span/kernel API already used by
   the Engine2D CPU-SIMD path.

## Reproduction

```sh
bin/simple test/05_perf/graphics_2d/simple_runner.spl
```

The fallback warning appears before the three `SCENE_RESULT` lines.

## Resolution

Resolved on 2026-05-31 by marking the framebuffer-mutating helper parameters
with `mut` capability in `test/05_perf/graphics_2d/simple_runner.spl`.

The native/JIT path then exposed a separate compiled interpolation issue for
top-level `text` constants. The runner now uses `runner_mode_text()` instead of
interpolating a top-level `RUNNER_MODE` value.

Verification:

```sh
bin/simple check test/05_perf/graphics_2d/simple_runner.spl
SIMPLE_NO_STUB_FALLBACK=1 bin/simple test/05_perf/graphics_2d/simple_runner.spl
```

The second command emits the header and three `SCENE_RESULT` lines without the
JIT fallback warning.

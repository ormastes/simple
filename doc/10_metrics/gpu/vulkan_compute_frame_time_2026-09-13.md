# Vulkan compute frame time — first measurement, and a failed A/B

Host: Windows 11, 1 Vulkan device, AVX-512 capable (F/VL/BW + XCR0 opmask/ZMM).
Benchmark: `test/05_perf/graphics_2d/bench_2d_vulkan.spl` — clear + 100 rects,
1920x1080 RGBA, Vulkan compute, 100 timed frames after 5 warmup frames.

**Prerequisite:** the seed must be built `--features vulkan`. Without it the
buffer and dispatch surface is stubbed while the probe still reports available,
and the benchmark silently produces nothing. See
`doc/08_tracking/bug/vulkan_feature_off_makes_gpu_benchmarks_silently_noop_2026-09-13.md`.

## The one clean measurement

Ten consecutive runs, quiet machine, current build:

```
7780 7993 7929 7883 7953 8049 7900 8199 7925 7989   (us/frame)
n=10  min=7780  median=7941  max=8199  stdev=105  spread=5.3%
```

`BENCH_RESULT scene=fill_1080p backend=vulkan_compute frames=100 avg_us≈7941
rects_per_frame=100 fb=1920x1080`

That is the number to quote for this host. Stdev is 1.3% of the median, which
is tight enough to detect a change of a few percent.

## The A/B that did NOT work — recorded so it is not repeated

The goal was to show the CPU/SIMD work did not hurt GPU offload, by comparing a
pre-SIMD seed (`c05895b817d`, built `--features vulkan` in a separate worktree)
against the current one. Two attempts, both unusable:

**Attempt 1 — blocked runs, contended.** The "before" set was collected while a
`cargo build` was still running:

```
before (contended)  n=10 median=9208  stdev=3549  spread=106%
after  (quiet)      n=10 median=7941  stdev=105   spread=5%
```

Comparing those would have "shown" a 14% GPU improvement from CPU-only changes,
which is nonsense. This is precisely the trap `.claude/rules/testing.md`
documents: hold the tree, the binary AND the machine load fixed, and state
which produced each number.

**Attempt 2 — interleaved A/B/A/B, 8 pairs each.** Alternating binaries to
cancel drift produced a **bimodal** distribution instead:

```
before:  51538 13197 13337 12466 45624 50284 13173 11763
after:   45636 14330 16887 23126 55812 54521 18418 22260
```

Two clusters, roughly 12-23 ms and 45-56 ms, in both arms. A median comparison
would report the current build 70% SLOWER; that is contention or GPU context
thrash from alternating two Vulkan processes, not a property of either binary.
**No conclusion can be drawn from this data, and none is drawn.**

## What can be asserted about GPU impact

Not from measurement, from scope: across the entire SIMD work
(`c05895b817d..HEAD`) **zero GPU source files are modified**. A grep for
`sffi_dispatch|ffi_dispatch|sffi_vulkan|ffi_vulkan|vulkan_icd|engine2d/engine.spl|draw_ir.spl|vulkan_session`
over the changed-file list returns one hit, and it is another session's
`doc/08_tracking/bug/` record, not source.

The single `interpreter_extern/gpu.rs` change is the Int→Bool fix for 14
externs declared `-> bool`, which makes the backend availability probe and the
whole compute-dispatch surface MORE correct than before — it is what allows
`if not rt_vulkan_X():` to branch at all.

## To actually close this

A trustworthy A/B on this host needs: a quiet machine (no concurrent builds),
blocked rather than interleaved runs so the GPU is not context-thrashed,
enough samples to see past the bimodality, and ideally an explanation for the
two clusters before trusting either arm.

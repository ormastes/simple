# The ML-KEM AVX2 C lane has no reproducible build recipe

**Status:** OPEN
**Found:** 2026-08-05
**Component:** `test/09_baselines/crypto/x25519mlkem768/`, `src/runtime/runtime_simd_dispatch.c`
**Impact:** the only artifact producing the campaign's first real paired timing
cannot be rebuilt from the repo.

## The result at stake

`build/check/x25519mlkem768-cpu-simd/mlkem_ntt_simd_c_test` is a prebuilt
x86-64 ELF that emits a genuine scalar-vs-AVX2 paired benchmark, gated behind
env `MLKEM_SIMD_BENCH_ITERS` (default `0`, i.e. off). Independently reproduced,
5 repeats at 20,000 iterations, `mlkem_ntt_simd_backend=1` every time:

| run | scalar ns/op | simd ns/op | speedup |
|---|---|---|---|
| 1 | 5325 | 3436 | 1.550 |
| 2 | 5788 | 3383 | 1.711 |
| 3 | 5672 | 3335 | 1.701 |
| 4 | 5437 | 3176 | 1.712 |
| 5 | 6847 | 3170 | 2.160 |

**Median 1.70x.** Report the median, not the max: the SIMD side is stable
(3170-3436, ~8% spread) while the scalar side scatters (5325-6847, 29%), so the
2.160 outlier is a slow *scalar* reading, not a fast SIMD one.

Scope, as the binary itself emits:
`mlkem_ntt_benchmark_scope=focused-primitive-mean-not-full-mlkem-promotion`.
This is an **NTT-primitive** result, not a full ML-KEM speedup, and not a
promotion.

## The defect

There is **no build script anywhere in the repo** for this lane. `grep -rln
"mlkem_ntt_simd_c_test"` over `scripts/` and `src/` returns nothing. The working
binary (built 2026-08-04 02:26, GCC 13.3.0) was produced ad hoc and its command
line was never recorded.

A naive rebuild from the sources fails at run time:

```
cc {-O2 | -O0 | -O2 -march=native | -O2 -mavx2} -I src/runtime \
   -o /tmp/v test/09_baselines/crypto/x25519mlkem768/mlkem_ntt_simd_c_test.c \
             src/runtime/runtime_simd_dispatch.c
```

All four link cleanly (`cc` exit 0, 0 errors) and then **segfault with exit 139
before emitting a single byte**. Since it links, no symbol is missing; the fault
is structural — additional translation units, or defines the ad-hoc build
supplied.

Contributing: the header does **not** declare the kernel entry points.
`src/runtime/runtime_simd_dispatch.h` is byte-identical between `main` and the
snapshot, and `grep -c rt_mlkem_ntt_simd` on it returns **0** in both. The build
therefore emits 10 implicit-declaration warnings, including
`rt_mlkem_ntt_simd_hits` and `rt_mlkem_ntt_simd_observed_rvv_vlen_bits`, whose
real return type is `int64_t` but which default to `int`.

Source/binary lineage is plausible but unproven: both contain
`mlkem_ntt_benchmark_scope`, `MLKEM_SIMD_BENCH_ITERS` and
`mlkem_ntt_scalar_ns_per_op`.

## Why the sources are landed anyway

They were **orphaned**. `rt_mlkem_ntt_simd_batch` has never existed on `main`
(0 hits at `origin/main`, and absent from every commit touching the file). It
lived only as uncommitted content in a scratch worktree
(`build/worktrees/simpleos-engine2d-stage4-snapshot`), 1618 lines against
main's 1211, plus two untracked test files. One worktree cleanup would have
destroyed the only source for the campaign's sole real timing result.

Landing was checked both directions first: 387 lines added, 4 removed; no
function present on `main` is dropped; `main` has not touched this file since
the snapshot. The 4 removed lines are `__attribute__((target("avx2")))`
replaced by a conditional `SIMPLE_RUNTIME_TARGET_AVX2` macro now applied at
**8** sites — broader coverage than before, and portable to non-x86.

## Next steps

1. Add a build script for the lane under `scripts/check/`, and record the exact
   flags that produce a working binary.
2. Declare the `rt_mlkem_ntt_simd_*` entry points in
   `src/runtime/runtime_simd_dispatch.h` so callers stop relying on implicit
   declarations with the wrong return type.
3. Then rebuild from committed sources and confirm the benchmark reproduces.
   **Until step 3 passes, the 1.70x number rests on a binary that cannot be
   regenerated from the tree.**

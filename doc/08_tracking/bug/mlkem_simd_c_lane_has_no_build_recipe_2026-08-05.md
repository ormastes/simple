# The ML-KEM AVX2 C lane has no reproducible build recipe

Status: FIXED
Status re-verified 2026-08-17 by source inspection (triage shard 02).
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

---

## RESOLVED 2026-08-05 — root cause, both losses, and a reproducible build

**Status: FIXED.** The lane builds from committed sources and reproduces the
prebuilt binary.

### Root cause: pointer truncation from the missing prototype

`rt_mlkem_ntt_simd_batch` returns `SplArray*`. With no prototype, C defaults the
return to `int`, so GCC keeps only `eax` and sign-extends it:

```
call  rt_mlkem_ntt_simd_batch
test  %eax,%eax          <- 32-bit null check
cltq                     <- sign-extends the TRUNCATED return
cmpq  $0x300,0x8(%rax)   <- SIGSEGV here
```

The working binary at the same call site has `test %rax,%rax` — full 64-bit, no
`cltq`. Proven by disassembly plus a gdb backtrace to
`mlkem_ntt_simd_c_test.c:213`, not inferred. Alignment, TLS init and a missing
`-D` are all eliminated. The other five implicit declarations return `int64_t`
and would corrupt values; only the pointer one faults.

### Both missing pieces were casualties of the same tree wipe

- `src/runtime/runtime.h` **used to declare all six kernels** at
  `1c74085cfce:1133-1140`. The test includes `runtime.h`, so the original build
  had real prototypes. Current `runtime.h`: 0 hits.
- A build script **`scripts/check/check-x25519mlkem768-cpu-simd.shs` existed**
  and is gone. Its flags: `-O2 -std=gnu11 -Wall -Wextra -pthread
  -ffunction-sections -fdata-sections -Isrc/runtime`, linked `-Wl,--gc-sections`.

Both were lost in `118c636ead8` (revert `7f5a55fa46e`). So the build was never
"ad hoc" — the repo lost its prototypes and its recipe.

`--gc-sections` also explains the only other binary difference: the prebuilt
binary lacks `dlopen/malloc/calloc/free` dynamic symbols while its `.o` still
carries 23 OpenCL symbols. The linker dropped them; the source is identical.

**Lineage confirmed, not merely plausible:** both binaries emit the identical
benchmark checksum `66698556`.

### Fix

- `src/runtime/runtime_simd_dispatch.h` — declares all six entry points with
  real signatures (`SplArray* rt_mlkem_ntt_simd_batch(SplArray*, bool)`, five
  `int64_t`), plus `<stdbool.h>` and a guarded `SplArray` forward declaration.
- `test/09_baselines/crypto/x25519mlkem768/mlkem_ntt_simd_c_test.c` — includes
  that header.
- `scripts/check/build-mlkem-simd-c-lane.shs` — builds from committed sources
  and runs, with **`-Werror=implicit-function-declaration`** so this exact class
  of failure cannot return silently. Verdict `MLKEM_SIMD_C_LANE: PASS/FAIL/SKIP`,
  non-zero on failure, `$?` taken from the binary rather than a pipe.

The naive command that previously segfaulted now builds with **0 errors, 0
implicit warnings** and the binary reports `MLKEM_NTT_SIMD_C_TEST: PASS`,
`mlkem_ntt_simd_backend=1`.

### The 1.70x figure is CORRECTED to ~1.6x

The earlier 1.70x came from **5 samples — too few**. Measured properly:

| source | n | median | min | max |
|---|---|---|---|---|
| rebuilt (alternating A/B) | 15 | 1.608 | 1.196 | 2.529 |
| prebuilt (alternating A/B) | 15 | 1.667 | 1.470 | 2.608 |
| rebuilt (independent lane, n=21) | 21 | 1.592 | 1.481 | 2.938 |
| prebuilt (independent lane, n=21) | 21 | 1.586 | 1.208 | 2.475 |

Rebuilt and prebuilt agree within noise (0.4%–3.7% depending on the run). The
honest figure is **~1.6x median**, and the metric **scatters 1.2x–2.9x**, so any
single reading — including a flattering one — is meaningless. Always report a
median over >=15 repeats with the range.

**Measurement trap recorded:** a first comparison ran all repeats of one binary
then all of the other, and showed a spurious 12.7% gap. Blocks are not an A/B.
Alternate the two binaries within the loop, or load drift becomes the result.

Scope is unchanged and remains the binary's own string:
`mlkem_ntt_benchmark_scope=focused-primitive-mean-not-full-mlkem-promotion` — an
NTT-primitive speedup, **not** a full ML-KEM speedup and **not** a promotion.

## Re-confirmed 2026-08-09

Fresh re-run of `sh scripts/check/build-mlkem-simd-c-lane.shs` from a clean
invocation: builds with 0 implicit-declaration warnings and exits with
`MLKEM_SIMD_C_LANE: PASS backend=1 iters=20000
bin=build/check/mlkem-simd-c-lane/mlkem_ntt_simd_c_test`. Status remains
**FIXED**; the build script and the header declarations from the 2026-08-05
resolution are both present and working on the current tree. No code changed
this pass.

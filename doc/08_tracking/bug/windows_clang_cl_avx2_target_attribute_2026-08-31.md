# clang-cl ignores `__attribute__((target("avx2")))`, forcing the Windows MSVC lane onto scalar SIMD paths

- **Date:** 2026-08-31
- **Status:** WORKED AROUND (correct, slower). The performance gap is real and
  is recorded here rather than absorbed silently.

## What happens

`runtime_simd_utf8.c` and `runtime_simd_dispatch.c` fail under clang-cl:

    error: use of undeclared identifier '__m256i'   (runtime_simd_utf8.c)
    error: unknown type name '__m256i'              (runtime_simd_dispatch.c)

Both files are in the core-C archive input list, so this stopped the entire
`core-c-bootstrap` runtime supplement from building — which is what leaves ~103
`rt_*` undefined at the Stage 2 link.

## Why

The design is deliberate and good: AVX2 bodies carry
`__attribute__((target("avx2")))` so only those functions get AVX2 codegen while
the rest of the translation unit stays at the baseline ISA, and
`simd_detect_avx2()` (real cpuid) decides at runtime whether to call them.

Under `-fms-compatibility`, clang-cl does not honour that attribute for the
purpose of exposing intrinsics, so the AVX2 bodies cannot compile at all.

Affected combination is narrow, and was checked rather than assumed:

| toolchain | AVX2 intrinsics without `/arch` | affected |
|---|---|---|
| GNU-driver clang | yes, attribute honoured | no |
| MSVC `cl.exe` | yes, permitted irrespective of `/arch` | no |
| **clang-cl** (`__clang__` && `_MSC_VER`) | **no** | **yes** |

## Why `/arch:AVX2` was NOT used

It would fix the compile and break the design. `/arch:AVX2` licenses the
compiler to emit AVX2 **anywhere in the translation unit**, including the scalar
fallbacks that exist precisely for CPUs without AVX2. A runtime-dispatch design
would become a crash on pre-Haswell hardware. Correctness beats the throughput.

## What was done

`SIMD_CAN_AVX2` now excludes clang-cl, and every x86-intrinsic block in
`runtime_simd_dispatch.c` (`#if` and `#elif` forms alike) is gated on it, so
clang-cl compiles the file exactly as a non-x86 target already does. The scalar
implementations — `scalar_utf8_count_codepoints`, `scalar_utf8_validate`,
`scalar_utf8_find_invalid`, and the trailing scalar loops in the engine2d
dispatchers — are pre-existing and are what now runs.

Verified: 18 of 18 core-C sources compile under clang-cl (was 16), and MinGW
`gcc -fsyntax-only` remains clean on all three touched files.

## The cost, stated plainly

Windows MSVC-lane builds lose AVX2 for UTF-8 counting/validation, the ML-KEM NTT
butterfly, and engine2d fill/blend. **SSE2 is lost too**, not just AVX2: the
SSE2 and AVX2 variants share enclosing blocks, and separating them was attempted
and abandoned — it produced a file where the SSE2 definitions were gated out
from under their own call sites. Treating clang-cl uniformly as "no x86
intrinsics" is the coherent state, and it is the state every non-x86 target
already builds in.

## How to close it properly

1. Confirm whether a newer clang honours `target` under `-fms-compatibility`;
   if so, gate the exclusion on `__clang_major__`.
2. Or split the AVX2/SSE2 bodies into their own translation units, each compiled
   with its own `-mavx2` / `-msse2`, so raising the ISA per file is safe. This
   is the standard structure for runtime dispatch and would restore both tiers
   on every toolchain.
3. Or build the Windows lane with real MSVC `cl.exe` for these two files.

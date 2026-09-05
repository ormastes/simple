# Native runtime UTF-8 SIMD coverage and memory — 2026-08-26

The forced C harness directly invokes scalar, SSE2, and AVX2 validation,
first-invalid, and code-point-count kernels. Its matrix covers valid ASCII and
multibyte inputs, malformed lead/continuation/overlong/surrogate/out-of-range/
truncated inputs, and invalid bytes at offsets 15–65.

Cycle 1 found an AVX2 defect: absolute invalid offset 32 was returned as 1.
`avx2_utf8_find_invalid` now adds the scalar fallback base, matching SSE2 and
the scalar oracle. Cycles 2 and 3 pass all assertions.

Seven samples, each processing 64 MiB per backend:

| Backend | p50 ns | p95 ns | Approx. p50 GB/s |
|---|---:|---:|---:|
| scalar | 75,303,528 | 75,562,893 | 0.89 |
| SSE2 | 4,506,439 | 4,584,278 | 14.89 |
| AVX2 | 2,410,049 | 2,425,389 | 27.85 |

The corpus is one static 1 MiB array. Harness/runtime validation performs zero
heap allocations, retains zero bytes, and reports process HWM 2,048 KiB.
Checksum is 1,344 and `active_avx2=1`.

gcov for the full `runtime_simd_utf8.c` owner reports 58.15% lines (157/270),
60.66% branches executed, and 54.51% branches taken at least once. This is not
100%: NEON, SSE2-only dispatch, tagged-string/cache APIs, and slice-audit modes
remain open. The evidence qualifies only this host's scalar/SSE2/AVX2 validator
kernels, not AVX-512, NEON, or RVV rows.

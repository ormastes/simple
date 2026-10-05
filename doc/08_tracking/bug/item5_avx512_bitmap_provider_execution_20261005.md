# Item 5 AVX512 bitmap-provider slice: execution evidence

This records a bounded C provider result, not completion of the Item 5 provider goal. The change is based on release commit `4ed90f33547b1c89ac485408326ef61b0a4b8b30`.

## Implementation

- `src/runtime/providers/vector/bitmap_avx512.c` implements the existing `simple_bitmap_kernel` raw-span ABI. It processes 16 packed `u32` words per AVX512F operation and retains a scalar tail.
- `src/runtime/providers/vector/bitmap_provider.c` checks AVX512F CPUID, XSAVE/OSXSAVE/AVX prerequisites, and XCR0 bits `0xe6` before calling that separate target-attributed translation unit. A test-only compile flag exercises feature refusal.
- `scripts/check/check-vector-bitmap-x86-avx512.shs` builds the dispatcher at `-march=x86-64` and the kernel as a separate target-attributed object, generates provider identity from the source/ABI digests, checks disassembly separation, and reuses `src/runtime/test/vector_bitmap_target_selfcheck.c` for dynamic load, every-output oracle checks, boundary/tail lengths, and canaries.
- The checker is wired through `.github/workflows/repo-hygiene.yml`.

## Native result

Output directory: `/tmp/item5-avx512-bitmap-20261005-r2` (WSL). The host exposed the AVX512F flag. The regular loaded provider reported `PASS bitmap-provider checks=70357 vector_iterations=884 supported=1 loads=1`; the forced-refusal provider reported `PASS bitmap-provider checks=70357 vector_iterations=0 supported=0 loads=1`. Thus the regular case executed full ZMM iterations, while the forced case refused every operation before writing output. The checker found no `zmmN` or `kmov` spellings in the baseline provider object and found `zmmN` spellings in the kernel object.

Receipt hashes:

- `artifacts.sha256`: `35e0003f7b4ef3235dc4b78fdd7a43e6e76ef141175e1c911bb07489eb8eb3e1`
- `source.sha256`: `4c53bf1048f7cd3399c58eb64db53d8e56d41c63f9ffa82ba86faa8eaec3a5f7`
- `native.log`: `352f1a19c59ad725fd8903f5d056f23c153bdcaaba3ae51e75732ed64f783286`
- `forced.log`: `f689364083d623bb7a7095314499a080a93b1dc67c6bfa47e0930f86a2c7f687`

## Limits

This is provider ABI and hardware-kernel evidence only. It does not prove admission through the Simple-owned session loader, invocation from Simple DB `QueryBuilder`/`RowBitmap`, or invocation from the HTTP parser. The wire currently covers HTTP byte/CRLF operations, but this provider implements bitmap AND/OR only. The ordinary `runtime_simd_dispatch.c` still contains its pre-existing AVX512 runtime kernels, so default executable-image minimization is not established by this slice. CUDA, Simple application probes, and SVE/SVE2/RVV execution remain outside this evidence.

The forced-refusal build bypasses `available()` as a whole; it does not independently toggle each CPUID, OSXSAVE, or XCR0 prerequisite. The inherited selfcheck does not snapshot inputs or assert the bitmap response's `scalar_result == -1`, so those properties still need explicit cases. Its constructor observer proves only that the diagnostic DSO was loaded by the test harness; it is not production provider-session admission evidence.

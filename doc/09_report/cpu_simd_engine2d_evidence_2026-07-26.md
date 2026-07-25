# CPU SIMD Engine2D AArch64 Evidence — 2026-07-26

## Scope

Native AArch64/NEON exact-bitmap evidence for Engine2D fill, copy, alpha,
scroll, and the 16x12 composed diagram.  The check uses no blur or tolerance.

## Diagnosis

- The production C/NEON `engine2d_blend_pixel` implementation was correct.
- The pure-Simple scalar fallback read packed pixels through `any` without
  normalizing them first.  Under native AOT this retained boxed values in its
  channel arithmetic, so scalar expected pixels diverged even though the C
  kernel was correct.
- The evidence receipt also read aggregate bool fields that native AOT stored
  incorrectly: hit count `2` and the reason text reported a native SIMD run,
  while `native_simd_executed` printed `false`.

## Fix

- Normalize packed source and destination words to `i64` in
  `_scalar_blend_row` before bit arithmetic.
- Make both evidence sources use the canonical scalar helpers rather than
  their duplicated scalar compositor.
- Preserve a non-opaque destination alpha fixture, which catches the former
  hardcoded-opaque reference formula.
- Derive receipt text and gates from per-kernel hit counters and summed exact
  bitmap mismatch totals, rather than aggregate bool storage or reason text.

## Native Capture

Command: native-build with the retained self-hosted AArch64 binary, followed by
`build/cpu-simd-parity-native/cpu_simd_engine2d_evidence_receipt`.

Before fix:

- diagram expected checksum: `79329719696120`
- diagram actual checksum: `79321896458941`
- diagram mismatches: `18` (first index `115`)
- native SIMD hits: `2`; aggregate receipt printed `false`

After fix:

- fill/copy/alpha/alpha-edge/scroll mismatch counts: `0`
- diagram expected and actual checksum: `79321896458941`
- diagram mismatch count: `0`
- `cpu_simd_executed_all=true`
- `cpu_simd_native_simd_executed=true`
- `cpu_simd_native_simd_bit_exact=true`
- native SIMD hits: `2`
- overall: `pass`

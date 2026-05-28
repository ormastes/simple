# SIMD Auto-Application Maintainer Guide

## Purpose

SIMD auto-application lets compiler optimization passes replace safe scalar patterns with vectorized forms while preserving scalar fallback behavior.

This guide is for optimizer authors adding or reviewing auto-SIMD rewrites.

## Allowed Rewrites

A rewrite is eligible only when all of these are true:

- The scalar operation is pure for the rewritten range.
- Lane count and element width are known or guarded.
- Overflow, saturation, signedness, and rounding behavior match the scalar path.
- Alignment assumptions are explicit, or the rewrite uses unaligned-safe loads/stores.
- The scalar fallback remains available for unsupported targets.

Common candidates:

- byte scanning and UTF-8/text classification,
- fixed-width integer bit operations,
- crypto/compression round helpers with exact scalar parity,
- small matrix/vector loops where dimensions are fixed or guarded.

## Fallback Rules

Every auto-SIMD rewrite must keep a scalar path.

Target feature checks decide whether the vector path is active:

- x86/x86_64: SSE/AVX feature gates.
- ARM/AArch64: NEON/SVE gates where available.
- RISC-V: vector extension gates where available.
- Unknown target: scalar only.

Do not emit a vector-only implementation unless the public API explicitly requires that target.

## Duplication Rules

Manual SIMD intrinsics and auto rewrites must not grow separate semantic implementations.

Use this ownership split:

- scalar helper: owns the reference semantics;
- SIMD helper: owns lane mechanics;
- optimizer recipe: owns detection and replacement;
- tests: prove scalar/SIMD parity.

If a manual intrinsic and an auto rewrite need the same operation, share the helper or record why they cannot share it.

## Verification

Use syntax checks for changed compiler/runtime files, then run focused parity tests.

```bash
bin/simple check src/compiler src/lib
bin/simple test test/unit/runtime/simd_text/simd_text_test.spl --mode=interpreter --clean
bin/simple test test/unit/runtime/simd_text/simd_text_fuzz_test.spl --mode=interpreter --clean
bin/simple test test/integration/rendering/simd_parity_spec.spl --mode=interpreter --clean
bin/simple test test/perf/scilib_simd_ops_perf_spec.spl --mode=interpreter --clean
```

When the change touches optimizer recipe selection, also run the feature-specific sys-test plan listed in:

- `doc/03_plan/sys_test/simd_auto_application.md`
- `doc/05_design/simd_rollout_plan_v2.md`

## Review Checklist

- [ ] Scalar behavior is still the source of truth.
- [ ] Target feature gate is explicit.
- [ ] Unsupported targets fall back to scalar code.
- [ ] Signedness and overflow behavior are documented in tests.
- [ ] Test names identify scalar-vs-SIMD parity.
- [ ] No duplicated helper exists for the same operation in another SIMD module.

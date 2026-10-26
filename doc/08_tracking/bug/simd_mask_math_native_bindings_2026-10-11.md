# SIMD mask projection and square-root binding failures

Status: local candidate applied on `release_phase3`; native verification and
performance admission pending. Do not mark fixed or land before verification
and the user's Phase3 pass gate. No workaround or skipped assertion is used.

## Reproduction and cause

The build-runner baseline had three failed HIR entries. Direct object-generation
diagnostics with the same immutable b580 compiler retained the causal errors:

- `src/lib/nogc_async_mut/simd/mask.spl`: unresolved type `V.Mask`.
- `src/lib/nogc_async_mut/simd/fixed.spl`: unresolved `V.Mask` and `rt_sqrt`.
- `src/lib/common/simd_scan.spl`: the same errors through its SIMD dependencies.

All three exited 1 before MIR/object emission. Evidence, source/log hashes,
elapsed times and process-tree memory are in
`build/native_probe/build-runner-review-20261011/DIRECT_SIMD_FAILURE_SUMMARY.json`.
The probes took 4.505-4.658 seconds, with peak working sets 248956-304828 KiB.
These failing-compilation timings are not throughput baselines for working code.

The `Vector` trait describes a mask projection in comments but does not declare
that associated type. Concrete comparison methods return `Mask<V>`.
`Mask.from_cmp` is an identity constructor, so its parameter can use `Self`.
`FixedVec` called `rt_sqrt` without a declaration. The existing scalar owner
`std.common.math.math.math_sqrt` binds `rt_math_sqrt` and takes/returns f64.

## Local repair and tests

The mask constructor takes `Self`, preserving its vector specialization.
Square-root operations use the scalar facade and explicitly convert between
the lane type and f64. Reciprocal square root converts back to the lane type
before division; f32 rounding and exceptional values require execution checks.
The existing loop and output-array ownership are unchanged.

`test/01_unit/lib/simd_mask_math_binding_spec.spl` contains six authored cases:
mask bits/lane counts for float and integer vectors, f32/f64 ordinary square
roots and reciprocal roots, and zero/negative/NaN/non-perfect-square behavior.
`test/fixtures/compiler/simd_mask_type_distinction_negative.spl` must fail for
incompatible mask vector types. Parser/import/tool failures cannot satisfy it.
Both are **UNRUN**. Actual baseline HIR failures supply the pre-fix reproduction;
they do not replace executable behavior or negative-type verification.

## Remaining admission

Run the corrected direct diagnostics with normal cache validation, retain all
failure evidence, and do not replay unrelated successful modules. Execute the
behavior and negative-type controls with suitable pure-Simple tooling. Measure
completed-work latency and peak memory, including f32 conversion costs; source
inspection alone does not establish no regression. Check the Rust seed only as
a separate supported-feature diagnostic, not a substitute for pure qualification.

The standalone test-runner's 26 failed entry paths are different from these
three SIMD entries; their causes remain independent until demonstrated.
This document is the pending bug record; a canonical bug-DB write is not claimed.

## Final bounded native attempt

The third native attempt is terminal; do not launch a fourth automatic retry.
Request `36ae586ac8f0db462c10744aeb59288a3d61a1c7ddb23160dd39837e7ce8d11c`
used private source `b1c827a277ecf14586d07675c2346029c56cd326`, the two
reviewed source edits, the real scalar math owner, and normal validation of a
separate copy of the prior cache. All Jobs closed; all three commands exited 1.

| Entry | Seconds | Peak working set KiB | Remaining failure |
|---|---:|---:|---|
| simd_scan | 43.130 | 335520 | MIR unresolved `cmp_eq`, `any`, `all`, `lane_active` |
| fixed | 9.941 | 284336 | Codegen rejects empty mask/vector MIR units |
| mask | 8.881 | 317336 | Codegen rejects empty mask/vector MIR units |

Evidence: `build/native_probe/build-runner-review-20261011/simd-final-cycle3/RESULT.json`
and its request-named stage logs. Fixed reports two successful internal units
and two failures; this is not a successful aggregate build or proof of the
requested output object. Artifact verification remains separate.

The repair progresses beyond the original HIR failures, but does not establish
working SIMD or passing behavior tests. Longer elapsed times include later
compiler stages and are not an equivalent-work performance regression test.
Investigate concrete generic method resolution and declaration-only artifact
policy separately. Do not invent runtime bodies to make empty units compile.

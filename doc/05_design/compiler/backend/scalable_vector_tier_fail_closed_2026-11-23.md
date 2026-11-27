# Scalable Vector (SVE/RVV) Tier Selection — Fail Closed (2026-11-23)

Scope: "Optional Backend Hardening" SVE/RVV item of
`doc/03_plan/release/1.0.0/robustness_completion_plan_2026-11-17.md` (owner: in scope, 2026-11-18).

## Rule
- Every `cpu_tier` spec has a SIMD class (`tier_spec_simd_class`,
  `src/lib/common/cpu_tier/tier_id.spl`), spelled like the seed's
  `SimdTier::as_str`: `scalar`, `x86_64_sse2|avx2|avx512`, `aarch64_neon|sve|sve2`,
  `riscv64_rvv`. `armv9-a` classes as `aarch64_sve2` (SVE2 is mandatory in v9).
- A named target whose tier classes as SVE, SVE2 or RVV is refused by
  `target_action_error` with
  `target-error: scalable-vector-unsupported: <name>: <tier> (<class>): native-build has no SVE/RVV codegen; drop cpu_tier for a scalar build`.
  No silent baseline build; the documented scalar fallback is to drop `cpu_tier`
  explicitly. The fixed-VL refusal (`sve256`, `zvl*`) still fires first.
- The target cache namespace is split by SIMD class
  (`build/target_cache/<target>/simd-<class>`) whenever a tier is set, so
  NEON / SVE / SVE2 / RVV objects never share entries. The seed's native object
  cache key already folds `active_simd_tier_name()` with the same spellings.

## Limits
No SVE/RVV hardware here: verification is cross-target classification and
diagnostic specs only (`test/01_unit/app/build/targets_executor_scalable_vector_spec.spl`).
When native-build gains SVE/RVV codegen, replace the refusal with a `--cpu` policy.

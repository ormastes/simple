# Host CPU Runtime Variants System Test Plan

- Verify `cpu_config.sdn` is created on first use and round-trips through the parser.
- Verify canonical rewrite refreshes `version`, `target_triple`, `generated_by`, `support`, `simple_support`, and clamps `enabled.*` to the allowed subset.
- Verify compiler/runtime tier defaults change when `enabled.simd_tier` is downscoped.
- Verify compiler/interpreter cache keys change with the active SIMD tier when the tier is selected from `cpu_config.sdn`, not only from `SIMPLE_SIMD_TIER`.
- Verify stdlib variant-root ordering changes with the active SIMD tier so downscoped runs resolve scalar/common paths before optimized roots.
- Verify dynamic loader sibling probing prefers suffixed variants before the unsuffixed runtime.
- Verify the v1 runtime-variant collapse matrix:
  `x86_64_avx512 -> x86_64_avx2 -> x86_64_sse2 -> scalar`,
  `aarch64_sve2 -> aarch64_neon -> scalar`,
  `aarch64_sve -> aarch64_neon -> scalar`,
  `riscv64_rvv -> scalar`.
- Verify package manifest round-trip preserves runtime-variant metadata.
- Verify embedded runtime selection chooses the best compatible present resource and falls back when the highest compatible variant metadata exists but the resource is absent.
- Verify malformed or truncated manifest sections fail closed instead of degrading to scalar/default metadata.

# Host CPU Runtime Variants

## Functional Requirements

- `REQ-001`: The Rust SIMD/common layer shall detect host SIMD support and persist a machine-local `cpu_config.sdn`. In v1, non-x86 optional runtime detection remains conservative for deferred tiers such as `aarch64_sve`, `aarch64_sve2`, and `riscv64_rvv` unless explicit target-specific probing is implemented and verified.
- `REQ-002`: `cpu_config.sdn` shall contain `support`, `simple_support`, and `enabled` sections.
- `REQ-003`: `SIMPLE_CPU_CONFIG_PATH` shall override the default config path.
- `REQ-004`: The default active tier shall resolve by precedence: explicit `SIMPLE_SIMD_TIER`, then `cpu_config.sdn enabled.simd_tier`, then raw host detection.
- `REQ-005`: `cpu_config.sdn` canonicalization shall rewrite `version`, `target_triple`, `generated_by`, `support`, `simple_support`, and `enabled` from current detection plus implementation support; user edits may only downscope `enabled.*`.
- `REQ-006`: Invalid `enabled` values shall be clamped to the allowed subset `support ∩ simple_support`, duplicates shall be removed, and the config file shall be rewritten.
- `REQ-007`: Dynamic runtime loading shall probe sibling suffixed runtime libraries in compatibility order before the unsuffixed fallback.
- `REQ-008`: Package manifests shall preserve the legacy single-variant fields and also support a runtime-variant index for embedded runtime resources.
- `REQ-009`: Embedded runtime selection shall choose the best compatible runtime resource for the active host tier and target triple.
- `REQ-010`: Compiler and interpreter cache keys shall include the active SIMD tier so that a downscoped `enabled.simd_tier` cannot reuse artifacts produced for a different tier.
- `REQ-011`: Stdlib variant-root selection shall follow the active SIMD tier so module resolution and runtime lookup paths change together when the active tier changes.
- `REQ-012`: The v1 runtime-variant matrix shall only ship distinct artifacts for implemented runtime families: `scalar`, `x86_64_sse2`, `x86_64_avx2`, `aarch64_neon`, and `riscv64_rvv` only when both the target toolchain and explicit host-capability probing support it.
- `REQ-013`: Hosts detected as `x86_64_avx512`, `aarch64_sve`, `aarch64_sve2`, or other unimplemented higher tiers shall collapse to the best implemented fallback tier for runtime variant probing and embedded runtime selection. This collapse behavior is sufficient for v1 readiness on x86_64 and aarch64; `riscv64_rvv` auto-selection is not first-class in v1 unless explicit RVV host probing is implemented and verified for that target.

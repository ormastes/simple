# Host CPU Runtime Variants Architecture

## 2026-10-11 environment-binding reconciliation

The [Item 5 variation integration](../../05_design/compiler/perf/item5_shared_provider_interfaces_2026-10-09.md#2026-10-11-variation-and-sosix-integration) supplies the current owner map. Reuse `composition/environment_variants` snapshots, catalog, admission, binding and generation state; keep existing public compatibility views without adding a peer resolver.

Distinguish detected hardware, OS-authorized state, compiled implementation availability, policy permission and actual execution evidence. Output target is independent of the compiler's execution host. A worker's vector length/affinity domain and an accelerator's generation can invalidate eligibility without changing architecture names. Bind at controlled boundaries and retain immutable generations for active sessions; no CPUID, catalog search or filesystem access in SIMD loops. ARM/RISC-V functionality and physical performance require separate target evidence.

## Historical V1 decision — superseded for shared ownership

The earlier V1 design treated `simple-simd` as the authority for `SimdTier`, raw detection, fallback ordering and best-implemented-tier collapse, with `cpu_config.sdn` layered over it. The 2026-10-11 selected design supersedes the global-ownership claim: retain legitimate native probe/legacy projection responsibilities there, but normalize feature meaning, eligibility and binding through the existing environment-variant authority. Caller migration and parity are pending; this document does not claim the old implementation has already been removed.

In v1, that authority is intentionally split between first-class runtime-detected tiers and conservatively modeled optional non-x86 tiers. X86_64 runtime detection remains first-class. AArch64 `sve`/`sve2` and riscv64 `rvv` are documented as deferred runtime-probing work unless a target-specific probe is implemented and verified.

## Flow

1. Raw host detection builds `support`.
2. Current Simple implementation support builds `simple_support`.
3. Canonicalization rewrites `version`, `target_triple`, `generated_by`, `support`, and `simple_support` from current detection data, then clamps `enabled` to a downscoped subset and persists the full canonical file.
4. Compiler/runtime consumers ask `simple-simd` for the active tier.
5. Cache keys and stdlib variant-root resolution derive from that same active tier so a config downscope changes both artifact identity and lookup order.
6. Native loader and package resource selectors use that same active tier.

This means v1 remains globally coherent even when some optional non-x86 features are conservatively under-detected: the active tier still drives canonicalization, cache identity, variant-root ordering, and runtime probing consistently. That is not treated as a release blocker for x86_64 or aarch64 because those hosts already collapse to shipped fallback tiers. It is only a target-specific blocker if a release explicitly claims first-class `riscv64_rvv` host auto-selection.

## Canonical Rewrite Contract

- Operators may edit `enabled.simd_tier` and `enabled.instruction_sets` to downscope the machine.
- Operators may not force-enable capabilities by editing `support` or `simple_support`; those sections are informational outputs regenerated from detection and current Simple implementation support.
- Invalid, duplicate, or out-of-order `enabled.instruction_sets` entries are rewritten into canonical schema order after clamping to `support ∩ simple_support`.

## Runtime Variant Matrix

- v1 ships distinct runtime artifacts only for:
  `scalar`,
  `x86_64_sse2`,
  `x86_64_avx2`,
  `aarch64_neon`,
  `riscv64_rvv` only when toolchain support exists and explicit RVV host probing is implemented.
- Higher detected host tiers collapse to implemented fallbacks during sibling probing and embedded resource selection:
  `x86_64_avx512 -> x86_64_avx2 -> x86_64_sse2 -> scalar`,
  `aarch64_sve2 -> aarch64_neon -> scalar`,
  `aarch64_sve -> aarch64_neon -> scalar`.

## Deferred Runtime Probing

- Linux-class runtime probing for `aarch64_sve` and `aarch64_sve2` is a plausible follow-up, but it is deferred in v1 and does not block current aarch64 readiness because the shipped runtime matrix already collapses those hosts to `aarch64_neon`.
- Real `riscv64_rvv` runtime probing is also deferred in v1. Because RVV is the only non-x86 optional tier with a potential dedicated runtime artifact in the current matrix, RVV host auto-selection must not be described as first-class unless that probe is explicitly implemented and verified.

## Package Contract

- `simd_tier` remains the legacy single-variant manifest field.
- `runtime_variants[]` adds `{ target_triple, simd_tier, resource_path }` for multi-runtime packages.

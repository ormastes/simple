# Host CPU Runtime Variants Architecture

## Decision

`simple-simd` remains the canonical host-capability authority because it already defines `SimdTier`, raw detection, fallback ordering, and best-implemented-tier collapse. The persisted `cpu_config.sdn` is layered on top of that crate instead of duplicating tier logic elsewhere.

## Flow

1. Raw host detection builds `support`.
2. Current Simple implementation support builds `simple_support`.
3. Canonicalization rewrites `version`, `target_triple`, `generated_by`, `support`, and `simple_support` from current detection data, then clamps `enabled` to a downscoped subset and persists the full canonical file.
4. Compiler/runtime consumers ask `simple-simd` for the active tier.
5. Cache keys and stdlib variant-root resolution derive from that same active tier so a config downscope changes both artifact identity and lookup order.
6. Native loader and package resource selectors use that same active tier.

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
  `riscv64_rvv` when toolchain support exists.
- Higher detected host tiers collapse to implemented fallbacks during sibling probing and embedded resource selection:
  `x86_64_avx512 -> x86_64_avx2 -> x86_64_sse2 -> scalar`,
  `aarch64_sve2 -> aarch64_neon -> scalar`,
  `aarch64_sve -> aarch64_neon -> scalar`.

## Package Contract

- `simd_tier` remains the legacy single-variant manifest field.
- `runtime_variants[]` adds `{ target_triple, simd_tier, resource_path }` for multi-runtime packages.

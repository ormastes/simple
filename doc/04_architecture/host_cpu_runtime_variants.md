# Host CPU Runtime Variants Architecture

## Decision

`simple-simd` remains the canonical host-capability authority because it already defines `SimdTier`, raw detection, fallback ordering, and best-implemented-tier collapse. The persisted `cpu_config.sdn` is layered on top of that crate instead of duplicating tier logic elsewhere.

## Flow

1. Raw host detection builds `support`.
2. Current Simple implementation support builds `simple_support`.
3. `enabled` is clamped to a downscoped subset and persisted.
4. Compiler/runtime consumers ask `simple-simd` for the active tier.
5. Native loader and package resource selectors use that same active tier.

## Package Contract

- `simd_tier` remains the legacy single-variant manifest field.
- `runtime_variants[]` adds `{ target_triple, simd_tier, resource_path }` for multi-runtime packages.


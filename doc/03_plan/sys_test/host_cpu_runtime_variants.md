# Host CPU Runtime Variants System Test Plan

- Verify `cpu_config.sdn` is created on first use and round-trips through the parser.
- Verify invalid `enabled` entries are clamped and rewritten.
- Verify compiler/runtime tier defaults change when `enabled.simd_tier` is downscoped.
- Verify dynamic loader sibling probing prefers suffixed variants before the unsuffixed runtime.
- Verify package manifest round-trip preserves runtime-variant metadata.
- Verify embedded runtime selection chooses the best compatible resource.


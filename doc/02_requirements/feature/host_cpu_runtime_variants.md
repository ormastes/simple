# Host CPU Runtime Variants

## Functional Requirements

- `REQ-001`: The Rust SIMD/common layer shall detect host SIMD support and persist a machine-local `cpu_config.sdn`.
- `REQ-002`: `cpu_config.sdn` shall contain `support`, `simple_support`, and `enabled` sections.
- `REQ-003`: `SIMPLE_CPU_CONFIG_PATH` shall override the default config path.
- `REQ-004`: The default active tier shall resolve by precedence: explicit `SIMPLE_SIMD_TIER`, then `cpu_config.sdn enabled.simd_tier`, then raw host detection.
- `REQ-005`: Invalid `enabled` values shall be clamped to the allowed subset and the config file shall be rewritten.
- `REQ-006`: Dynamic runtime loading shall probe sibling suffixed runtime libraries in compatibility order before the unsuffixed fallback.
- `REQ-007`: Package manifests shall preserve the legacy single-variant fields and also support a runtime-variant index for embedded runtime resources.
- `REQ-008`: Embedded runtime selection shall choose the best compatible runtime resource for the active host tier and target triple.


# Host CPU Runtime Variants Spec

Executable artifact:
- `doc/06_spec/app/compiler/feature/host_cpu_runtime_variants_spec.spl`

## Requirement Coverage

- `REQ-001` to `REQ-004`: expressed in the executable spec and covered by `simple-simd` host config unit tests for first-use persistence, round-trip parsing, `SIMPLE_CPU_CONFIG_PATH`, and active-tier precedence.
- `REQ-005` and `REQ-006`: expressed in the executable spec and covered by `simple-simd` host config canonicalization tests for full-file rewrite, allowed-subset clamping, duplicate removal, and rejection of invalid edits outside `enabled.*`.
- `REQ-006`: also verified by malformed-config reload tests that ensure long-lived processes observe on-disk changes instead of using stale cached data forever.
- `REQ-007`: expressed in the executable spec and covered by `simple-native-loader` dynamic provider tests for sibling probe ordering, default search-path behavior, and fail-fast handling when a higher-priority variant exists but is broken.
- `REQ-008` and `REQ-009`: expressed in the executable spec and covered by loader and runtime package manifest tests for `runtime_variants[]` round-trip, invalid-manifest fail-closed behavior, and embedded-resource fallback when the highest compatible resource is absent.
- `REQ-010`: expressed in the executable spec and covered by compiler cache-key tests plus driver build-cache tests that hash the active SIMD tier instead of raw host detection.
- `REQ-011`: expressed in the executable spec and covered by stdlib variant-root ordering tests plus compiler module/path-resolution tests driven by `cpu_config.sdn`.
- `REQ-012` and `REQ-013`: expressed in the executable spec and covered by loader/interpreter runtime-candidate ordering tests and package runtime-variant selection tests for collapse through implemented v1 fallback tiers.

## Scenario Notes

- Downscoping `enabled.simd_tier` to `scalar` must change compiler defaults, cache identity, stdlib root ordering, and runtime-library selection together.
- Truncated or malformed manifest sections must fail closed and must not silently degrade to scalar/default metadata.
- Embedded runtime selection must continue through lower compatible variants until it finds a present resource.
- The executable `.spl` artifact is intentionally minimal and requirement-oriented; the heavier behavior validation stays in the Rust unit/integration tests named above.

## Artifact Status

- The repo contract now has the expected executable `.spl` system spec for this feature.
- This Markdown file remains the traceability note linking requirement groups to the executable spec and the lower-level Rust verification surface.

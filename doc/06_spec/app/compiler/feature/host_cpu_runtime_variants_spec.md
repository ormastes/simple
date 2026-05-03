# Host CPU Runtime Variants Spec

## Requirement Coverage

- `REQ-001` to `REQ-004`: covered by `simple-simd` host config unit tests for first-use persistence, round-trip parsing, `SIMPLE_CPU_CONFIG_PATH`, and active-tier precedence.
- `REQ-005` and `REQ-006`: covered by `simple-simd` host config canonicalization tests for full-file rewrite, allowed-subset clamping, duplicate removal, and rejection of invalid edits outside `enabled.*`.
- `REQ-006`: also verified by malformed-config reload tests that ensure long-lived processes observe on-disk changes instead of using stale cached config forever.
- `REQ-007`: covered by `simple-native-loader` dynamic provider tests for sibling probe ordering and fail-fast behavior when a higher-priority variant exists but is broken.
- `REQ-008`: covered by loader and runtime package manifest tests for `runtime_variants[]` round-trip, invalid-manifest fail-closed behavior, and embedded-resource fallback when the highest compatible resource is absent.
- `REQ-009`: covered by compiler cache-key tests and driver build-cache tests that hash the active SIMD tier instead of raw host detection.
- `REQ-010`: partially covered by stdlib variant-root helper tests; end-to-end module-resolution coverage remains a follow-up gap outside this file’s ownership.
- `REQ-011` and `REQ-012`: covered by loader/interpreter runtime-candidate ordering tests and package runtime-variant selection tests for collapse through implemented v1 fallback tiers.

## Scenario Notes

- Downscoping `enabled.simd_tier` to `scalar` must change compiler defaults, cache identity, stdlib root ordering, and runtime-library selection together.
- Truncated or malformed manifest sections must fail closed and must not silently degrade to scalar/default metadata.
- Embedded runtime selection must continue through lower compatible variants until it finds a present resource.

## Artifact Status

- The repo contract expects an executable `.spl` system spec for this feature.
- Within this task’s owned-file constraint, this Markdown spec is tightened to record requirement-to-test coverage and the remaining executable-spec gap; creating `doc/06_spec/app/compiler/feature/host_cpu_runtime_variants_spec.spl` remains a follow-up outside the allowed ownership set.

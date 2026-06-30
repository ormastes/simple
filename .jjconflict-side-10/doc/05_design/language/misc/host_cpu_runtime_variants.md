# Host CPU Runtime Variants Design

## CPU Config

- Path:
  `dirs_next::cache_dir()/simple/host/<target-triple>/cpu_config.sdn`
- Override:
  `SIMPLE_CPU_CONFIG_PATH`
- Fallback:
  `~/.simple/cache/host/<target-triple>/cpu_config.sdn`

## Selection Rules

- Active tier precedence:
  1. `SIMPLE_SIMD_TIER`
  2. `cpu_config.sdn enabled.simd_tier`
  3. raw `detect_profile()`
- Default `enabled.simd_tier` uses the best currently implemented tier for the host family.
- In v1, `detect_profile()` is fully first-class for x86_64 and for baseline aarch64 NEON selection, but optional non-x86 runtime probes for `aarch64_sve`, `aarch64_sve2`, and `riscv64_rvv` are deferred. Those capabilities are therefore conservative unless a target-specific probe is explicitly added later.
- Canonical rewrite refreshes `version`, `target_triple`, `generated_by`, `support`, `simple_support`, and `enabled` from the current host/config rules on each accepted load.
- `simple_support.instruction_sets` contains only instruction sets currently backed by shipped Simple fallbacks, not every host-detected capability.
- `enabled.instruction_sets` is clamped to `support ∩ simple_support`, deduplicated, and rewritten in stable schema order.
- Editing `support` or `simple_support` is not a supported control surface; only `enabled.*` is user-downscopable.

## Cache And Variant Roots

- Compiler object-cache keys and interpreter path-resolution cache keys include the active SIMD tier name.
- Test-runner build cache keys also follow the active SIMD tier rather than raw host detection.
- Stdlib variant-root candidate ordering is tier-sensitive, so a downscoped config changes both cache identity and which stdlib/runtime root is searched first.

## Loader Rules

- Probe suffixed sibling names first:
  `libsimple_runtime.<tier>.so`
  `libsimple_runtime.<tier>.dylib`
  `simple_runtime.<tier>.dll`
- Fallback to unsuffixed scalar/common runtime last.
- Probe only implemented v1 dedicated variants:
  `x86_64_sse2`, `x86_64_avx2`, `aarch64_neon`, and `riscv64_rvv` only when explicit RVV host probing is available for that target.
- Collapse unimplemented higher tiers through compatible fallbacks before the unsuffixed runtime:
  `x86_64_avx512 -> x86_64_avx2 -> x86_64_sse2 -> scalar`,
  `aarch64_sve2 -> aarch64_neon -> scalar`,
  `aarch64_sve -> aarch64_neon -> scalar`.
- Embedded runtime selection follows the same collapse order and continues to lower compatible entries when higher-tier metadata exists but the corresponding embedded resource is absent.

## v1 Non-Blocking Limits

- Conservative under-detection of `aarch64_sve` and `aarch64_sve2` is not a v1 release blocker because those hosts already select the shipped `aarch64_neon` fallback path.
- Conservative under-detection of `wasm128` is not a v1 release blocker because wasm still collapses to scalar/common behavior in this feature slice.
- `riscv64_rvv` is different: if no explicit RVV runtime probe exists, documentation and packaging must not claim first-class RVV host auto-selection. A build may still carry an RVV artifact, but automatic host selection for that artifact is only supported where RVV detection is explicitly implemented and verified.

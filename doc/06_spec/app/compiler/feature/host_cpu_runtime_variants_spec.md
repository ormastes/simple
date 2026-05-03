# Host CPU Runtime Variants Spec

Executable artifact:
- `doc/06_spec/app/compiler/feature/host_cpu_runtime_variants_spec.spl`

## What The Executable Spec Now Verifies Directly

The `.spl` file is no longer only a literal contract model. It now uses current
Simple-facing runtime hooks plus real temp files and environment variables to
exercise the feature in-process where that is actually exposed today.

Direct behavioral coverage now includes:
- writing a fresh `cpu_config.sdn` at an explicit `SIMPLE_CPU_CONFIG_PATH` on first use
- editing that same file and observing the active runtime SIMD tier change again in the same process
- explicit override precedence: `SIMPLE_SIMD_TIER` over `cpu_config.sdn`
- invalid override fallback back to `cpu_config.sdn enabled.simd_tier`
- canonical rewrite of malformed `enabled.instruction_sets` after a real runtime read

The behavioral hook used is the runtime-exported `rt_numeric_active_simd_tier()`
symbol, because it is currently the strongest repo-exposed Simple entrypoint
that flows through the active-tier resolution path backed by the Rust host CPU
config implementation.

## What Still Remains Modeled

Some feature areas are still not observable from SSpec through a stable
Simple-facing API:
- native loader sibling-library probe ordering
- embedded package `runtime_variants` selection
- fail-closed package manifest parsing
- compiler stdlib variant-root search order
- compiler and driver tier-sensitive cache-key formation

Those behaviors remain in the `.spl` as explicit contract-model scenarios, not
as fake “black-box” claims. The markdown and the test names keep that split
visible.

## Why The Spec Stops There

This follow-up was intentionally limited to the spec files, and the repo still
does not expose direct Simple-callable APIs for:
- parsing `cpu_config.sdn` through the Rust host-config module
- asking the native loader for its candidate library list
- invoking package runtime-variant selection directly
- querying compiler/module-loader stdlib root candidates directly from SSpec

Without those hooks, pretending to verify those paths end-to-end from `.spl`
would be dishonest. The strongest feasible black-box coverage today is the
runtime active-tier path, because it is reachable from Simple through a real
runtime symbol and it performs actual config reads and rewrites.

## Traceability Split

- `REQ-001` to `REQ-006`: directly behavior-tested in the `.spl` via temp
  `cpu_config.sdn` files, env changes, real runtime calls, and rewritten-file
  assertions.
- `REQ-007` to `REQ-013`: still modeled in the `.spl` and backed by the Rust
  unit/integration tests added across `simple-native-loader`, package readers,
  `simple-compiler`, and `simple-driver`.

## Residual Limitation

If the repo later exposes stable Simple-facing hooks for loader candidate
enumeration, package runtime selection, or compiler stdlib root resolution, the
remaining modeled sections should be upgraded to the same temp-file/env-driven
behavioral style used here.

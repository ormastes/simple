# Host CPU Runtime Variants Spec

Executable artifact:
- `doc/06_spec/app/compiler/feature/host_cpu_runtime_variants_spec.spl`

## What The Executable Spec Now Verifies Directly

The `.spl` file is no longer only a literal contract model, but the strongest
behavioral path currently reachable from `simple test` is narrower than hoped.

Direct executable coverage now shells out to the source-of-truth Rust test
suite in `simple-simd` and asserts that the relevant host-config regressions
pass in a fresh isolated Cargo target dir. That executable check covers the
real implementation for:
- first-use `cpu_config.sdn` generation
- invalid `enabled` clamp and rewrite
- `SIMPLE_CPU_CONFIG_PATH` override handling
- explicit override precedence over config
- reload after an on-disk edit in the same process
- canonical rewrite using `support ∩ simple_support`

For non-x86 optional runtime detection, the spec intentionally treats v1 as conservative unless an explicit target probe exists. That means this feature is not blocked by missing direct runtime probes for `aarch64_sve` or `aarch64_sve2`, because current shipped behavior collapses those hosts to `aarch64_neon`. It is also not blocked by the lack of `wasm128` runtime probing in this slice. By contrast, `riscv64_rvv` auto-selection is only considered first-class when explicit RVV host probing exists and is verified.

This is still a real black-box command path from SSpec, but it is command-level
behavioral verification rather than in-process function calls.

## Why The Spec Does Not Call The Runtime Internals Directly

I attempted to upgrade the spec further by calling a real runtime symbol from
the `.spl` itself after writing temp config files. That works for `bin/simple -c`
sources, but the `simple test` runner does not expose that symbol to SSpec
execution. In other words:
- the direct runtime hook exists in some Simple execution contexts
- the SSpec runner used for this file cannot link it today

Because of that limitation, the most honest executable route from this spec is:
1. run a real command from SSpec
2. build the current Rust implementation
3. assert that the relevant implementation tests passed

## What Still Remains Modeled

Some feature areas are still not observable from SSpec through a stable
Simple-facing API:
- native loader sibling-library probe ordering
- embedded package `runtime_variants` selection
- fail-closed package manifest parsing
- compiler stdlib variant-root search order, modeled to match the real
  `src/lib/std/variants/<tier>/src` layout
- compiler and driver tier-sensitive cache-key formation

Those behaviors remain in the `.spl` as explicit contract-model scenarios, not
as fake “black-box” claims. The markdown and the test names keep that split
visible.

## Why The Spec Stops There

This follow-up was intentionally limited to the spec files, and the repo still
does not expose stable Simple-callable APIs for:
- parsing `cpu_config.sdn` through the Rust host-config module from SSpec
- asking the native loader for its candidate library list
- invoking package runtime-variant selection directly
- querying compiler/module-loader stdlib root candidates directly from SSpec
- observing invalid override fallback in-process from the test runner itself

Without those hooks, pretending to verify those paths end-to-end from `.spl`
would be dishonest, so the remaining sections stay explicitly modeled.

## Traceability Split

- `REQ-001` to `REQ-006`: executable command-level verification plus one small
  remaining precedence model for invalid-override fallback.
- `REQ-007` to `REQ-013`: still modeled in the `.spl` and backed by the Rust
  unit/integration tests added across `simple-native-loader`, package readers,
  `simple-compiler`, and `simple-driver`.

## Residual Limitation

If the repo later exposes stable Simple-facing hooks for host-config reads,
loader candidate enumeration, package runtime selection, or compiler stdlib
root resolution inside the SSpec runner, this file should be upgraded again
from command-level verification to direct temp-file/env-driven behavioral
scenarios.

Separate from that observability gap, v1 also defers real runtime probing for
optional non-x86 tiers such as `aarch64_sve`, `aarch64_sve2`, and
`riscv64_rvv`. This spec therefore treats those paths as contract limits, not
as global release blockers. Only a release that explicitly promises RVV host
auto-selection would need RVV probing to move from deferred work to required
coverage here.

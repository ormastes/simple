<!-- codex-design -->
# GPU/Web Differential Oracle Detail Design

## Implemented shared slice

- `src/lib/common/spec/differential_trace.spl`: immutable schema validation.
- `src/lib/nogc_sync_mut/test/differential_conformance.spl`: `GpuEnvironmentProfile`,
  `ReferenceOracleAdapter`, semantic policy/result, comparison and profile
  admission.
- `test/01_unit/lib/nogc_sync_mut/gpu/differential_oracle_spec.spl`: mapped
  handles, pixel/layer mutation, malformed sequence, environment/fence/readback,
  budget, and test-only adapter contract.

`simpleos_qemu_gpu_environment_profiles()` exports the three canonical IDs.
The x86_64 QEMU contract uses `virtio-gpu-pci`; the AArch64 and RISC-V QEMU
contracts explicitly use `virtio-gpu-mmio`. All three require 3D,
capset-query-fix, resource-blob, host-visible, and context-init; device
execution/fence/device-origin-readback; and no fallback.

## Adapter algorithm

1. The fixture receives a deterministic run ID and environment profile.
2. Candidate and independent reference adapter each emit `TraceEvent`s at their
   own layer boundary.
3. Adapter replaces transient handles with deterministic IDs and records only
   operation-specific semantic digest/scalar facts. It records its canonical UI
   profile, arch/transport, required feature facts, Venus/device/oracle identity,
   device-origin readback, fallback, dropped-event count, and completion state.
4. Test supplies a paired candidate/reference ID mapping. The comparator checks
   ordered events and mapped parent lineage; it never maps an unknown ID.
5. The environment profile gates required operations, UI profile, architecture,
   transport, feature conjunction, Venus/device/oracle identity, no-fallback,
   and live evidence before a trace comparison can be promoted.
6. Mutation suite changes exactly one property at a time and asserts rejection.

## Next implementation lanes

| Lane | Files | Contract |
|---|---|---|
| Dynamic oracle owner | `src/lib/nogc_sync_mut/gpu/reference_oracle_sffi.spl` | versioned `libvulkan`/Mesa symbol probe, ABI/ownership/error values; test-only importers |
| Vulkan/Venus adapter | `test/helpers/gpu_reference_oracle.spl` | discovery/capset/submit/fence/readback semantic events |
| Web/Chrome adapter | `test/helpers/web_reference_oracle.spl` | DOM/style/layout/paint/composite semantic projection plus artifact pointer |
| GPU live profile suite | `test/03_system/os/qemu/*` | no fallback, actual device identity, exact pixels, environment facts |
| Browser profile suite | `test/02_integration/rendering/*` | fixed viewport, stage projection, reviewed bitmap and negative mutations |

The Chromium browser profile is further frozen by
`doc/05_design/chromium_web_renderer_primitive_differential.md`: it has one
test-only bridge library, caller-owned bounded JSON output, explicit handle
release, primitive-only stage projections, and a distinct Simple GPU receipt.
It reuses `NormalizedTrace`/`GpuEnvironmentProfile`; it does not add a generic
Chrome display-list converter or a production browser backend.

Each lane owns only the listed new file(s). Merge owner: `/root`. Lower-model
sidecars: N/A (interfaces were frozen by the coordinating highest-capability
agents). Final reviewer: normal/highest-capability root agent.

## SFFI acceptance tests

Compiled-mode tests must cover missing library, missing symbol, ABI/version
mismatch, null result, failed call, rejected ownership release, and successful
load/unload. The adapter must also prove it does not cause a production import
and does not claim an unavailable provider as a pass. Reference output is
evidence only; CPU scalar exact oracle and device-origin pixels remain separate
requirements.

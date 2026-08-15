# Engine2D strict create: enum identity mismatch across import alias paths

Date: 2026-08-15
Status: WORKED AROUND IN STDLIB; UNDERLYING COMPILER DEFECT OPEN

## Symptom

`Engine2D.create_with_backend_strict(16, 16, "vulkan")` returned
`Err(probe)` whose diagnostic read
`requested=vulkan;selected=vulkan;status=Initialized;...;reason=Vulkan initialized`
— i.e. the probe SUCCEEDED, yet the strict path treated it as
not-initialized. This made
`scripts/check/check-vulkan-engine2d-readback.shs` report
`present_exercised=false / readback_exercised=false / spec_status=not_run /
overall=fail` on a host with a fully working NVIDIA Vulkan stack
(TITAN RTX, `simple-runtime/vulkan` feature build).

## Root cause

`src/lib/gc_async_mut/gpu/engine2d/engine.spl` imports the probe types via
the ALIAS module path:

    use std.gpu.engine2d.backend_probe.{BackendProbeResult, BackendStatus}

while the `BackendProbeResult` object is constructed inside the canonical
module (`std.gc_async_mut.gpu.engine2d.backend_probe`). Under native
codegen the two import paths yield distinct enum identities, so inside
engine.spl `probe.status == BackendStatus.Initialized` is ALWAYS false even
when `backend_status_text(probe.status)` prints `Initialized`. A repro
script importing the enum via the canonical path performed the identical
comparison on the identical probe and got `true`.

## Fix applied (stdlib workaround)

`create_with_backend_strict` now calls `backend_probe_initialized(probe)`
— the comparison executes inside the enum's defining module, where the
identity is consistent — instead of comparing `probe.status` locally
(`src/lib/gc_async_mut/gpu/engine2d/engine.spl`, import line 57 + strict
create body ~line 789). While diagnosing, the if/match tail-expression body
was also rewritten with explicit `return`s.

## Still open

- Compiler: enum values must compare equal regardless of which alias path
  the comparing module used to import the enum type.
- engine.spl has further `probe.status == BackendStatus.Initialized`
  comparisons (~lines 949-1128, backend auto-selection) that are likely
  equally false-negative under native codegen and silently degrade backend
  selection; they should be migrated to `backend_probe_initialized` or
  fixed by the compiler-level fix.

## Related

- `scripts/check/check-vulkan-engine2d-readback.shs` also passed
  `--no-daemon` to `simple test`, which the pure-Simple test runner rejects
  (`Error: unknown option: --no-daemon`) — the real flag is
  `--no-session-daemon`. Fixed in the same change; with both fixes the lane
  reports `overall=pass` with `spec_status=pass` on the TITAN RTX host.

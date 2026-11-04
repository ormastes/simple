# Metal engine2d backend has no Linux emulation lane — blocked on non-macOS hosts

- **Date:** 2026-08-19
- **Status:** BLOCKER-DOCUMENTED (2026-11-04) — host-neutral verification lane exists; GPU-execution lane needs an owner decision. Not a code defect.
- **Owner/lane:** Linux — `crosscompile_xray_lead/linux_adapter` (reassigned 2026-11-04 by owner decision; removed from the macOS lane and its open count).
- **Area:** rendering / engine2d backend matrix

## Evidence

Real browser launch on this Linux host (backend-resolve log):

```
[backend-resolve] metal rejected: unavailable: Metal requires macOS
```

Source of the gate:
- `src/lib/gc_async_mut/gpu/engine2d/backend_metal.spl:286-291` — `probe_metal()`
  returns `BackendProbeResult.unavailable("metal", "Metal requires macOS")`
  whenever `is_macos()` is false, before any session init is attempted.
- `src/lib/gc_async_mut/gpu/engine2d/backend_metal.spl:393-399` —
  `MetalBackend.init()` hard-fails off macOS with
  `last_error = "Metal requires macOS"`.
- `src/lib/nogc_sync_mut/gpu/engine2d/metal_session.spl:154` — the nogc session
  layer carries the same gate.

## Why no emulation lane exists

Unlike DirectX (which has an honest Linux compatibility path,
`directx-software-emulation`, backed by a DXVK/vk-ICD probe plus CPU raster,
plus a separate `directx-on-vulkan` lane), there is no MoltenVK-reverse-style
shim (Metal-on-Vulkan) or software-Metal RenderBackend anywhere in
`src/lib/gc_async_mut/gpu/engine2d/`. `src/lib/gc_async_mut/processing/metal_emulator.spl`
exists but is a compute-pipeline emulator for the processing layer, not a
`RenderBackend` — it cannot serve the engine2d render lane.

## Verdict

The metal backend config cannot be exercised on this host. The rejection is
honest and correct; do not fake a lane. Coverage on Linux is limited to the
availability contract, pinned by
`test/02_integration/rendering/backend_emulation_spec.spl`
("metal availability" context: on non-macOS the probe must report exactly
"Metal requires macOS").

## Unblock options (if ever wanted)

1. Run the existing lane on a real macOS host
   (`test/02_integration/rendering/macos_metal_2d_live_harness.spl`).
2. Implement a disclosed `metal-software-emulation` RenderBackend mirroring the
   DirectX pattern (honest renamed lane, CPU raster, probe-gated).

## 2026-11-04 triage (metalemu lane, release/1.0.0)

**What already exercises the Metal backend on Linux CI (no GPU claimed):**

- `test/02_integration/rendering/metal_msl_pipeline_spec.spl` — two
  host-neutral source-contract scenarios: every mandatory session pipeline maps
  to exactly one MSL `kernel` entry point in `backend_metal_msl.spl`, and a
  device-glass receipt stays separate from CPU-mirror execution. Its dispatch
  scenarios fall to an explicit `is_macos() == false` assertion off macOS
  (non-vacuous OS gate, not a pass).
- `test/02_integration/rendering/engine2d_shared_raster_parity_spec.spl` plus
  `src/lib/gc_async_mut/gpu/engine2d/backend_emu.spl` — the "Metal-exact" CPU
  twin kernels (circle, rounded rect, triangle, `lerp_channel`) pinned
  bit-for-bit against SoftwareBackend. This is the algorithmic half of a
  Metal emulation lane and is host-neutral.
- `test/02_integration/rendering/backend_emulation_spec.spl` — the availability
  contract ("Metal requires macOS").

These specs were not re-run in this change (doc-only triage); they are cited
from the tree at `origin/release/1.0.0`.

**What cannot be done honestly in-repo without an owner decision:**

1. *MSL compile check on Linux.* Apple ships no Linux `metal` front-end; the
   only real compiler is `xcrun metal` / `MTLDevice.newLibraryWithSource`.
   A third-party MSL parser (or a Simple-written one) would validate syntax,
   not Apple's semantics — owner must decide whether that is worth carrying.
2. *GPU execution.* There is no Metal-on-Vulkan runtime. A
   `metal-software-emulation` RenderBackend (DirectX pattern) would execute on
   the CPU through the same `backend_emu` kernels already covered above, so it
   adds a renamed lane, not new evidence. Not implemented: it would be
   over-engineering with no gain in coverage.
3. *Real Metal in CI.* `gpu-lane-tests.yml` already has a `macos-latest`
   matrix row; running `metal_msl_pipeline_spec.spl` there is the honest GPU
   lane, gated on a runner with a usable `bin/simple` (CI baseline has none —
   see `publish` job notes in `.claude/rules/vcs.md`).

**Recommendation:** option 3 (macOS runner) once a self-hosted macOS
`bin/simple` is admitted by the bootstrap lane; until then the Linux coverage
is the source-contract + CPU-twin parity listed above. Remaining gap: no
Linux-side MSL compile and no GPU execution off macOS.

## 2026-11-04 handoff to the Linux lane (owner decision)

The owner ruled this belongs to the Linux side, not the macOS lane: it is a
Linux capability request (no Metal coverage off macOS), not a native macOS
defect. It is reassigned to `crosscompile_xray_lead/linux_adapter` and removed
from the macOS inventory count (`arm64_macos_audit_20261103/current_inventory.*`).
Handoff summary of what PR #6570 recorded: Linux already has host-neutral
coverage (`metal_msl_pipeline_spec.spl` source contract,
`engine2d_shared_raster_parity_spec.spl` + `backend_emu.spl` Metal-exact CPU
twins, `backend_emulation_spec.spl` availability contract). Open choices for the
Linux owner: (1) an MSL syntax checker on Linux (third-party or Simple-written;
validates syntax only, not Apple semantics); (2) a disclosed
`metal-software-emulation` backend (DirectX pattern) — judged to add a renamed
lane but no new evidence; (3) real Metal on the `macos-latest` row of
`gpu-lane-tests.yml`, gated on an admitted self-hosted macOS `bin/simple` —
the recommended path. Remaining gap unchanged: no Linux-side MSL compile and no
GPU execution off macOS.

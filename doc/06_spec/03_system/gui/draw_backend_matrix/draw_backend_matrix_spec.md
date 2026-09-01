# Per-Backend Drawing Matrix — System-Specific Checkpoints

> One SHARED body — probe, create-success, draw-apply, readback-verify — run against every 2D drawing backend key Engine2D exposes: `software` (the absolute reference), `cpu`, `directx`, `vulkan`, and `metal`. Availability is never silently skipped: a backend that cannot init on this host reports a concrete `host-unavailable(reason)`, and asserting that classification IS the system-specific checkpoint's pass condition (fail-closed, per the intensive GPU/draw/event test plan).

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Per-Backend Drawing Matrix — System-Specific Checkpoints

One SHARED body — probe, create-success, draw-apply, readback-verify — run against every 2D drawing backend key Engine2D exposes: `software` (the absolute reference), `cpu`, `directx`, `vulkan`, and `metal`. Availability is never silently skipped: a backend that cannot init on this host reports a concrete `host-unavailable(reason)`, and asserting that classification IS the system-specific checkpoint's pass condition (fail-closed, per the intensive GPU/draw/event test plan).

## At a Glance

| Field | Value |
|-------|-------|
| Category | Testing \| **Status:** Implemented |
| Status | Active |
| Requirements | N/A |
| Plan | doc/03_plan/ui/testing/gpu_draw_event_intensive_tests.md |
| Design | N/A |
| Research | N/A |
| Source | `test/03_system/gui/draw_backend_matrix/draw_backend_matrix_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

One SHARED body — probe, create-success, draw-apply, readback-verify — run
against every 2D drawing backend key Engine2D exposes: `software` (the
absolute reference), `cpu`, `directx`, `vulkan`, and `metal`. Availability is
never silently skipped: a backend that cannot init on this host reports a
concrete `host-unavailable(reason)`, and asserting that classification IS the
system-specific checkpoint's pass condition (fail-closed, per the intensive
GPU/draw/event test plan).

Every readback assertion is an ABSOLUTE oracle — a known drawn pixel equals
the draw color, a known background pixel equals the clear color — never a
cross-backend diff alone. This avoids the false-green history documented in
`doc/07_guide/ui/engine2d_cpu_metal_bit_parity.md` (software-vs-itself
tautology, MATCH-only comparisons, memorized pixel tables).

## Key Concepts

| Concept | Description |
|---------|-------------|
| Probe | `Engine2D.probe_backend(w, h, key)` — native-only availability (no emulation fallback), so `metal` reports honestly `Unavailable` off macOS. It runs its own create+init+shutdown and throws it away, so its answer is a PREDICTION: only its SELF-consistency is asserted, never the create outcome |
| Create-attempt | `Engine2D.create_requested_backend` is a SECOND, INDEPENDENT create and is attempted regardless of the probe. On success it must resolve to the backend's own honest self-reported name (`directx` → `directx-software-emulation`), catching alias dishonesty; a probe/create divergence is disclosed on a `[toctou]` line |
| Readback provenance | `read_pixels_with_source()` feeds `assert_provenance_invariants` unconditionally on every backend and outcome, and `report_outcome` prints `GPU-PROVEN` or an explicit `GPU BRANCH SKIPPED … proves NOTHING about the GPU path` |
| Draw-apply | one filled rect + one line drawn on a real framebuffer |
| Readback-verify | `read_pixels()` download; rect interior == rect color, line pixel == line color, far pixel == background — an absolute pixel oracle, fed through the shared `read_pixels_ppm` (P6) encoder |
| Vulkan device lane | `bin/simple test` runs specs in the classic interpreter, so real `vkCreateInstance`/`vkCmdDispatch` execute without any extra env var (see `doc/07_guide/ui/gpu_backends/vulkan_backed_rendering.md`) |

## Related Specifications

- `test/01_unit/lib/gc_async_mut/gpu/engine2d/engine2d_env_backend_select_spec.spl` — the `SIMPLE_2D_BACKEND` override model this spec's shared checkpoint follows
- `test/01_unit/lib/gc_async_mut/gpu/engine2d/backend_vulkan_drawing_spec.spl` — Vulkan lane hardening (structured error classification)
- `test/01_unit/lib/gc_async_mut/gpu/engine2d/vulkan_compute_oracle_spec.spl` — the honest device-count-zero gate this spec's Vulkan lane mirrors
- `test/02_integration/lib/gpu/cpu_sw_primitive_readback_spec.spl` — the shared per-primitive readback body this spec reuses

## Syntax

Steps are grouped `probe` → `create-success` → `draw-apply` → `readback-verify`
per backend `it`. `std.spec` matchers only; facades only (`std.io_runtime`
`env_set`), no raw `rt_*` externs.

## Scenarios

### Draw backend matrix — per-combination system-specific checkpoints

#### software (baseline): always available, honest name, draw-apply, readback-verify

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- software (baseline): always available, honest name, draw-apply, readback-verify


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("software (baseline): always available, honest name, draw-apply, readback-verify")
run_backend_lane("software", "software")
```

</details>

#### cpu: always available, honest name, draw-apply, readback-verify

- cpu: always available, honest name, draw-apply, readback-verify


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("cpu: always available, honest name, draw-apply, readback-verify")
run_backend_lane("cpu", "cpu")
```

</details>

#### directx: honest CPU software-emulation name, draw-apply, readback-verify (or host-unavailable)

- directx: honest CPU software-emulation name, draw-apply, readback-verify (or host-unavailable)


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("directx: honest CPU software-emulation name, draw-apply, readback-verify (or host-unavailable)")
# Never claims a native D3D11 driver: create_requested_backend stamps
# the backend's own self-reported "directx-software-emulation" name,
# not the requested "directx" key.
run_backend_lane("directx", "directx-software-emulation")
```

</details>

#### vulkan: real device draw-apply + readback-verify under the classic interpreter (or host-unavailable)

- vulkan: real device draw-apply + readback-verify under the classic interpreter (or host-unavailable)


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("vulkan: real device draw-apply + readback-verify under the classic interpreter (or host-unavailable)")
# bin/simple test runs in the classic interpreter, so real
# vkCreateInstance/vkCmdDispatch execute here when a device is
# present — no extra env var needed (see vulkan_backed_rendering.md).
run_backend_lane("vulkan", "vulkan")
```

</details>

#### metal: honest host-unavailable classification off macOS (or native draw-apply on macOS)

- metal: honest host-unavailable classification off macOS (or native draw-apply on macOS)


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("metal: honest host-unavailable classification off macOS (or native draw-apply on macOS)")
# Engine2D.probe_backend("metal", ...) tries ONLY native MetalBackend
# (no metal-on-vulkan emulation fallback), so on this Linux host it
# must report Unavailable with a concrete reason — the system-specific
# checkpoint behavior the plan asks for. On macOS it would report
# Initialized and the shared body runs the real GPU draw-apply path.
run_backend_lane("metal", "metal")
```

</details>

#### directx: extended drawing-op parity with checked Metal surface (rounded_rect outline, gradient linear/radial, shadow, scaled+transform image) — absolute pixel oracle (or host-unavailable)

- directx: extended drawing-op parity with checked Metal surface (rounded_rect outline, gradient linear/radial, shadow, scaled+transform image) — absolute pixel oracle (or host-unavailable)


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("directx: extended drawing-op parity with checked Metal surface (rounded_rect outline, gradient linear/radial, shadow, scaled+transform image) — absolute pixel oracle (or host-unavailable)")
# Confirms DirectXBackend forwards these extended ops to the same
# honest internal SoftwareBackend that already rasterizes its base
# RenderBackend ops, closing the delta against Metal's inherent-method
# surface (see backend_directx.spl impl Engine2DExtended).
assert_directx_extended_ops()
```

</details>

#### vulkan: extended drawing-op parity with checked Metal surface (rounded_rect outline, gradient linear/radial, shadow, scaled+transform image) — absolute pixel oracle (or host-unavailable)

- vulkan: extended drawing-op parity with checked Metal surface (rounded_rect outline, gradient linear/radial, shadow, scaled+transform image) — absolute pixel oracle (or host-unavailable)


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("vulkan: extended drawing-op parity with checked Metal surface (rounded_rect outline, gradient linear/radial, shadow, scaled+transform image) — absolute pixel oracle (or host-unavailable)")
# Confirms VulkanBackend's existing emu-composed extended ops (already
# present pre-change) produce the same exact pixels as the shared
# backend_emu.spl/backend_emu_adv.spl algorithm DirectX/software use.
assert_vulkan_extended_ops()
```

</details>

#### SIMPLE_2D_BACKEND override selects software when it initializes (model: engine2d_env_backend_select_spec)

- SIMPLE_2D_BACKEND override selects software when it initializes (model: engine2d_env_backend_select_spec)
- set SIMPLE_2D_BACKEND=software and confirm auto-detect honors it
   - Expected: Engine2D.detect_best_backend() equals `software`
- clear the override so later runs auto-probe again
- RUN VERDICT reading rule


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("SIMPLE_2D_BACKEND override selects software when it initializes (model: engine2d_env_backend_select_spec)")
step("set SIMPLE_2D_BACKEND=software and confirm auto-detect honors it")
env_set("SIMPLE_2D_BACKEND", "software")
expect(Engine2D.detect_best_backend()).to_equal("software")
step("clear the override so later runs auto-probe again")
env_set("SIMPLE_2D_BACKEND", "")

step("RUN VERDICT reading rule")
# Deliberately NOT quoting the literal marker tokens: a verdict line that
# contains them is counted by `grep -c` and inflates the very number it
# is explaining (this turned a true 0 into a reported 1).
print "[RUN VERDICT] A green run of this spec does NOT by itself mean a GPU was exercised."
print "[RUN VERDICT] Count the per-lane GPU/PROVEN disclosure lines: those, and only those, are"
print "[RUN VERDICT] frames a device produced (device_readback + handle > 0 + identity > 0 + full frame)."
print "[RUN VERDICT] Every GPU/BRANCH/SKIPPED line proves NOTHING about the GPU path, and a"
print "[RUN VERDICT] '[toctou]' line means the probe's prediction did not survive to the create."
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Plan:** `doc/03_plan/ui/testing/gpu_draw_event_intensive_tests.md`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `c7f71e33c71c91f1641922c25fc38684fddcad74078e6ee62b3d6b3ef011ba31`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `c7f71e33c71c91f1641922c25fc38684fddcad74078e6ee62b3d6b3ef011ba31`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `c7f71e33c71c91f1641922c25fc38684fddcad74078e6ee62b3d6b3ef011ba31`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/gui/draw_backend_matrix/draw_backend_matrix_spec.spl
mirror: doc/06_spec/03_system/gui/draw_backend_matrix/draw_backend_matrix_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/gui/draw_backend_matrix/draw_backend_matrix_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/gui/draw_backend_matrix/draw_backend_matrix_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/gui/draw_backend_matrix/draw_backend_matrix_spec.spl:296:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'software (baseline): always available, honest name, draw-apply, readback-verify' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/gui/draw_backend_matrix/draw_backend_matrix_spec.spl:301:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'cpu: always available, honest name, draw-apply, readback-verify' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/gui/draw_backend_matrix/draw_backend_matrix_spec.spl:306:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'directx: honest CPU software-emulation name, draw-apply, readback-verify (or host-unavailable)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

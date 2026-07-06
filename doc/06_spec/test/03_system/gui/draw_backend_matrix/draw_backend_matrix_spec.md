# Per-Backend Drawing Matrix — System-Specific Checkpoints

> One SHARED body — probe, create-success, draw-apply, readback-verify — run against every 2D drawing backend key Engine2D exposes: `software` (the absolute reference), `cpu`, `directx`, `vulkan`, and `metal`. Availability is never silently skipped: a backend that cannot init on this host reports a concrete `host-unavailable(reason)`, and asserting that classification IS the system-specific checkpoint's pass condition (fail-closed, per the intensive GPU/draw/event test plan).

<!-- sdn-diagram:id=draw_backend_matrix_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=draw_backend_matrix_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

draw_backend_matrix_spec -> std
draw_backend_matrix_spec -> test
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=draw_backend_matrix_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

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
| Updated | 2026-07-06 |
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
| Probe | `Engine2D.probe_backend(w, h, key)` — native-only availability (no emulation fallback), so `metal` reports honestly `Unavailable` off macOS even though `directx-on-vulkan`/`metal-on-vulkan` emulation exists elsewhere |
| Create-success | `Engine2D.create_requested_backend` must resolve to the backend's own honest self-reported name (`directx` → `directx-software-emulation`), catching alias dishonesty |
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

- run backend lane


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
run_backend_lane("software", "software")
```

</details>

#### cpu: always available, honest name, draw-apply, readback-verify

- run backend lane


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
run_backend_lane("cpu", "cpu")
```

</details>

#### directx: honest CPU software-emulation name, draw-apply, readback-verify (or host-unavailable)

- run backend lane


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Never claims a native D3D11 driver: create_requested_backend stamps
# the backend's own self-reported "directx-software-emulation" name,
# not the requested "directx" key.
run_backend_lane("directx", "directx-software-emulation")
```

</details>

#### vulkan: real device draw-apply + readback-verify under the classic interpreter (or host-unavailable)

- run backend lane


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# bin/simple test runs in the classic interpreter, so real
# vkCreateInstance/vkCmdDispatch execute here when a device is
# present — no extra env var needed (see vulkan_backed_rendering.md).
run_backend_lane("vulkan", "vulkan")
```

</details>

#### metal: honest host-unavailable classification off macOS (or native draw-apply on macOS)

- run backend lane


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Engine2D.probe_backend("metal", ...) tries ONLY native MetalBackend
# (no metal-on-vulkan emulation fallback), so on this Linux host it
# must report Unavailable with a concrete reason — the system-specific
# checkpoint behavior the plan asks for. On macOS it would report
# Initialized and the shared body runs the real GPU draw-apply path.
run_backend_lane("metal", "metal")
```

</details>

#### SIMPLE_2D_BACKEND override selects software when it initializes (model: engine2d_env_backend_select_spec)

- set SIMPLE_2D_BACKEND=software and confirm auto-detect honors it
- env set
   - Expected: Engine2D.detect_best_backend() equals `software`
- clear the override so later runs auto-probe again
- env set


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("set SIMPLE_2D_BACKEND=software and confirm auto-detect honors it")
env_set("SIMPLE_2D_BACKEND", "software")
expect(Engine2D.detect_best_backend()).to_equal("software")
step("clear the override so later runs auto-probe again")
env_set("SIMPLE_2D_BACKEND", "")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Plan:** [doc/03_plan/ui/testing/gpu_draw_event_intensive_tests.md](doc/03_plan/ui/testing/gpu_draw_event_intensive_tests.md)


</details>

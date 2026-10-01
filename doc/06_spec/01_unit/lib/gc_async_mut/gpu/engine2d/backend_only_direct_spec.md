# Backend-only direct drawing surface — below the Engine2D facade

> This is the layer BELOW `test/03_system/gui/draw_backend_matrix/draw_backend_matrix_spec.spl`. That matrix spec drives every backend THROUGH the `Engine2D` facade (`probe_backend` / `create_requested_backend`). This spec instead constructs each directly-constructible backend object with its own `create()` — no `Engine2D`, no GUI stack — and exercises its own op surface at the lowest owned layer: honest probe -> per-op draw -> direct `read_pixels()` buffer assert with an ABSOLUTE oracle (a known drawn point == the draw color, a known background point == the clear color).

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Backend-only direct drawing surface — below the Engine2D facade

This is the layer BELOW `test/03_system/gui/draw_backend_matrix/draw_backend_matrix_spec.spl`. That matrix spec drives every backend THROUGH the `Engine2D` facade (`probe_backend` / `create_requested_backend`). This spec instead constructs each directly-constructible backend object with its own `create()` — no `Engine2D`, no GUI stack — and exercises its own op surface at the lowest owned layer: honest probe -> per-op draw -> direct `read_pixels()` buffer assert with an ABSOLUTE oracle (a known drawn point == the draw color, a known background point == the clear color).

## At a Glance

| Field | Value |
|-------|-------|
| Category | Testing \| **Status:** Implemented |
| Status | Active |
| Plan | doc/03_plan/ui/testing/gpu_draw_event_intensive_tests.md |
| Source | `test/01_unit/lib/gc_async_mut/gpu/engine2d/backend_only_direct_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

This is the layer BELOW `test/03_system/gui/draw_backend_matrix/draw_backend_matrix_spec.spl`.
That matrix spec drives every backend THROUGH the `Engine2D` facade
(`probe_backend` / `create_requested_backend`). This spec instead constructs
each directly-constructible backend object with its own `create()` — no
`Engine2D`, no GUI stack — and exercises its own op surface at the lowest owned
layer: honest probe -> per-op draw -> direct `read_pixels()` buffer assert with
an ABSOLUTE oracle (a known drawn point == the draw color, a known background
point == the clear color).

Availability is never a silent skip. `software` and `cpu` are pure-CPU and
always init. `directx` and `vulkan` may have no device on this host: they then
fail-closed — `directx` asserts its honest `cpu_mirror` readback provenance plus
`leaf=` dispatch evidence, `vulkan` asserts a CLASSIFIED (never `None`)
`last_error`.

## Key Concepts

| Concept | Description |
|---------|-------------|
| Direct construct | `SoftwareBackend.create()`, `CpuBackend.create()`, `DirectXBackend.create()`, `VulkanBackend.create()` — no facade |
| name() honesty | `software`, `cpu`, `directx-software-emulation` (never plain `directx`), `vulkan` |
| Absolute oracle | filled-rect interior == RED, background == a distinct clear color (both ARGB channels compared, via the shared `assert_color_eq`) |
| Fail-closed | no-device backends assert a concrete reason, never pass green on a no-op |

## Syntax

Shared parameterized body `assert_backend_direct(kind)`; one `it` per backend.
`std.spec` matchers only; the shared `assert_color_eq` / `read_pixels_ppm`
helpers are reused (never duplicated).

## Scenarios

### Backend-only direct drawing — one lane per directly-constructible backend

#### software (baseline): direct construct, honest name, filled-rect readback == RED / BG

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- software (baseline): direct construct, honest name, filled-rect readback == RED / BG


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("software (baseline): direct construct, honest name, filled-rect readback == RED / BG")
assert_backend_direct("software")
```

</details>

#### cpu: direct construct, honest name, filled-rect readback == RED / BG

- cpu: direct construct, honest name, filled-rect readback == RED / BG


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("cpu: direct construct, honest name, filled-rect readback == RED / BG")
assert_backend_direct("cpu")
```

</details>

#### directx: honest directx-software-emulation name; readback == RED/BG or host-unavailable(cpu_mirror+leaf)

- directx: honest directx-software-emulation name; readback == RED/BG or host-unavailable(cpu_mirror+leaf)


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("directx: honest directx-software-emulation name; readback == RED/BG or host-unavailable(cpu_mirror+leaf)")
assert_backend_direct("directx")
```

</details>

#### vulkan: real-device filled-rect readback == RED/BG or host-unavailable(classified last_error)

- vulkan: real-device filled-rect readback == RED/BG or host-unavailable(classified last_error)


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("vulkan: real-device filled-rect readback == RED/BG or host-unavailable(classified last_error)")
assert_backend_direct("vulkan")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Plan:** `doc/03_plan/ui/testing/gpu_draw_event_intensive_tests.md`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `f8f8f619a3f97048c56e414528440285ba6332b6c29e02bafa0c1b6f33c12fec`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `f8f8f619a3f97048c56e414528440285ba6332b6c29e02bafa0c1b6f33c12fec`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `f8f8f619a3f97048c56e414528440285ba6332b6c29e02bafa0c1b6f33c12fec`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/gc_async_mut/gpu/engine2d/backend_only_direct_spec.spl
mirror: doc/06_spec/01_unit/lib/gc_async_mut/gpu/engine2d/backend_only_direct_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/gc_async_mut/gpu/engine2d/backend_only_direct_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/gc_async_mut/gpu/engine2d/backend_only_direct_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/gc_async_mut/gpu/engine2d/backend_only_direct_spec.spl:185:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'software (baseline): direct construct, honest name, filled-rect readback == RED / BG' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gc_async_mut/gpu/engine2d/backend_only_direct_spec.spl:190:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'cpu: direct construct, honest name, filled-rect readback == RED / BG' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gc_async_mut/gpu/engine2d/backend_only_direct_spec.spl:195:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'directx: honest directx-software-emulation name; readback == RED/BG or host-unavailable(cpu_mirror+leaf)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

# Arm64 Wm Shared Mdi Contract Specification

## Scenarios

### ARM64 QEMU WM shared MDI contract

#### reports the canonical shared MDI model and QEMU framebuffer backend

<details>
<summary>Executable SPipe</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val evidence = arm64_wm_shared_mdi_evidence(320, 240)
expect(evidence.surface_count).to_equal(5)
expect(evidence.first_title).to_equal("Terminal")
expect(evidence.focused_title).to_equal("Calculator")
expect(evidence.simple_web_surface_count).to_equal(5)
expect(evidence.renderer_path).to_equal("shared_mdi_framebuffer_scene")
expect(evidence.backend_kind).to_equal("qemu-aarch64-hvf-framebuffer-cpu-simd")
expect(evidence.readback_status).to_equal("qmp-screendump-required")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/qemu/arm64_wm_shared_mdi_contract_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- ARM64 QEMU WM shared MDI contract

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


# Engine 2d Qemu Specification

> <details>

<!-- sdn-diagram:id=engine_2d_qemu_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=engine_2d_qemu_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

engine_2d_qemu_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=engine_2d_qemu_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Engine 2d Qemu Specification

## Scenarios

### Engine2D QEMU graphics-core acceptance contract

#### requires BGA Engine2D verification markers

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val serial = "[E2D] Engine2D verification frame painted\n" +
    "[E2D-PRIM] Engine2D primitive frame painted\n"
expect(_contains_all_markers(serial, [
    "[E2D] Engine2D verification frame painted",
    "[E2D-PRIM] Engine2D primitive frame painted"
])).to_equal(true)
```

</details>

#### requires WM Simple Web Engine2D markers

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val serial = "[wm-demo] wm-service-ready\n" +
    "[e2d-demo] engine-core-ready\n" +
    "[web-demo] pixels-ready count=114400\n" +
    "[integrated-demo] render-ready\n"
expect(_contains_all_markers(serial, [
    "[wm-demo] wm-service-ready",
    "[e2d-demo] engine-core-ready",
    "[web-demo] pixels-ready",
    "[integrated-demo] render-ready"
])).to_equal(true)
```

</details>

#### keeps VirtIO-GPU as proof coverage

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val serial = "[gui-e2d-virtio] render-ready\n"
expect(_contains_all_markers(serial, ["[gui-e2d-virtio] render-ready"])).to_equal(true)
```

</details>

#### requires QMP PPM capture to be non-empty and non-black

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_nonblack_ppm_contract(1024, 768, 1)).to_equal(true)
expect(_nonblack_ppm_contract(1024, 768, 0)).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/app/os/feature/engine_2d_qemu_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Engine2D QEMU graphics-core acceptance contract

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

# Graphical Backend Capture Specification

## Scenarios

### graphical backend capture facade

#### captures browser-rendered pixels through the shared BackendCapture shape

<details>
<summary>Executable SPipe</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val capture = capture_with_backend(_html(), 32, 24, "software")
expect(capture.success).to_equal(true)
expect(capture.backend_name).to_equal("software")
expect(capture.width).to_equal(32)
expect(capture.height).to_equal(24)
expect(capture.pixels.len()).to_equal(32 * 24)
```

</details>

#### captures Engine2D readback pixels for a canonical filled-rect case

<details>
<summary>Executable SPipe</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val capture = capture_engine2d_filled_rect(
    16,
    12,
    "cpu",
    0xFFFFFFFFu32,
    0xFF2563EBu32
)
expect(capture.success).to_equal(true)
expect(capture.pixels.len()).to_equal(16 * 12)
```

</details>

#### feeds shared captures into the wm_compare graphical equality report

<details>
<summary>Executable SPipe</summary>

Runnable source: 45 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val first = capture_engine2d_filled_rect(
    16,
    12,
    "cpu",
    0xFFFFFFFFu32,
    0xFF2563EBu32
)
val second = capture_engine2d_filled_rect(
    16,
    12,
    "cpu",
    0xFFFFFFFFu32,
    0xFF2563EBu32
)
val geometry = surface_geometry(16, 12, first.width, first.height, 1.0, "srgb")
val scenario = render_case(
    "engine2d_filled_rect",
    16,
    12,
    "#ffffff",
    ["clear", "filled_rect"],
    "strict"
)
val expected = graphical_capture(
    "2d:" + first.backend_name,
    "render_target",
    first.pixels,
    geometry,
    first.success,
    first.error
)
val actual = graphical_capture(
    "2d:" + second.backend_name,
    "render_target",
    second.pixels,
    geometry,
    second.success,
    second.error
)
val report = graphical_equality_compare(scenario, expected, actual)
expect(report.pixel_status).to_equal("exact_match")
expect(report.accepted).to_equal(true)
val sdn = graphical_equality_report_sdn(report)
expect(sdn).to_contain("engine2d_filled_rect")
expect(sdn).to_contain("expected_backend: \"2d:cpu\"")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/integration/rendering/graphical_backend_capture_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- graphical backend capture facade

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


# Graphical Backend Equality Specification

> <details>

<!-- sdn-diagram:id=graphical_backend_equality_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=graphical_backend_equality_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

graphical_backend_equality_spec -> std
graphical_backend_equality_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=graphical_backend_equality_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Graphical Backend Equality Specification

## Scenarios

### wm_compare graphical backend equality

#### parses simple and composed backend selectors

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cpu = graphical_backend_spec("2d:cpu")
expect(cpu.valid).to_equal(true)
expect(cpu.primary_kind).to_equal("2d")
expect(cpu.primary_name).to_equal("cpu")
expect(cpu.chain_count).to_equal(1)

val composed = graphical_backend_spec("gui:electron+wm:host")
expect(composed.valid).to_equal(true)
expect(composed.primary_kind).to_equal("gui")
expect(composed.primary_name).to_equal("electron")
expect(composed.chain_count).to_equal(2)
```

</details>

#### rejects invalid backend selectors with reasons

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val invalid = graphical_backend_spec("sound:alsa")
expect(invalid.valid).to_equal(false)
expect(invalid.reason).to_equal("unknown backend kind")

val missing = graphical_backend_spec("2d")
expect(missing.valid).to_equal(false)
expect(missing.reason).to_equal("expected kind:name")

val invalid_chain = graphical_backend_spec("gui:electron+bad:host")
expect(invalid_chain.valid).to_equal(false)
expect(invalid_chain.primary_kind).to_equal("gui")
expect(invalid_chain.reason).to_equal("unknown backend kind")
```

</details>

#### validates normalized capture metadata before pixel comparison

1.  solid
   - Expected: graphical_capture_metadata_valid(capture) is true
2.  solid
   - Expected: graphical_capture_metadata_valid(bad) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val geometry = surface_geometry(4, 3, 4, 3, 1.0, "srgb")
val capture = graphical_capture(
    "2d:cpu",
    "render_target",
    _solid(0xFFFFFFFFu32, 12),
    geometry,
    true,
    ""
)
expect(graphical_capture_metadata_valid(capture)).to_equal(true)

val bad = graphical_capture(
    "2d:cpu",
    "render_target",
    _solid(0xFFFFFFFFu32, 11),
    geometry,
    true,
    ""
)
expect(graphical_capture_metadata_valid(bad)).to_equal(false)
```

</details>

#### rejects invalid capture rectangles and color metadata

1. var geometry = surface geometry
2. geometry content rect = surface rect
3.  solid
   - Expected: graphical_capture_metadata_valid(overflow) is false
4.  solid
   - Expected: graphical_capture_metadata_valid(missing_color) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var geometry = surface_geometry(4, 3, 4, 3, 1.0, "srgb")
geometry.content_rect = surface_rect(2, 0, 4, 3)
val overflow = graphical_capture(
    "2d:cpu",
    "render_target",
    _solid(0xFFFFFFFFu32, 12),
    geometry,
    true,
    ""
)
expect(graphical_capture_metadata_valid(overflow)).to_equal(false)

val empty_color = surface_geometry(4, 3, 4, 3, 1.0, "")
val missing_color = graphical_capture(
    "2d:cpu",
    "render_target",
    _solid(0xFFFFFFFFu32, 12),
    empty_color,
    true,
    ""
)
expect(graphical_capture_metadata_valid(missing_color)).to_equal(false)
```

</details>

#### requires exact equality for strict CPU software cases

1.  solid
2.  solid
   - Expected: report.pixel_status equals `exact_match`
   - Expected: report.shape_status equals `pixel_proxy_match`
   - Expected: report.color_status equals `pixel_proxy_match`
   - Expected: report.accepted is true
   - Expected: report.exact_required is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 31 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val geometry = surface_geometry(4, 3, 4, 3, 1.0, "srgb")
val scenario = render_case(
    "solid_blue",
    4,
    3,
    "#2563eb",
    ["clear", "rect"],
    "strict"
)
val expected = graphical_capture(
    "2d:cpu",
    "render_target",
    _solid(0xFF2563EBu32, 12),
    geometry,
    true,
    ""
)
val actual = graphical_capture(
    "2d:cpu",
    "render_target",
    _solid(0xFF2563EBu32, 12),
    geometry,
    true,
    ""
)
val report = graphical_equality_compare(scenario, expected, actual)
expect(report.pixel_status).to_equal("exact_match")
expect(report.shape_status).to_equal("pixel_proxy_match")
expect(report.color_status).to_equal("pixel_proxy_match")
expect(report.accepted).to_equal(true)
expect(report.exact_required).to_equal(true)
```

</details>

#### reports portable GPU tolerance diagnostics explicitly

1.  solid
2.  near
   - Expected: report.pixel_status equals `tolerance_match`
   - Expected: report.tolerance_acceptance_allowed is true
   - Expected: report.exact_required is false
   - Expected: report.accepted is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 31 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val geometry = surface_geometry(20, 10, 20, 10, 1.0, "srgb")
val scenario = render_case(
    "portable_gpu_blue",
    20,
    10,
    "#2563eb",
    ["clear", "rect"],
    "portable_gpu"
)
val expected = graphical_capture(
    "2d:cpu",
    "render_target",
    _solid(0xFF2563EBu32, 200),
    geometry,
    true,
    ""
)
val actual = graphical_capture(
    "2d:vulkan",
    "render_target",
    _near(200),
    geometry,
    true,
    ""
)
val report = graphical_equality_compare(scenario, expected, actual)
expect(report.pixel_status).to_equal("tolerance_match")
expect(report.tolerance_acceptance_allowed).to_equal(true)
expect(report.exact_required).to_equal(false)
expect(report.accepted).to_equal(true)
expect(report.match_percentage).to_be_greater_than(9849)
```

</details>

#### separates metadata mismatch from pixel mismatch

1.  solid
2.  solid
   - Expected: report.metadata_status equals `metadata_mismatch`
   - Expected: report.pixel_status equals `not_evaluated`
   - Expected: report.accepted is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val expected_geometry = surface_geometry(4, 3, 4, 3, 1.0, "srgb")
val actual_geometry = surface_geometry(4, 3, 5, 3, 1.0, "srgb")
val scenario = render_case("metadata_mismatch", 4, 3, "#fff", ["clear"], "strict")
val expected = graphical_capture(
    "2d:cpu",
    "render_target",
    _solid(0xFFFFFFFFu32, 12),
    expected_geometry,
    true,
    ""
)
val actual = graphical_capture(
    "web:simple",
    "render_target",
    _solid(0xFFFFFFFFu32, 15),
    actual_geometry,
    true,
    ""
)
val report = graphical_equality_compare(scenario, expected, actual)
expect(report.metadata_status).to_equal("metadata_mismatch")
expect(report.pixel_status).to_equal("not_evaluated")
expect(report.accepted).to_equal(false)
```

</details>

#### keeps backend and capture failures separate from drawing equality

1.  solid
2.  solid
   - Expected: report.backend_status equals `backend_invalid`
   - Expected: report.capture_status equals `capture_failed`
   - Expected: report.pixel_status equals `not_evaluated`


<details>
<summary>Executable SSpec</summary>

Runnable source: 27 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val geometry = surface_geometry(4, 3, 4, 3, 1.0, "srgb")
val scenario = render_case("capture_failure", 4, 3, "#fff", ["clear"], "strict")
val expected = graphical_capture(
    "2d:cpu",
    "render_target",
    _solid(0xFFFFFFFFu32, 12),
    geometry,
    true,
    ""
)
val actual = graphical_capture(
    "bad:backend",
    "render_target",
    _solid(0xFFFFFFFFu32, 12),
    geometry,
    false,
    "backend unavailable"
)
val report = graphical_equality_compare(scenario, expected, actual)
expect(report.backend_status).to_equal("backend_invalid")
expect(report.capture_status).to_equal("capture_failed")
expect(report.pixel_status).to_equal("not_evaluated")
val sdn = graphical_equality_report_sdn(report)
expect(sdn).to_contain("graphical_equality_report")
expect(sdn).to_contain("backend_status: \"backend_invalid\"")
expect(sdn).to_contain("metadata_status:")
expect(sdn).to_contain("artifacts:")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/gui/wm_compare/graphical_backend_equality_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- wm_compare graphical backend equality

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

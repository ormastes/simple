# Backend Opencl Text Fallback Specification

> <details>

<!-- sdn-diagram:id=backend_opencl_text_fallback_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=backend_opencl_text_fallback_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

backend_opencl_text_fallback_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=backend_opencl_text_fallback_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Backend Opencl Text Fallback Specification

## Scenarios

### Engine2D OpenCL text fallback

#### uses mirror draw_text without staging a device glyph upload when unavailable

- var backend = OpenClBackend create
   - Expected: backend.mirror.init(8, 8) is true
- backend draw text
   - Expected: backend.device_current is false
   - Expected: pixels.len() equals `64`
- backend shutdown


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var backend = OpenClBackend.create()
expect(backend.mirror.init(8, 8)).to_equal(true)

backend.device_current = true
backend.draw_text(0, 0, "A", 0xff112233u32, 7)

val pixels = backend.read_pixels()
expect(backend.device_current).to_equal(false)
expect(pixels.len()).to_equal(64)

backend.shutdown()
```

</details>

#### uses mirror draw_text_bg without staging a device glyph upload when unavailable

- var backend = OpenClBackend create
   - Expected: backend.mirror.init(8, 8) is true
- backend draw text bg
   - Expected: backend.device_current is false
   - Expected: pixels.len() equals `64`
- backend shutdown


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var backend = OpenClBackend.create()
expect(backend.mirror.init(8, 8)).to_equal(true)

backend.device_current = true
backend.draw_text_bg(0, 0, "A", 0xff112233u32, 0xff445566u32, 7)

val pixels = backend.read_pixels()
expect(backend.device_current).to_equal(false)
expect(pixels.len()).to_equal(64)

backend.shutdown()
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gpu/engine2d/backend_opencl_text_fallback_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Engine2D OpenCL text fallback

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

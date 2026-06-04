# Helpers Text Specification

> <details>

<!-- sdn-diagram:id=helpers_text_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=helpers_text_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

helpers_text_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=helpers_text_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Helpers Text Specification

## Scenarios

### Engine2D shared text blit helpers

#### returns an empty payload for empty text

<details>
<summary>Executable SPipe</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val payload = text_blit_buffer("", 0xffffffffu32, 0xff000000u32, 7)

expect(payload.is_empty()).to_equal(true)
expect(payload.width).to_equal(0)
expect(payload.height).to_equal(0)
expect(payload.pixels.len()).to_equal(0)
```

</details>

#### keeps dimensions and pixels together for background text

<details>
<summary>Executable SPipe</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val payload = text_blit_buffer("I", 0xff111111u32, 0xff222222u32, 7)

expect(payload.is_empty()).to_equal(false)
expect(payload.width > 0).to_equal(true)
expect(payload.height > 0).to_equal(true)
expect(payload.pixels.len()).to_equal(payload.width * payload.height)
```

</details>

#### uses zero pixels as transparent background for foreground text

<details>
<summary>Executable SPipe</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val payload = text_transparent_blit_buffer("A", 0xff111111u32, 7)
val opaque = text_blit_buffer("A", 0xff111111u32, 0xff222222u32, 7)
var differing_count = 0
var idx = 0
while idx < payload.pixels.len():
    if payload.pixels[idx] != opaque.pixels[idx]:
        differing_count = differing_count + 1
    idx = idx + 1

expect(payload.is_empty()).to_equal(false)
expect(payload.width).to_equal(opaque.width)
expect(payload.height).to_equal(opaque.height)
expect(differing_count > 0).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gpu/engine2d/helpers_text_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Engine2D shared text blit helpers

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

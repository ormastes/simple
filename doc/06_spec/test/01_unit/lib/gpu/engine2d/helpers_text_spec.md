# Helpers Text Specification

> 1. var cache = TextBlitCache new

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
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Helpers Text Specification

## Scenarios

### Engine2D shared text blit helpers

#### keeps empty background and transparent payload contracts stable

1. var cache = TextBlitCache new
   - Expected: repeated_first.is_empty() is false
   - Expected: repeated_second.width equals `repeated_first.width`
   - Expected: repeated_second.height equals `repeated_first.height`
   - Expected: cache.cache_misses equals `1`
   - Expected: cache.cache_hits equals `1`
   - Expected: cache.lookup_scan_count equals `repeated_scans_after_miss`


<details>
<summary>Executable SSpec</summary>

Runnable source: 48 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val empty_payload = text_blit_buffer("", 0xffffffffu32, 0xff000000u32, 7)
expect(empty_payload.is_empty()).to_equal(true)
expect(empty_payload.width).to_equal(0)
expect(empty_payload.height).to_equal(0)
expect(empty_payload.pixels.len()).to_equal(0)

val background_payload = text_blit_buffer("I", 0xff111111u32, 0xff222222u32, 7)
var background_fg_count = 0
var background_idx = 0
while background_idx < background_payload.pixels.len():
    if background_payload.pixels[background_idx] == 0xff111111u32:
        background_fg_count = background_fg_count + 1
    background_idx = background_idx + 1

expect(background_payload.is_empty()).to_equal(false)
expect(background_payload.width > 0).to_equal(true)
expect(background_payload.height > 0).to_equal(true)
expect(background_payload.pixels.len()).to_equal(background_payload.width * background_payload.height)
expect(background_fg_count > 0).to_equal(true)

val transparent_payload = text_transparent_blit_buffer("A", 0xff111111u32, 7)
val opaque_payload = text_blit_buffer("A", 0xff111111u32, 0xff222222u32, 7)
var transparent_differing_count = 0
var transparent_fg_count = 0
var transparent_idx = 0
while transparent_idx < transparent_payload.pixels.len():
    if transparent_payload.pixels[transparent_idx] != opaque_payload.pixels[transparent_idx]:
        transparent_differing_count = transparent_differing_count + 1
    if transparent_payload.pixels[transparent_idx] == 0xff111111u32:
        transparent_fg_count = transparent_fg_count + 1
    transparent_idx = transparent_idx + 1

expect(transparent_payload.is_empty()).to_equal(false)
expect(transparent_payload.width).to_equal(opaque_payload.width)
expect(transparent_payload.height).to_equal(opaque_payload.height)
expect(transparent_differing_count > 0).to_equal(true)
expect(transparent_fg_count > 0).to_equal(true)

var cache = TextBlitCache.new()
val repeated_first = cache.transparent_blit_buffer("Repeat", 0xff111111u32, 14)
val repeated_scans_after_miss = cache.lookup_scan_count
val repeated_second = cache.transparent_blit_buffer("Repeat", 0xff111111u32, 14)
expect(repeated_first.is_empty()).to_equal(false)
expect(repeated_second.width).to_equal(repeated_first.width)
expect(repeated_second.height).to_equal(repeated_first.height)
expect(cache.cache_misses).to_equal(1)
expect(cache.cache_hits).to_equal(1)
expect(cache.lookup_scan_count).to_equal(repeated_scans_after_miss)
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
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

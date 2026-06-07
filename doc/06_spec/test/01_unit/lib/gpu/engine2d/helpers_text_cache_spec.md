# Helpers Text Cache Specification

> 1. var cache = TextBlitCache new

<!-- sdn-diagram:id=helpers_text_cache_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=helpers_text_cache_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

helpers_text_cache_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=helpers_text_cache_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Helpers Text Cache Specification

## Scenarios

### Engine2D text blit cache

#### keeps repeated Draw IR labels on the hot cache path without rescanning entries

1. var cache = TextBlitCache new
   - Expected: first.is_empty() is false
   - Expected: second.width equals `first.width`
   - Expected: second.height equals `first.height`
   - Expected: cache.cache_misses equals `1`
   - Expected: cache.cache_hits equals `1`
   - Expected: cache.lookup_scan_count equals `scans_after_miss`
   - Expected: third.is_empty() is false
   - Expected: cache.lookup_scan_count > scans_after_miss is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var cache = TextBlitCache.new()
val first = cache.transparent_blit_buffer("Repeat", 0xff111111u32, 14)
val scans_after_miss = cache.lookup_scan_count
val second = cache.transparent_blit_buffer("Repeat", 0xff111111u32, 14)

expect(first.is_empty()).to_equal(false)
expect(second.width).to_equal(first.width)
expect(second.height).to_equal(first.height)
expect(cache.cache_misses).to_equal(1)
expect(cache.cache_hits).to_equal(1)
expect(cache.lookup_scan_count).to_equal(scans_after_miss)

val third = cache.transparent_blit_buffer("Other", 0xff111111u32, 14)
expect(third.is_empty()).to_equal(false)
expect(cache.lookup_scan_count > scans_after_miss).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gpu/engine2d/helpers_text_cache_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Engine2D text blit cache

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

# Smf Cache Offset Specification

> <details>

<!-- sdn-diagram:id=smf_cache_offset_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=smf_cache_offset_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

smf_cache_offset_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=smf_cache_offset_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Smf Cache Offset Specification

## Scenarios

### Smf Cache Offset

#### stores cache statistics values

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val stats = CacheStats(
    total_files: 5,
    total_memory: 1024,
    cache_hits: 10,
    cache_misses: 3
)

expect(stats.total_files).to_equal(5)
expect(stats.total_memory).to_equal(1024)
expect(stats.cache_hits).to_equal(10)
expect(stats.cache_misses).to_equal(3)
```

</details>

#### creates an empty cache by default

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cache = SmfCache.new()
expect(cache.cached_count()).to_equal(0)
expect(cache.is_cached("missing.smf")).to_equal(false)
expect(cache.get_stats().total_files).to_equal(0)
```

</details>

#### decodes little-endian u32 values

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(bytes_to_u32([1, 0, 0, 0])).to_equal(1)
expect(bytes_to_u32([0, 1, 0, 0])).to_equal(256)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/loader/smf_cache_offset_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Smf Cache Offset

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

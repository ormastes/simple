# Learned Index Specification

> <details>

<!-- sdn-diagram:id=learned_index_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=learned_index_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

learned_index_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=learned_index_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Learned Index Specification

## Scenarios

### DB learned segment index

#### requires explicit opt-in and falls back to exact full scan when disabled

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val idx = learned_segment_build([10, 20, 30], [1, 2, 3], false)
val probe = learned_segment_probe(idx, 20)
val hits = learned_segment_lookup_exact(idx, 20)

expect(learned_segment_enabled(idx)).to_equal(false)
expect(probe.fallback).to_equal(true)
expect(learned_segment_window_size(probe)).to_equal(3)
expect(hits.len()).to_equal(1)
expect(hits[0]).to_equal(2)
```

</details>

#### uses a bounded learned window for sorted static segments

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val idx = learned_segment_build([0, 10, 20, 30, 40, 50, 60, 70], [100, 101, 102, 103, 104, 105, 106, 107], true)
val probe = learned_segment_probe(idx, 40)
val hits = learned_segment_lookup_exact(idx, 40)

expect(learned_segment_enabled(idx)).to_equal(true)
expect(probe.used_model).to_equal(true)
expect(probe.fallback).to_equal(false)
expect(learned_segment_window_size(probe)).to_be_less_than(8)
expect(hits.len()).to_equal(1)
expect(hits[0]).to_equal(104)
```

</details>

#### disables unsafe unsorted segments and preserves exact results

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val idx = learned_segment_build([10, 40, 30, 50], [1, 4, 3, 5], true)
val probe = learned_segment_probe(idx, 30)
val hits = learned_segment_lookup_exact(idx, 30)

expect(learned_segment_enabled(idx)).to_equal(false)
expect(learned_segment_unsafe_fallbacks(idx)).to_equal(1)
expect(probe.fallback).to_equal(true)
expect(hits.len()).to_equal(1)
expect(hits[0]).to_equal(3)
```

</details>

#### returns no rows for out-of-range probes without scanning

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val idx = learned_segment_build([100, 200, 300], [10, 20, 30], true)
val probe = learned_segment_probe(idx, 50)
val hits = learned_segment_lookup_exact(idx, 50)

expect(probe.used_model).to_equal(true)
expect(probe.fallback).to_equal(false)
expect(learned_segment_window_size(probe)).to_equal(0)
expect(hits.len()).to_equal(0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/db/learned_index_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- DB learned segment index

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

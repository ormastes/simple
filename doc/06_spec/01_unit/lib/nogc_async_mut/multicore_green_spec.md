# Multicore Green Specification

> <details>

<!-- sdn-diagram:id=multicore_green_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=multicore_green_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

multicore_green_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=multicore_green_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Multicore Green Specification

## Scenarios

### Multicore green facade

#### joins multiple value tasks

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val h0 = multicore_green_spawn(\: multicore_green_lcg(0))
val h1 = multicore_green_spawn(\: multicore_green_lcg(1))
val h2 = multicore_green_spawn(\: multicore_green_lcg(2))
val h3 = multicore_green_spawn(\: multicore_green_lcg(3))

expect(h0.ran_inline_fallback()).to_equal(true)
expect(h0.used_runtime_pool()).to_equal(false)
val got = h0.join() + h1.join() + h2.join() + h3.join()
val expected = multicore_green_lcg(0) + multicore_green_lcg(1) + multicore_green_lcg(2) + multicore_green_lcg(3)
expect(got).to_equal(expected)
```

</details>

#### exposes sliced inline fallback evidence in interpreter mode

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val handle = multicore_green_spawn_sliced(0, multicore_green_slice_once)
expect(handle.ran_inline_fallback()).to_equal(true)
expect(handle.used_runtime_pool()).to_equal(false)
expect(handle.join()).to_equal(19)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_async_mut/multicore_green_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Multicore green facade

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

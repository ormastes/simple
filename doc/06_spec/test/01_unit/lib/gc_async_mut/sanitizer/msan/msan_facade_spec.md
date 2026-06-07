# Msan Facade Specification

> 1. msan reset

<!-- sdn-diagram:id=msan_facade_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=msan_facade_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

msan_facade_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=msan_facade_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Msan Facade Specification

## Scenarios

### gc_async_mut sanitizer msan facade

#### re-exports memory sanitizer state checks and records

1. msan reset
   - Expected: msan_is_enabled() is false
   - Expected: msan_check_init("buffer") is true
2. msan enable
   - Expected: msan_is_enabled() is true
3. msan alloc uninit
   - Expected: msan_check_init("buffer") is false
4. msan init
   - Expected: msan_check_init("buffer") is true
5. msan free region
   - Expected: msan_check_not_freed("buffer") is false
   - Expected: msan_error_count() equals `2`
   - Expected: msan_get_events()[0].kind equals `msan`
   - Expected: region.initialized is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
msan_reset()
expect(msan_is_enabled()).to_equal(false)
expect(msan_check_init("buffer")).to_equal(true)

msan_enable()
expect(msan_is_enabled()).to_equal(true)
msan_alloc_uninit("buffer", 64)
expect(msan_check_init("buffer")).to_equal(false)
msan_init("buffer")
expect(msan_check_init("buffer")).to_equal(true)
msan_free_region("buffer")
expect(msan_check_not_freed("buffer")).to_equal(false)
expect(msan_error_count()).to_equal(2)
expect(msan_get_events()[0].kind).to_equal("msan")

val region = mem_region("buffer", 64)
expect(region.initialized).to_equal(false)
```

</details>

#### re-exports overlap checks

1. msan reset
2. msan enable
3. msan alloc init
   - Expected: msan_check_overlap("buffer", 0, "buffer", 8, 16) is false
   - Expected: msan_check_overlap("left", 0, "right", 8, 16) is true
   - Expected: msan_error_count() equals `1`
   - Expected: msan_get_events()[0].kind equals `msan`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
msan_reset()
msan_enable()
msan_alloc_init("buffer", 64)
expect(msan_check_overlap("buffer", 0, "buffer", 8, 16)).to_equal(false)
expect(msan_check_overlap("left", 0, "right", 8, 16)).to_equal(true)
expect(msan_error_count()).to_equal(1)
expect(msan_get_events()[0].kind).to_equal("msan")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gc_async_mut/sanitizer/msan/msan_facade_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- gc_async_mut sanitizer msan facade

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

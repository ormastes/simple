# Asan Facade Specification

> 1. asan reset

<!-- sdn-diagram:id=asan_facade_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=asan_facade_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

asan_facade_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=asan_facade_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Asan Facade Specification

## Scenarios

### nogc_async_mut sanitizer asan facade

#### re-exports address sanitizer allocation and access checks

1. asan reset
   - Expected: asan_is_enabled() is false
   - Expected: asan_check_access(1) is true
2. asan enable
   - Expected: asan_is_enabled() is true
3. asan on alloc
   - Expected: asan_check_access(1) is true
   - Expected: asan_check_bounds(1, 8, 4) is true
   - Expected: asan_check_bounds(1, 15, 4) is false
4. asan on free
   - Expected: asan_check_access(1) is false
5. asan on free
   - Expected: asan_error_count() equals `3`
   - Expected: asan_get_events()[0].kind equals `asan`
   - Expected: record.freed is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
asan_reset()
expect(asan_is_enabled()).to_equal(false)
expect(asan_check_access(1)).to_equal(true)

asan_enable()
expect(asan_is_enabled()).to_equal(true)
asan_on_alloc(1, 16, "buffer")
expect(asan_check_access(1)).to_equal(true)
expect(asan_check_bounds(1, 8, 4)).to_equal(true)
expect(asan_check_bounds(1, 15, 4)).to_equal(false)
asan_on_free(1)
expect(asan_check_access(1)).to_equal(false)
asan_on_free(1)
expect(asan_error_count()).to_equal(3)
expect(asan_get_events()[0].kind).to_equal("asan")

val record = asan_alloc_record(1, 16, "buffer")
expect(record.freed).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_async_mut/sanitizer/asan/asan_facade_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- nogc_async_mut sanitizer asan facade

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

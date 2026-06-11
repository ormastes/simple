# Lsan Facade Specification

> 1. lsan reset

<!-- sdn-diagram:id=lsan_facade_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=lsan_facade_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

lsan_facade_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=lsan_facade_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Lsan Facade Specification

## Scenarios

### gc_async_mut sanitizer lsan facade

#### re-exports leak sanitizer disabled-state checks and records

1. lsan reset
   - Expected: lsan_is_enabled() is false
   - Expected: lsan_check_since("missing") equals `0`
   - Expected: lsan_bytes_since("missing") equals `0`
   - Expected: lsan_error_count() equals `0`
   - Expected: checkpoint.name equals `before`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
lsan_reset()
expect(lsan_is_enabled()).to_equal(false)
expect(lsan_check_since("missing")).to_equal(0)
expect(lsan_bytes_since("missing")).to_equal(0)
expect(lsan_error_count()).to_equal(0)

val checkpoint = leak_checkpoint("before", 7)
expect(checkpoint.name).to_equal("before")
```

</details>

#### re-exports suppression tags

1. lsan reset
   - Expected: lsan_is_suppressed("fixture") is false
2. lsan suppress tag
   - Expected: lsan_is_suppressed("fixture") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
lsan_reset()
expect(lsan_is_suppressed("fixture")).to_equal(false)
lsan_suppress_tag("fixture")
expect(lsan_is_suppressed("fixture")).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gc_async_mut/sanitizer/lsan/lsan_facade_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- gc_async_mut sanitizer lsan facade

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

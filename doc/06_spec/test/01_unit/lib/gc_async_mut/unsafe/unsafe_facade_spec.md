# Unsafe Facade Specification

> <details>

<!-- sdn-diagram:id=unsafe_facade_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=unsafe_facade_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

unsafe_facade_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=unsafe_facade_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Unsafe Facade Specification

## Scenarios

### gc_async_mut unsafe facades

#### re-exports layout and maybe-uninit helpers

<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val layout = layout_info_new("DeviceRegs", ["C", "packed"], ["status"])
expect(layout_info_has_repr(layout, "C")).to_equal(true)
expect(layout_info_has_repr(layout, "transparent")).to_equal(false)
expect(layout_info_field_is_volatile(layout, "status")).to_equal(true)
expect(layout_info_repr_attrs(layout).len()).to_equal(2)
expect(layout_info_volatile_fields(layout)[0]).to_equal("status")

val empty_text = new_uninit<text>()
expect(mu_is_initialized(empty_text)).to_equal(false)
val filled_text = mu_write_text(empty_text, "ready")
expect(mu_is_initialized(filled_text)).to_equal(true)
expect(mu_assume_init_text(filled_text)).to_equal("ready")

val empty_bool = new_uninit<bool>()
val filled_bool = mu_write_bool(empty_bool, true)
expect(mu_assume_init_bool(filled_bool)).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gc_async_mut/unsafe/unsafe_facade_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- gc_async_mut unsafe facades

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

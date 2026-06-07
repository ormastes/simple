# Layout Scanner Specification

> 1. layout scanner reset

<!-- sdn-diagram:id=layout_scanner_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=layout_scanner_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

layout_scanner_spec -> app
layout_scanner_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=layout_scanner_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Layout Scanner Specification

## Scenarios

### Layout Scanner

#### captures repr annotations and struct entries

1. layout scanner reset
2. "# @repr
   - Expected: info == nil is false
   - Expected: layout_info_has_repr(info, "C") is true
   - Expected: layout_info_has_repr(info, "packed") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
layout_scanner_reset()
scan_layout_annotations(
    "# @repr(C, packed)\nstruct Dma:\n    ctrl: u32\n"
)

val info = get_layout_for_struct("Dma")

expect(info == nil).to_equal(false)
expect(layout_info_has_repr(info, "C")).to_equal(true)
expect(layout_info_has_repr(info, "packed")).to_equal(true)
```

</details>

#### tracks volatile fields without leaking state

1. layout scanner reset
   - Expected: info == nil is false
   - Expected: layout_info_field_is_volatile(info, "status") is true
   - Expected: layout_info_field_is_volatile(info, "addr") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
layout_scanner_reset()
scan_layout_annotations(
    "struct Regs:\n    # @volatile\n    status: u32\n    addr: u64\n"
)

val info = get_layout_for_struct("Regs")

expect(info == nil).to_equal(false)
expect(layout_info_field_is_volatile(info, "status")).to_equal(true)
expect(layout_info_field_is_volatile(info, "addr")).to_equal(false)
```

</details>

#### keeps multiple structs isolated and returns nil for missing entries

1. layout scanner reset
2. "struct A:\n    x: i64\n\n# @repr
   - Expected: info_a == nil is false
   - Expected: info_b == nil is false
   - Expected: layout_info_has_repr(info_a, "C") is false
   - Expected: layout_info_has_repr(info_b, "C") is true
   - Expected: missing == nil is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
layout_scanner_reset()
scan_layout_annotations(
    "struct A:\n    x: i64\n\n# @repr(C)\nstruct B:\n    y: u32\n"
)

val info_a = get_layout_for_struct("A")
val info_b = get_layout_for_struct("B")
val missing = get_layout_for_struct("Missing")

expect(info_a == nil).to_equal(false)
expect(info_b == nil).to_equal(false)
expect(layout_info_has_repr(info_a, "C")).to_equal(false)
expect(layout_info_has_repr(info_b, "C")).to_equal(true)
expect(missing == nil).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/backend/layout_scanner_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Layout Scanner

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

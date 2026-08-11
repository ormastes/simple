# Pixel Region Ignore Specification

> Tests covering GUI image compare — ignore sections.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Pixel Region Ignore Specification

## Scenarios

### GUI image compare — ignore sections

#### names a rectangular region of the captured image

- Select a 120x40 region at offset (16, 8) — a status bar, say
- Confirm the rectangle round-trips exactly through the selector
   - Expected: pixel_region_x(region) equals `16`
   - Expected: pixel_region_y(region) equals `8`
   - Expected: pixel_region_width(region) equals `120`
   - Expected: pixel_region_height(region) equals `40`
- Confirm it is carried as a pixel_region, not silently downgraded
   - Expected: selector_kind_name(region.kind) equals `pixel_region`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Select a 120x40 region at offset (16, 8) — a status bar, say")
val region = selector_pixel_region(16, 8, 120, 40)

step("Confirm the rectangle round-trips exactly through the selector")
expect(pixel_region_x(region)).to_equal(16)
expect(pixel_region_y(region)).to_equal(8)
expect(pixel_region_width(region)).to_equal(120)
expect(pixel_region_height(region)).to_equal(40)

step("Confirm it is carried as a pixel_region, not silently downgraded")
expect(selector_kind_name(region.kind)).to_equal("pixel_region")
```

</details>

#### keeps a large region's extent intact rather than truncating it

- Select a region spanning a 4K framebuffer
- Confirm both extents survive the packing
   - Expected: pixel_region_width(region) equals `3840`
   - Expected: pixel_region_height(region) equals `2160`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# The rect is packed two-per-field; a naive 32-bit pack corrupts a 4K capture.
step("Select a region spanning a 4K framebuffer")
val region = selector_pixel_region(0, 0, 3840, 2160)

step("Confirm both extents survive the packing")
expect(pixel_region_width(region)).to_equal(3840)
expect(pixel_region_height(region)).to_equal(2160)
```

</details>

#### records why a region is masked instead of dropping it silently

- Mask the clock region, stating the reason it cannot be compared
- Confirm the reason travelled with the check
- Confirm the masked rectangle is still fully described
   - Expected: pixel_region_width(clock) equals `100`
   - Expected: pixel_region_height(clock) equals `20`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Mask the clock region, stating the reason it cannot be compared")
val clock = selector_pixel_region(900, 4, 100, 20)
val ignored = check_ignore("clock", "wall-clock text differs on every capture")

step("Confirm the reason travelled with the check")
expect(ignored.reason.len()).to_be_greater_than(0)
expect(ignored.reason).to_contain("wall-clock")

step("Confirm the masked rectangle is still fully described")
expect(pixel_region_width(clock)).to_equal(100)
expect(pixel_region_height(clock)).to_equal(20)
```

</details>

#### pairs a masked region with a positive check over the rest of the image

- Build an oracle that masks the clock but still checks the title bar
- Confirm both checks are carried — the mask did not replace the oracle
   - Expected: spec.checks.len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# An oracle needs at least one positive claim; the comparator rejects an
# all-ignore spec ("oracle has no positive production check"). This example
# documents the shape a real GUI comparison must take.
step("Build an oracle that masks the clock but still checks the title bar")
val title = selector_pixel_region(0, 0, 400, 24)
val checks = [
    check_exact_selector(title, "title-bar-digest"),
    check_ignore("clock", "wall-clock text differs on every capture")
]
val spec = oracle_spec("gui.image.v1", checks)

step("Confirm both checks are carried — the mask did not replace the oracle")
expect(spec.checks.len()).to_equal(2)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/spec/evidence/pixel_region_ignore_spec.spl` |
| Updated | 2026-08-11 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering GUI image compare — ignore sections.
- GUI image compare — ignore sections

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

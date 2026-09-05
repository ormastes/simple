# view_layout_edge_spec

> Office sheets freeze-panes and print-area edge-case spec.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 22 | 22 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# view_layout_edge_spec

Office sheets freeze-panes and print-area edge-case spec.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/office/sheets/view_layout_edge_spec.spl` |
| Updated | 2026-08-18 |
| Generator | `simple spipe-docgen` (Simple) |

Office sheets freeze-panes and print-area edge-case spec.

Zero and negative freeze counts, freezes that would leave nothing to
scroll, malformed and out-of-bounds print ranges, inverted ranges, and
clearing when nothing is set.

## Scenarios

### freeze panes: rejected input
_Invalid freeze counts are rejected and leave the layout unchanged._

#### rejects a negative row count

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sheet = Sheet.new("S1")
val result = freeze_panes(sheet, default_view_layout(), 0 - 1, 0)
expect(result.ok).to_equal(false)
expect(result.reason).to_equal("negative freeze count")
expect(frozen_extent(result.layout)).to_equal("R0C0")
```

</details>

#### rejects a negative column count

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sheet = Sheet.new("S1")
val result = freeze_panes(sheet, default_view_layout(), 0, 0 - 5)
expect(result.ok).to_equal(false)
expect(has_frozen_panes(result.layout)).to_equal(false)
```

</details>

#### rejects freezing every row, leaving nothing to scroll

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sheet = Sheet.new("S1")
val result = freeze_panes(sheet, default_view_layout(), sheet.row_count, 0)
expect(result.ok).to_equal(false)
```

</details>

#### rejects freezing every column, leaving nothing to scroll

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sheet = Sheet.new("S1")
val result = freeze_panes(sheet, default_view_layout(), 0, sheet.col_count)
expect(result.ok).to_equal(false)
```

</details>

#### rejects a row count beyond the sheet bounds

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sheet = Sheet.new("S1")
val result = freeze_panes(sheet, default_view_layout(), sheet.row_count + 10, 0)
expect(result.ok).to_equal(false)
```

</details>

#### preserves an existing freeze when a new one is rejected

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sheet = Sheet.new("S1")
val good = freeze_panes(sheet, default_view_layout(), 2, 2).layout
val bad = freeze_panes(sheet, good, 0 - 1, 0)
expect(bad.ok).to_equal(false)
expect(frozen_extent(bad.layout)).to_equal("R2C2")
```

</details>

### freeze panes: boundary and no-op cases
_Zero counts, the last legal count, and repeated unfreezing._

#### accepts a zero freeze as an explicit unfreeze

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sheet = Sheet.new("S1")
val frozen = freeze_panes(sheet, default_view_layout(), 3, 3).layout
val result = freeze_panes(sheet, frozen, 0, 0)
expect(result.ok).to_equal(true)
expect(has_frozen_panes(result.layout)).to_equal(false)
```

</details>

#### accepts the largest count that still leaves one scrollable line

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sheet = Sheet.new("S1")
val result = freeze_panes(sheet, default_view_layout(), sheet.row_count - 1, sheet.col_count - 1)
expect(result.ok).to_equal(true)
```

</details>

#### unfreezing when nothing is frozen is a no-op

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cleared = unfreeze_panes(default_view_layout())
expect(has_frozen_panes(cleared)).to_equal(false)
expect(frozen_extent(cleared)).to_equal("R0C0")
```

</details>

#### treats an unparseable reference as not frozen

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sheet = Sheet.new("S1")
val layout = freeze_panes(sheet, default_view_layout(), 5, 5).layout
expect(is_frozen_ref(layout, "not-a-ref")).to_equal(false)
expect(is_frozen_ref(layout, "")).to_equal(false)
```

</details>

### print area: rejected input
_Malformed and out-of-bounds ranges are rejected._

#### rejects a single cell reference with no colon

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sheet = Sheet.new("S1")
val result = set_print_area(sheet, default_view_layout(), "A1")
expect(result.ok).to_equal(false)
expect(has_print_area(result.layout)).to_equal(false)
```

</details>

#### rejects an empty range string

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sheet = Sheet.new("S1")
expect(set_print_area(sheet, default_view_layout(), "").ok).to_equal(false)
```

</details>

#### rejects a garbage range

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sheet = Sheet.new("S1")
expect(set_print_area(sheet, default_view_layout(), "1A:!!").ok).to_equal(false)
```

</details>

#### rejects a range past the sheet column bound

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sheet = Sheet.new("S1")
val result = set_print_area(sheet, default_view_layout(), "A1:ZZ5")
expect(result.ok).to_equal(false)
```

</details>

#### rejects a range past the sheet row bound

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sheet = Sheet.new("S1")
val result = set_print_area(sheet, default_view_layout(), "A1:B5000")
expect(result.ok).to_equal(false)
```

</details>

#### preserves an existing print area when a new one is rejected

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sheet = Sheet.new("S1")
val good = set_print_area(sheet, default_view_layout(), "A1:C3").layout
val bad = set_print_area(sheet, good, "A1:B5000")
expect(bad.ok).to_equal(false)
expect(bad.layout.print_area).to_equal("A1:C3")
```

</details>

### print area: normalization and no-ops
_Inverted ranges normalize; clearing an unset area is safe._

#### normalizes a fully inverted range

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sheet = Sheet.new("S1")
val result = set_print_area(sheet, default_view_layout(), "C3:A1")
expect(result.ok).to_equal(true)
expect(result.layout.print_area).to_equal("A1:C3")
```

</details>

#### normalizes a corner-swapped range per axis

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sheet = Sheet.new("S1")
val result = set_print_area(sheet, default_view_layout(), "C1:A3")
expect(result.ok).to_equal(true)
expect(result.layout.print_area).to_equal("A1:C3")
```

</details>

#### accepts a degenerate single-cell range

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sheet = Sheet.new("S1")
val result = set_print_area(sheet, default_view_layout(), "B2:B2")
expect(result.ok).to_equal(true)
expect(result.layout.print_area).to_equal("B2:B2")
expect(print_area_refs(result.layout).len()).to_equal(1)
```

</details>

#### accepts a lowercase range and stores it uppercased

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sheet = Sheet.new("S1")
val result = set_print_area(sheet, default_view_layout(), "a1:b2")
expect(result.ok).to_equal(true)
expect(result.layout.print_area).to_equal("A1:B2")
```

</details>

#### clearing when nothing is set is a no-op

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cleared = clear_print_area(default_view_layout())
expect(has_print_area(cleared)).to_equal(false)
expect(print_area_refs(cleared).len()).to_equal(0)
```

</details>

#### clearing twice stays cleared

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sheet = Sheet.new("S1")
val layout = set_print_area(sheet, default_view_layout(), "A1:C3").layout
expect(has_print_area(clear_print_area(clear_print_area(layout)))).to_equal(false)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 22 |
| Active scenarios | 22 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

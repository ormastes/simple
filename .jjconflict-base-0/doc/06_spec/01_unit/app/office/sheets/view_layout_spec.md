# view_layout_spec

> Office sheets freeze-panes and print-area core behaviour spec.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 13 | 13 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# view_layout_spec

Office sheets freeze-panes and print-area core behaviour spec.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/office/sheets/view_layout_spec.spl` |
| Updated | 2026-08-18 |
| Generator | `simple spipe-docgen` (Simple) |

Office sheets freeze-panes and print-area core behaviour spec.

Covers freezing rows/columns, unfreezing, querying the frozen extent, and
setting/clearing/querying a print area as an A1 range.

## Scenarios

### freeze panes: core
_Freeze leading rows/columns and query the frozen extent._

#### starts with nothing frozen

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val layout = default_view_layout()
expect(has_frozen_panes(layout)).to_equal(false)
expect(frozen_extent(layout)).to_equal("R0C0")
```

</details>

#### freezes rows only

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sheet = Sheet.new("S1")
val result = freeze_panes(sheet, default_view_layout(), 2, 0)
expect(result.ok).to_equal(true)
expect(frozen_extent(result.layout)).to_equal("R2C0")
```

</details>

#### freezes columns only

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sheet = Sheet.new("S1")
val result = freeze_panes(sheet, default_view_layout(), 0, 3)
expect(result.ok).to_equal(true)
expect(frozen_extent(result.layout)).to_equal("R0C3")
```

</details>

#### freezes rows and columns together

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sheet = Sheet.new("S1")
val result = freeze_panes(sheet, default_view_layout(), 1, 1)
expect(result.ok).to_equal(true)
expect(has_frozen_panes(result.layout)).to_equal(true)
expect(frozen_extent(result.layout)).to_equal("R1C1")
```

</details>

#### unfreezes back to nothing frozen

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sheet = Sheet.new("S1")
val frozen = freeze_panes(sheet, default_view_layout(), 2, 2)
val cleared = unfreeze_panes(frozen.layout)
expect(has_frozen_panes(cleared)).to_equal(false)
expect(frozen_extent(cleared)).to_equal("R0C0")
```

</details>

### freeze panes: per-cell membership
_is_frozen_ref reports whether a cell stays pinned while scrolling._

#### reports a cell in a frozen row as frozen

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sheet = Sheet.new("S1")
val layout = freeze_panes(sheet, default_view_layout(), 2, 0).layout
expect(is_frozen_ref(layout, "D1")).to_equal(true)
expect(is_frozen_ref(layout, "D2")).to_equal(true)
expect(is_frozen_ref(layout, "D3")).to_equal(false)
```

</details>

#### reports a cell in a frozen column as frozen

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sheet = Sheet.new("S1")
val layout = freeze_panes(sheet, default_view_layout(), 0, 2).layout
expect(is_frozen_ref(layout, "A9")).to_equal(true)
expect(is_frozen_ref(layout, "B9")).to_equal(true)
expect(is_frozen_ref(layout, "C9")).to_equal(false)
```

</details>

### print area: core
_Set, query, expand, and clear a print area._

#### starts with no print area

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val layout = default_view_layout()
expect(has_print_area(layout)).to_equal(false)
expect(layout.print_area).to_equal("")
```

</details>

#### sets a print area from an A1 range

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sheet = Sheet.new("S1")
val result = set_print_area(sheet, default_view_layout(), "A1:C10")
expect(result.ok).to_equal(true)
expect(result.layout.print_area).to_equal("A1:C10")
expect(has_print_area(result.layout)).to_equal(true)
```

</details>

#### expands the print area into cell references

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sheet = Sheet.new("S1")
val layout = set_print_area(sheet, default_view_layout(), "A1:B2").layout
val refs = print_area_refs(layout)
expect(refs.len()).to_equal(4)
expect(refs[0]).to_equal("A1")
```

</details>

#### clears a set print area

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sheet = Sheet.new("S1")
val layout = set_print_area(sheet, default_view_layout(), "A1:C3").layout
val cleared = clear_print_area(layout)
expect(has_print_area(cleared)).to_equal(false)
expect(print_area_refs(cleared).len()).to_equal(0)
```

</details>

### view layout: axis independence
_Freeze state and print area are independent slots on one layout._

#### keeps the print area across a freeze and unfreeze

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sheet = Sheet.new("S1")
val with_area = set_print_area(sheet, default_view_layout(), "A1:C3").layout
val frozen = freeze_panes(sheet, with_area, 1, 1).layout
expect(frozen.print_area).to_equal("A1:C3")
expect(unfreeze_panes(frozen).print_area).to_equal("A1:C3")
```

</details>

#### keeps the frozen extent across clearing the print area

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sheet = Sheet.new("S1")
val frozen = freeze_panes(sheet, default_view_layout(), 2, 1).layout
val with_area = set_print_area(sheet, frozen, "A1:C3").layout
expect(frozen_extent(clear_print_area(with_area))).to_equal("R2C1")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 13 |
| Active scenarios | 13 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

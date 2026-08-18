# sheet_visibility_spec

> Sheet row-visibility spec.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 12 | 12 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# sheet_visibility_spec

Sheet row-visibility spec.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/office/sheets/sheet_visibility_spec.spl` |
| Updated | 2026-08-18 |
| Generator | `simple spipe-docgen` (Simple) |

Sheet row-visibility spec.

Row visibility is the foundation Excel uses for hidden rows, filtered
views, and SUBTOTAL's 101-111 semantics. State lives on Sheet as
`hidden_rows: [i64]` — a plain list of 1-based (Excel-style) row indices,
NOT a Dict-in-struct (see the quirk ledger: Dict-in-struct corrupts under
copy-return). Membership is a linear scan; hide_row dedupes on insert so a
row is never hidden twice, and out-of-range rows (< 1 or beyond
row_count) are silently ignored.

## Scenarios

### Sheet row visibility: hide/unhide
_Basic hide -> is_row_hidden true, unhide -> false round trip._

#### hide_row makes is_row_hidden true

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sheet = Sheet.new("S1")
assert_false(sheet.is_row_hidden(2))
sheet.hide_row(2)
assert_true(sheet.is_row_hidden(2))
```

</details>

#### unhide_row makes is_row_hidden false again

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sheet = Sheet.new("S1")
sheet.hide_row(3)
assert_true(sheet.is_row_hidden(3))
sheet.unhide_row(3)
assert_false(sheet.is_row_hidden(3))
```

</details>

#### hiding one row does not affect a different row

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sheet = Sheet.new("S1")
sheet.hide_row(4)
assert_true(sheet.is_row_hidden(4))
assert_false(sheet.is_row_hidden(5))
```

</details>

#### unhide_row on a never-hidden row is a no-op

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sheet = Sheet.new("S1")
sheet.unhide_row(7)
assert_false(sheet.is_row_hidden(7))
```

</details>

### Sheet row visibility: hide_rows range
_hide_rows(from, to) hides every row in the inclusive range._

#### hides every row in the range, inclusive

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sheet = Sheet.new("S1")
sheet.hide_rows(2, 4)
assert_true(sheet.is_row_hidden(2))
assert_true(sheet.is_row_hidden(3))
assert_true(sheet.is_row_hidden(4))
```

</details>

#### does not hide rows outside the range

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sheet = Sheet.new("S1")
sheet.hide_rows(2, 4)
assert_false(sheet.is_row_hidden(1))
assert_false(sheet.is_row_hidden(5))
```

</details>

#### handles a reversed (from > to) range the same as ascending

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sheet = Sheet.new("S1")
sheet.hide_rows(6, 5)
assert_true(sheet.is_row_hidden(5))
assert_true(sheet.is_row_hidden(6))
```

</details>

### Sheet row visibility: idempotency
_Hiding an already-hidden row is a no-op, not a duplicate entry._

#### hiding the same row twice keeps it hidden (no crash, no dup effect)

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sheet = Sheet.new("S1")
sheet.hide_row(2)
sheet.hide_row(2)
assert_true(sheet.is_row_hidden(2))
sheet.unhide_row(2)
# A single unhide fully clears it even though hide_row was called
# twice -- proves hidden_rows never grew a duplicate entry.
assert_false(sheet.is_row_hidden(2))
```

</details>

### Sheet row visibility: out-of-range
_Out-of-range row indices are silently ignored, not errors/crashes._

#### hide_row(0) is a no-op (rows are 1-based)

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sheet = Sheet.new("S1")
sheet.hide_row(0)
assert_false(sheet.is_row_hidden(0))
```

</details>

#### hide_row of a negative row is a no-op

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sheet = Sheet.new("S1")
sheet.hide_row(-1)
assert_false(sheet.is_row_hidden(-1))
```

</details>

#### hide_row beyond row_count is a no-op

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sheet = Sheet.new("S1")
sheet.hide_row(sheet.row_count.to_i64() + 50)
assert_false(sheet.is_row_hidden(sheet.row_count.to_i64() + 50))
```

</details>

### Sheet row visibility: unhide_all_rows
_unhide_all_rows clears every hidden row (used by AutoFilter clear)._

#### clears multiple hidden rows at once

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sheet = Sheet.new("S1")
sheet.hide_rows(2, 5)
sheet.unhide_all_rows()
assert_false(sheet.is_row_hidden(2))
assert_false(sheet.is_row_hidden(3))
assert_false(sheet.is_row_hidden(4))
assert_false(sheet.is_row_hidden(5))
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 12 |
| Active scenarios | 12 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

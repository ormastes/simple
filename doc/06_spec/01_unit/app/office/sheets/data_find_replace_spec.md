# data_find_replace_spec

> Calc find & replace spec.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# data_find_replace_spec

Calc find & replace spec.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/office/sheets/data_find_replace_spec.spl` |
| Updated | 2026-08-18 |
| Generator | `simple spipe-docgen` (Simple) |

Calc find & replace spec.

sheet_find returns A1 refs (row-major) whose display text contains the needle,
case-insensitive unless match_case. sheet_replace substitutes in non-formula
cell values only, leaving formula cells untouched, and returns the sheet.

## Scenarios

### Calc sheet_find

#### finds case-insensitively in row-major order

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sh = _build()
val hits = sheet_find(sh, "apple", false)
expect(hits.len()).to_equal(2)
expect(hits[0]).to_equal("A1")
expect(hits[1]).to_equal("A2")
```

</details>

#### respects match_case when requested

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sh = _build()
val hits = sheet_find(sh, "apple", true)
expect(hits.len()).to_equal(1)
expect(hits[0]).to_equal("A2")
```

</details>

#### returns empty for a needle that is absent or empty

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sh = _build()
expect(sheet_find(sh, "zzz", false).len()).to_equal(0)
expect(sheet_find(sh, "", false).len()).to_equal(0)
```

</details>

### Calc sheet_replace

#### replaces case-insensitively and returns the mutated sheet

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sh = _build()
sh = sheet_replace(sh, "apple", "PEAR", false)
expect(cell_display_text(sh.get_cell("A1"))).to_equal("PEAR")
expect(cell_display_text(sh.get_cell("A2"))).to_equal("PEAR pie")
expect(cell_display_text(sh.get_cell("B1"))).to_equal("banana")
```

</details>

#### leaves formula cells untouched

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sh = _build()
sh.set_value("C1", "=5")
sh = sheet_replace(sh, "5", "X", false)
expect(cell_display_text(sh.get_cell("C1"))).to_contain("5")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

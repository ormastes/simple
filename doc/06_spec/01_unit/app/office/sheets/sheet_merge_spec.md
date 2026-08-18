# sheet_merge_spec

> Office sheets three-way merge spec.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 21 | 21 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# sheet_merge_spec

Office sheets three-way merge spec.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/office/sheets/sheet_merge_spec.spl` |
| Updated | 2026-08-18 |
| Generator | `simple spipe-docgen` (Simple) |

Office sheets three-way merge spec.

Hand-built fixtures for sheet_merge3 covering every merge rule: clean merges
in each direction, identical changes, conflicting changes (mine wins, all
three raw texts recorded), add-add conflicts, delete-vs-change conflicts,
formula-as-text merging, conflict_report formatting, merge_annotate markers,
empty-sheet and no-change edge cases.

## Scenarios

### sheet_merge3: clean merges

#### keeps unchanged value from base when all three sides agree

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var base = Sheet.new("s")
base.set_value("A1", "10")
var mine = Sheet.new("s")
mine.set_value("A1", "10")
var theirs = Sheet.new("s")
theirs.set_value("A1", "10")

val result = sheet_merge3(base, mine, theirs)
assert_equal(result.conflicts.len(), 0)
assert_equal(cell_display_text(result.merged.get_cell("A1")), "10")
```

</details>

#### takes mine's value when only mine changed

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var base = Sheet.new("s")
base.set_value("A1", "10")
var mine = Sheet.new("s")
mine.set_value("A1", "20")
var theirs = Sheet.new("s")
theirs.set_value("A1", "10")

val result = sheet_merge3(base, mine, theirs)
assert_equal(result.conflicts.len(), 0)
assert_equal(cell_display_text(result.merged.get_cell("A1")), "20")
```

</details>

#### takes theirs' value when only theirs changed

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var base = Sheet.new("s")
base.set_value("A1", "10")
var mine = Sheet.new("s")
mine.set_value("A1", "10")
var theirs = Sheet.new("s")
theirs.set_value("A1", "30")

val result = sheet_merge3(base, mine, theirs)
assert_equal(result.conflicts.len(), 0)
assert_equal(cell_display_text(result.merged.get_cell("A1")), "30")
```

</details>

### sheet_merge3: identical change

#### takes the shared value with no conflict when both sides change identically

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var base = Sheet.new("s")
base.set_value("A1", "10")
var mine = Sheet.new("s")
mine.set_value("A1", "99")
var theirs = Sheet.new("s")
theirs.set_value("A1", "99")

val result = sheet_merge3(base, mine, theirs)
assert_equal(result.conflicts.len(), 0)
assert_equal(cell_display_text(result.merged.get_cell("A1")), "99")
```

</details>

### sheet_merge3: conflicting change

#### keeps mine's value and records all three raw texts as a conflict

<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var base = Sheet.new("s")
base.set_value("A1", "10")
var mine = Sheet.new("s")
mine.set_value("A1", "20")
var theirs = Sheet.new("s")
theirs.set_value("A1", "30")

val result = sheet_merge3(base, mine, theirs)
assert_equal(result.conflicts.len(), 1)
assert_equal(cell_display_text(result.merged.get_cell("A1")), "20")
val c = result.conflicts[0]
assert_equal(c.ref, "A1")
assert_equal(c.base_text, "10")
assert_equal(c.mine_text, "20")
assert_equal(c.theirs_text, "30")
```

</details>

### sheet_merge3: add-add

#### takes the value with no conflict when both sides add identically

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var base = Sheet.new("s")
var mine = Sheet.new("s")
mine.set_value("Z9", "hello")
var theirs = Sheet.new("s")
theirs.set_value("Z9", "hello")

val result = sheet_merge3(base, mine, theirs)
assert_equal(result.conflicts.len(), 0)
assert_equal(cell_display_text(result.merged.get_cell("Z9")), "hello")
```

</details>

#### conflicts and keeps mine when both sides add different values

<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var base = Sheet.new("s")
var mine = Sheet.new("s")
mine.set_value("Z9", "mine-value")
var theirs = Sheet.new("s")
theirs.set_value("Z9", "theirs-value")

val result = sheet_merge3(base, mine, theirs)
assert_equal(result.conflicts.len(), 1)
assert_equal(cell_display_text(result.merged.get_cell("Z9")), "mine-value")
val c = result.conflicts[0]
assert_equal(c.ref, "Z9")
assert_equal(c.base_text, "<absent>")
assert_equal(c.mine_text, "mine-value")
assert_equal(c.theirs_text, "theirs-value")
```

</details>

#### takes mine's value with no conflict when only mine adds

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var base = Sheet.new("s")
var mine = Sheet.new("s")
mine.set_value("Q1", "only-mine")
var theirs = Sheet.new("s")

val result = sheet_merge3(base, mine, theirs)
assert_equal(result.conflicts.len(), 0)
assert_equal(cell_display_text(result.merged.get_cell("Q1")), "only-mine")
```

</details>

#### takes theirs' value with no conflict when only theirs adds

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var base = Sheet.new("s")
var mine = Sheet.new("s")
var theirs = Sheet.new("s")
theirs.set_value("Q1", "only-theirs")

val result = sheet_merge3(base, mine, theirs)
assert_equal(result.conflicts.len(), 0)
assert_equal(cell_display_text(result.merged.get_cell("Q1")), "only-theirs")
```

</details>

### sheet_merge3: delete vs unchanged

#### deletes the cell when mine deletes and theirs leaves it unchanged

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var base = Sheet.new("s")
base.set_value("A1", "keep-me")
var mine = Sheet.new("s")
# mine never set A1 -> stays absent (deleted)
var theirs = Sheet.new("s")
theirs.set_value("A1", "keep-me")

val result = sheet_merge3(base, mine, theirs)
assert_equal(result.conflicts.len(), 0)
assert_true(is_empty_cell(result.merged, "A1"))
```

</details>

#### deletes the cell when theirs deletes and mine leaves it unchanged

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var base = Sheet.new("s")
base.set_value("A1", "keep-me")
var mine = Sheet.new("s")
mine.set_value("A1", "keep-me")
var theirs = Sheet.new("s")
# theirs never set A1 -> stays absent (deleted)

val result = sheet_merge3(base, mine, theirs)
assert_equal(result.conflicts.len(), 0)
assert_true(is_empty_cell(result.merged, "A1"))
```

</details>

#### deletes the cell with no conflict when both sides delete it

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var base = Sheet.new("s")
base.set_value("A1", "gone-soon")
var mine = Sheet.new("s")
var theirs = Sheet.new("s")

val result = sheet_merge3(base, mine, theirs)
assert_equal(result.conflicts.len(), 0)
assert_true(is_empty_cell(result.merged, "A1"))
```

</details>

### sheet_merge3: delete vs change

#### keeps theirs' change and records a conflict when mine deleted it

<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var base = Sheet.new("s")
base.set_value("A1", "10")
var mine = Sheet.new("s")
# mine deletes A1 (never set) -> absent
var theirs = Sheet.new("s")
theirs.set_value("A1", "changed-by-theirs")

val result = sheet_merge3(base, mine, theirs)
assert_equal(result.conflicts.len(), 1)
assert_equal(cell_display_text(result.merged.get_cell("A1")), "changed-by-theirs")
val c = result.conflicts[0]
assert_equal(c.base_text, "10")
assert_equal(c.mine_text, "<absent>")
assert_equal(c.theirs_text, "changed-by-theirs")
```

</details>

#### keeps mine's change and records a conflict when theirs deleted it

<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var base = Sheet.new("s")
base.set_value("A1", "10")
var mine = Sheet.new("s")
mine.set_value("A1", "changed-by-mine")
var theirs = Sheet.new("s")
# theirs deletes A1 (never set) -> absent

val result = sheet_merge3(base, mine, theirs)
assert_equal(result.conflicts.len(), 1)
assert_equal(cell_display_text(result.merged.get_cell("A1")), "changed-by-mine")
val c = result.conflicts[0]
assert_equal(c.base_text, "10")
assert_equal(c.mine_text, "changed-by-mine")
assert_equal(c.theirs_text, "<absent>")
```

</details>

### sheet_merge3: formulas merge as text

#### treats identical formula source as unchanged even across three copies

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var base = Sheet.new("s")
base.set_value("A1", "=1+1")
var mine = Sheet.new("s")
mine.set_value("A1", "=1+1")
var theirs = Sheet.new("s")
theirs.set_value("A1", "=1+1")

val result = sheet_merge3(base, mine, theirs)
assert_equal(result.conflicts.len(), 0)
```

</details>

#### conflicts on differing formula source text

<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var base = Sheet.new("s")
base.set_value("A1", "=A2+A3")
var mine = Sheet.new("s")
mine.set_value("A1", "=A2+A4")
var theirs = Sheet.new("s")
theirs.set_value("A1", "=A2+A5")

val result = sheet_merge3(base, mine, theirs)
assert_equal(result.conflicts.len(), 1)
val c = result.conflicts[0]
assert_equal(c.base_text, "=A2+A3")
assert_equal(c.mine_text, "=A2+A4")
assert_equal(c.theirs_text, "=A2+A5")
```

</details>

### conflict_report

#### formats one exact line per conflict

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var base = Sheet.new("s")
base.set_value("A1", "10")
var mine = Sheet.new("s")
mine.set_value("A1", "20")
var theirs = Sheet.new("s")
theirs.set_value("A1", "30")

val result = sheet_merge3(base, mine, theirs)
val lines = conflict_report(result)
assert_equal(lines.len(), 1)
assert_equal(lines[0], "A1|base=10|mine=20|theirs=30")
```

</details>

### merge_annotate

#### marks a conflicted cell's text with the mine/theirs marker

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var base = Sheet.new("s")
base.set_value("A1", "10")
var mine = Sheet.new("s")
mine.set_value("A1", "20")
var theirs = Sheet.new("s")
theirs.set_value("A1", "30")

val result = sheet_merge3(base, mine, theirs)
val annotated = merge_annotate(result)
assert_equal(cell_display_text(annotated.get_cell("A1")), "<<20>>|<<30>>")
```

</details>

### sheet_merge3: edge cases

#### returns an empty merged sheet with zero conflicts for three empty sheets

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var base = Sheet.new("s")
var mine = Sheet.new("s")
var theirs = Sheet.new("s")

val result = sheet_merge3(base, mine, theirs)
assert_equal(result.conflicts.len(), 0)
assert_equal(result.merged.cell_count(), 0)
```

</details>

#### produces zero conflicts when nothing changed across several cells

<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var base = Sheet.new("s")
base.set_value("A1", "1")
base.set_value("A2", "2")
base.set_value("A3", "three")
var mine = Sheet.new("s")
mine.set_value("A1", "1")
mine.set_value("A2", "2")
mine.set_value("A3", "three")
var theirs = Sheet.new("s")
theirs.set_value("A1", "1")
theirs.set_value("A2", "2")
theirs.set_value("A3", "three")

val result = sheet_merge3(base, mine, theirs)
assert_equal(result.conflicts.len(), 0)
assert_equal(result.merged.cell_count(), 3)
```

</details>

### sheet_merge3: hidden rows

#### takes mine's hidden rows wholesale regardless of base/theirs

<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var base = Sheet.new("s")
base.hide_row(1)
var mine = Sheet.new("s")
mine.hide_row(2)
mine.hide_row(3)
var theirs = Sheet.new("s")
theirs.hide_row(9)

val result = sheet_merge3(base, mine, theirs)
assert_true(result.merged.is_row_hidden(2))
assert_true(result.merged.is_row_hidden(3))
assert_false(result.merged.is_row_hidden(1))
assert_false(result.merged.is_row_hidden(9))
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 21 |
| Active scenarios | 21 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

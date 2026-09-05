# pivot_gui_view_spec

> Pivot-table GUI view spec.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 15 | 15 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# pivot_gui_view_spec

Pivot-table GUI view spec.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/office/pivot_gui_view_spec.spl` |
| Updated | 2026-08-18 |
| Generator | `simple spipe-docgen` (Simple) |

Pivot-table GUI view spec.

pivot_gui_view(sheet, data_range, row_field_col, col_field_col, value_col,
agg_name, title) runs the existing pivot_build engine
(app.office.sheets.pivot) over `data_range` and renders the resulting grid
through the same table_widget machinery sheet_gui_view uses. The dump's
first line is "pivot|<agg>|<title>"; each following line is one pipe-joined
row of the engine's own result grid (its column-keys header row, each
data row, and its grand-total row -- totals row/col exactly as the engine
provides them). An unknown agg name or an empty/unparseable data range
fails closed with an "error|<reason>" line instead of crashing.

Ground truth (same dataset shape as sheets/pivot_spec.spl, hand-verified
there and rechecked here): Region/Product/Amount rows
  East,A,10
  East,B,20
  West,A,30
  West,B,40
  East,A,5
  West,B,15
2D pivot region x product SUM: East/A=15, East/B=20, West/A=30, West/B=55,
row totals East=35 West=85, col totals A=45 B=75, grand=120.

## Scenarios

### pivot_gui_view: header line
_The dump always starts with a pivot|<agg>|<title> header line._

#### the first line carries the agg name and title

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sheet = _pivot_gui_dataset()
val view = pivot_gui_view(sheet, "A1:C6", 0, 1, 2, "SUM", "Region x Product")
val lines = view.text_dump.split("\n")
expect(lines[0]).to_equal("pivot|SUM|Region x Product")
```

</details>

### pivot_gui_view: 2D SUM aggregates

#### the column-keys header row lists row-key label, col keys, and Grand Total

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sheet = _pivot_gui_dataset()
val view = pivot_gui_view(sheet, "A1:C6", 0, 1, 2, "SUM", "T")
val lines = view.text_dump.split("\n")
expect(lines[1]).to_equal("Row/Col|A|B|Grand Total")
```

</details>

#### the East row carries East/A=15, East/B=20, row total=35

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sheet = _pivot_gui_dataset()
val view = pivot_gui_view(sheet, "A1:C6", 0, 1, 2, "SUM", "T")
val lines = view.text_dump.split("\n")
expect(lines[2]).to_equal("East|15|20|35")
```

</details>

#### the West row carries West/A=30, West/B=55, row total=85

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sheet = _pivot_gui_dataset()
val view = pivot_gui_view(sheet, "A1:C6", 0, 1, 2, "SUM", "T")
val lines = view.text_dump.split("\n")
expect(lines[3]).to_equal("West|30|55|85")
```

</details>

#### the Grand Total row carries col totals A=45, B=75, and grand=120

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sheet = _pivot_gui_dataset()
val view = pivot_gui_view(sheet, "A1:C6", 0, 1, 2, "SUM", "T")
val lines = view.text_dump.split("\n")
expect(lines[4]).to_equal("Grand Total|45|75|120")
```

</details>

### pivot_gui_view: empty data range fails closed

#### an empty data range produces an error|empty-range line

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sheet = _pivot_gui_dataset()
val view = pivot_gui_view(sheet, "", 0, 1, 2, "SUM", "T")
expect(view.text_dump).to_contain("error|empty-range")
```

</details>

### pivot_gui_view: unknown agg name fails closed

#### an unknown agg name produces an error|unknown-agg line

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sheet = _pivot_gui_dataset()
val view = pivot_gui_view(sheet, "A1:C6", 0, 1, 2, "BOGUS", "T")
expect(view.text_dump).to_contain("error|unknown-agg")
```

</details>

### pivot session

#### pivot_session_view renders the same dump as a direct pivot_gui_view call

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sheet = _pivot_gui_dataset()
val session = pivot_session_new(sheet, "A1:C6", 0, 1, 2, "SUM", "T")
val view = pivot_session_view(session)
val direct = pivot_gui_view(sheet, "A1:C6", 0, 1, 2, "SUM", "T")
expect(view.text_dump).to_equal(direct.text_dump)
```

</details>

#### set_agg average changes the dump to hand-computed averages

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sheet = _pivot_gui_dataset()
var session = pivot_session_new(sheet, "A1:C6", 0, 1, 2, "SUM", "T")
session = pivot_session_set_agg(session, "average")
expect(session.last_error).to_equal("")
val view = pivot_session_view(session)
val lines = view.text_dump.split("\n")
# East/A = (10+5)/2 = 7.5, East/B = 20/1 = 20, East row = (10+20+5)/3 = 11.666666666666666
expect(lines[2]).to_equal("East|7.5|20|11.666666666666666")
# West/A = 30/1 = 30, West/B = (40+15)/2 = 27.5, West row = (30+40+15)/3 = 28.333333333333332
expect(lines[3]).to_equal("West|30|27.5|28.333333333333332")
# col A avg = (10+30+5)/3 = 15, col B avg = (20+40+15)/3 = 25, grand = 120/6 = 20
expect(lines[4]).to_equal("Grand Total|15|25|20")
```

</details>

#### set_agg with an invalid name leaves agg_name unchanged and sets last_error

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sheet = _pivot_gui_dataset()
var session = pivot_session_new(sheet, "A1:C6", 0, 1, 2, "SUM", "T")
session = pivot_session_set_agg(session, "BOGUS")
expect(session.agg_name).to_equal("SUM")
expect(session.last_error).to_equal("unknown-agg")
val view = pivot_session_view(session)
expect(view.text_dump).to_contain("East|15|20|35")
```

</details>

#### swap_fields transposes: the header row becomes the old row keys

<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sheet = _pivot_gui_dataset()
var session = pivot_session_new(sheet, "A1:C6", 0, 1, 2, "SUM", "T")
session = pivot_session_swap_fields(session)
expect(session.last_error).to_equal("")
val view = pivot_session_view(session)
val lines = view.text_dump.split("\n")
expect(lines[1]).to_equal("Row/Col|East|West|Grand Total")
# Product A row: East/A=10+5=15, West/A=30, row total=45
expect(lines[2]).to_equal("A|15|30|45")
# Product B row: East/B=20, West/B=40+15=55, row total=75
expect(lines[3]).to_equal("B|20|55|75")
# col totals: East=15+20=35, West=30+55=85, grand=120
expect(lines[4]).to_equal("Grand Total|35|85|120")
```

</details>

#### set_value_col moves the aggregated column to a second in-range numeric field

<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sheet = _pivot_gui_dataset_with_extra_col()
var session = pivot_session_new(sheet, "A1:D6", 0, 1, 2, "SUM", "T")
session = pivot_session_set_value_col(session, "D")
expect(session.last_error).to_equal("")
expect(session.value_col).to_equal(3)
val view = pivot_session_view(session)
val lines = view.text_dump.split("\n")
# D = C + 100: East/A=110+105=215, East/B=120, East row=335
expect(lines[2]).to_equal("East|215|120|335")
# West/A=130, West/B=140+115=255, West row=385
expect(lines[3]).to_equal("West|130|255|385")
# col totals: A=215+130=345, B=120+255=375, grand=720
expect(lines[4]).to_equal("Grand Total|345|375|720")
```

</details>

#### step key \

<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sheet = _pivot_gui_dataset()
val session = pivot_session_new(sheet, "A1:C6", 0, 1, 2, "sum", "T")
val step1 = pivot_gui_step(session, "a")
assert_false(step1.quit)
expect(step1.session.agg_name).to_equal("count")
val step2 = pivot_gui_step(step1.session, "a")
expect(step2.session.agg_name).to_equal("average")
val step3 = pivot_gui_step(step2.session, "a")
expect(step3.session.agg_name).to_equal("min")
val step4 = pivot_gui_step(step3.session, "a")
expect(step4.session.agg_name).to_equal("max")
val step5 = pivot_gui_step(step4.session, "a")
expect(step5.session.agg_name).to_equal("sum")
```

</details>

#### step key \

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sheet = _pivot_gui_dataset()
val session = pivot_session_new(sheet, "A1:C6", 0, 1, 2, "SUM", "T")
val step = pivot_gui_step(session, "s")
assert_false(step.quit)
expect(step.session.row_field_col).to_equal(1)
expect(step.session.col_field_col).to_equal(0)
```

</details>

#### step key \

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sheet = _pivot_gui_dataset()
val session = pivot_session_new(sheet, "A1:C6", 0, 1, 2, "SUM", "T")
val step = pivot_gui_step(session, "q")
assert_true(step.quit)
expect(step.session.agg_name).to_equal("SUM")
expect(step.session.row_field_col).to_equal(0)
expect(step.session.col_field_col).to_equal(1)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 15 |
| Active scenarios | 15 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

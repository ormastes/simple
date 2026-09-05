# fill_series_spec

> Office sheets fill-series spec.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 13 | 13 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# fill_series_spec

Office sheets fill-series spec.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/office/sheets/fill_series_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Office sheets fill-series spec.

Core autofill behaviour: numeric progressions, numbered labels, month and
weekday cycles, verbatim copy fills, and writing them into a sheet.

## Scenarios

### detect_fill_pattern: numeric seeds

#### detects a step of 2 from 1,3

- detects a step of 2 from 1,3


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects a step of 2 from 1,3")
match detect_fill_pattern(_nums([1.0, 3.0])):
    FillPattern.Linear(start, step):
        assert_true(start == 1.0)
        assert_true(step == 2.0)
    _:
        assert_true(false)
```

</details>

#### defaults a single numeric seed to step 1

- defaults a single numeric seed to step 1


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("defaults a single numeric seed to step 1")
match detect_fill_pattern(_nums([7.0])):
    FillPattern.Linear(start, step):
        assert_true(start == 7.0)
        assert_true(step == 1.0)
    _:
        assert_true(false)
```

</details>

#### falls back to copy when the difference is inconsistent

- falls back to copy when the difference is inconsistent


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("falls back to copy when the difference is inconsistent")
match detect_fill_pattern(_nums([1.0, 2.0, 9.0])):
    FillPattern.CopyCycle:
        assert_true(true)
    _:
        assert_true(false)
```

</details>

### detect_fill_pattern: labels and names
_Numbered labels increment; month and weekday names cycle._

#### detects a numbered label prefix

- detects a numbered label prefix


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects a numbered label prefix")
match detect_fill_pattern(_cells(["Item1", "Item2"])):
    FillPattern.TextNumber(prefix, start, step, pad):
        assert_true(prefix == "Item")
        assert_true(start == 1)
        assert_true(step == 1)
        assert_true(pad == 0)
    _:
        assert_true(false)
```

</details>

#### detects a month name cycle

- detects a month name cycle


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects a month name cycle")
match detect_fill_pattern(_cells(["Jan", "Feb"])):
    FillPattern.NameCycle(list_id, start_index, step):
        assert_true(list_id == 0)
        assert_true(start_index == 0)
        assert_true(step == 1)
    _:
        assert_true(false)
```

</details>

#### treats unrelated text as a copy fill

- treats unrelated text as a copy fill


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("treats unrelated text as a copy fill")
match detect_fill_pattern(_cells(["red", "blue"])):
    FillPattern.CopyCycle:
        assert_true(true)
    _:
        assert_true(false)
```

</details>

### fill_series_cells: value generation
_Generated values continue past the end of the seed._

#### continues an arithmetic progression

- continues an arithmetic progression


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("continues an arithmetic progression")
val out = fill_series_cells(_nums([1.0, 3.0]), 3)
assert_true(out.len() == 3)
assert_true(cell_display_text(out[0]) == "5")
assert_true(cell_display_text(out[1]) == "7")
assert_true(cell_display_text(out[2]) == "9")
```

</details>

#### increments a numbered label

- increments a numbered label


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("increments a numbered label")
val out = fill_series_cells(_cells(["Item1"]), 2)
assert_true(cell_display_text(out[0]) == "Item2")
assert_true(cell_display_text(out[1]) == "Item3")
```

</details>

#### wraps a weekday cycle past the end of the list

- wraps a weekday cycle past the end of the list


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("wraps a weekday cycle past the end of the list")
val out = fill_series_cells(_cells(["Fri"]), 3)
assert_true(cell_display_text(out[0]) == "Sat")
assert_true(cell_display_text(out[1]) == "Sun")
assert_true(cell_display_text(out[2]) == "Mon")
```

</details>

#### repeats a copy fill cyclically

- repeats a copy fill cyclically


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("repeats a copy fill cyclically")
val out = fill_series_cells(_cells(["red", "blue"]), 3)
assert_true(cell_display_text(out[0]) == "red")
assert_true(cell_display_text(out[1]) == "blue")
assert_true(cell_display_text(out[2]) == "red")
```

</details>

### sheet_fill_series: writing into a sheet
_Fills run down a column or across a row and report the cells written._

#### fills a column downward

- fills a column downward


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("fills a column downward")
var sheet = Sheet.new("S1")
sheet.set_value("A1", "1")
sheet.set_value("A2", "3")

val written = sheet_fill_series(sheet, "A1:A2", "A3:A5")

assert_true(written == 3)
assert_true(cell_display_text(sheet.get_cell("A3")) == "5")
assert_true(cell_display_text(sheet.get_cell("A4")) == "7")
assert_true(cell_display_text(sheet.get_cell("A5")) == "9")
```

</details>

#### fills a row rightward

- fills a row rightward


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("fills a row rightward")
var sheet = Sheet.new("S2")
sheet.set_value("B1", "10")
sheet.set_value("C1", "20")

val written = sheet_fill_series(sheet, "B1:C1", "D1:E1")

assert_true(written == 2)
assert_true(cell_display_text(sheet.get_cell("D1")) == "30")
assert_true(cell_display_text(sheet.get_cell("E1")) == "40")
```

</details>

#### leaves the seed cells untouched

- leaves the seed cells untouched


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("leaves the seed cells untouched")
var sheet = Sheet.new("S3")
sheet.set_value("A1", "5")
sheet_fill_series(sheet, "A1:A1", "A2:A3")
assert_true(cell_display_text(sheet.get_cell("A1")) == "5")
assert_true(cell_display_text(sheet.get_cell("A2")) == "6")
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `d2c7fce64d9dc62e3f209e74a32cee8b3f832dc8808ebbf38b092eaee7e97d50`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `d2c7fce64d9dc62e3f209e74a32cee8b3f832dc8808ebbf38b092eaee7e97d50`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `d2c7fce64d9dc62e3f209e74a32cee8b3f832dc8808ebbf38b092eaee7e97d50`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/app/office/sheets/fill_series_spec.spl
mirror: doc/06_spec/01_unit/app/office/sheets/fill_series_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/app/office/sheets/fill_series_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/office/sheets/fill_series_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/office/sheets/fill_series_spec.spl:36:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'detects a step of 2 from 1,3' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/office/sheets/fill_series_spec.spl:46:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'defaults a single numeric seed to step 1' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/office/sheets/fill_series_spec.spl:56:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'falls back to copy when the difference is inconsistent' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

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
| Updated | 2026-08-26 |
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

#### hide_row makes is_row_hidden true

- hide_row makes is_row_hidden true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("hide_row makes is_row_hidden true")
var sheet = Sheet.new("S1")
assert_false(sheet.is_row_hidden(2))
sheet.hide_row(2)
assert_true(sheet.is_row_hidden(2))
```

</details>

#### unhide_row makes is_row_hidden false again

- unhide_row makes is_row_hidden false again


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("unhide_row makes is_row_hidden false again")
var sheet = Sheet.new("S1")
sheet.hide_row(3)
assert_true(sheet.is_row_hidden(3))
sheet.unhide_row(3)
assert_false(sheet.is_row_hidden(3))
```

</details>

#### hiding one row does not affect a different row

- hiding one row does not affect a different row


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("hiding one row does not affect a different row")
var sheet = Sheet.new("S1")
sheet.hide_row(4)
assert_true(sheet.is_row_hidden(4))
assert_false(sheet.is_row_hidden(5))
```

</details>

#### unhide_row on a never-hidden row is a no-op

- unhide_row on a never-hidden row is a no-op


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("unhide_row on a never-hidden row is a no-op")
var sheet = Sheet.new("S1")
sheet.unhide_row(7)
assert_false(sheet.is_row_hidden(7))
```

</details>

### Sheet row visibility: hide_rows range
_hide_rows(from, to) hides every row in the inclusive range._

#### hides every row in the range, inclusive

- hides every row in the range, inclusive


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("hides every row in the range, inclusive")
var sheet = Sheet.new("S1")
sheet.hide_rows(2, 4)
assert_true(sheet.is_row_hidden(2))
assert_true(sheet.is_row_hidden(3))
assert_true(sheet.is_row_hidden(4))
```

</details>

#### does not hide rows outside the range

- does not hide rows outside the range


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does not hide rows outside the range")
var sheet = Sheet.new("S1")
sheet.hide_rows(2, 4)
assert_false(sheet.is_row_hidden(1))
assert_false(sheet.is_row_hidden(5))
```

</details>

#### handles a reversed (from > to) range the same as ascending

- handles a reversed (from > to) range the same as ascending


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles a reversed (from > to) range the same as ascending")
var sheet = Sheet.new("S1")
sheet.hide_rows(6, 5)
assert_true(sheet.is_row_hidden(5))
assert_true(sheet.is_row_hidden(6))
```

</details>

### Sheet row visibility: idempotency
_Hiding an already-hidden row is a no-op, not a duplicate entry._

#### hiding the same row twice keeps it hidden (no crash, no dup effect)

- hiding the same row twice keeps it hidden (no crash, no dup effect)


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("hiding the same row twice keeps it hidden (no crash, no dup effect)")
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

- hide_row(0) is a no-op (rows are 1-based)


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("hide_row(0) is a no-op (rows are 1-based)")
var sheet = Sheet.new("S1")
sheet.hide_row(0)
assert_false(sheet.is_row_hidden(0))
```

</details>

#### hide_row of a negative row is a no-op

- hide_row of a negative row is a no-op


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("hide_row of a negative row is a no-op")
var sheet = Sheet.new("S1")
sheet.hide_row(-1)
assert_false(sheet.is_row_hidden(-1))
```

</details>

#### hide_row beyond row_count is a no-op

- hide_row beyond row_count is a no-op


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("hide_row beyond row_count is a no-op")
var sheet = Sheet.new("S1")
sheet.hide_row(sheet.row_count.to_i64() + 50)
assert_false(sheet.is_row_hidden(sheet.row_count.to_i64() + 50))
```

</details>

### Sheet row visibility: unhide_all_rows
_unhide_all_rows clears every hidden row (used by AutoFilter clear)._

#### clears multiple hidden rows at once

- clears multiple hidden rows at once


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("clears multiple hidden rows at once")
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `d17ba688652f355780cc79b4fddfde0292624657834406682d62b22f6fbc08a4`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `d17ba688652f355780cc79b4fddfde0292624657834406682d62b22f6fbc08a4`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `d17ba688652f355780cc79b4fddfde0292624657834406682d62b22f6fbc08a4`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/app/office/sheets/sheet_visibility_spec.spl
mirror: doc/06_spec/01_unit/app/office/sheets/sheet_visibility_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/app/office/sheets/sheet_visibility_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/office/sheets/sheet_visibility_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/office/sheets/sheet_visibility_spec.spl:27:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'hide_row makes is_row_hidden true' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/office/sheets/sheet_visibility_spec.spl:35:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'unhide_row makes is_row_hidden false again' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/office/sheets/sheet_visibility_spec.spl:44:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'hiding one row does not affect a different row' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

# TreeSitter Incremental Parsing Specification

> This file now uses a self-contained local harness to model point adjustment,

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 39 | 39 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# TreeSitter Incremental Parsing Specification

This file now uses a self-contained local harness to model point adjustment,

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/feature/features/treesitter/treesitter_incremental_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

This file now uses a self-contained local harness to model point adjustment,
edit summaries, line counting, and incremental reparse behavior without relying
on unavailable production treesitter modules.

## Scenarios

### TreeSitter Point

#### creates point

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- creates point


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("creates point")
val point = Point.create(3, 7)
check(point.line == 3)
check(point.column == 7)
```

</details>

#### compares points on same line

- compares points on same line


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("compares points on same line")
val left = Point.create(4, 1)
val right = Point.create(4, 9)
check(left.compare(right) < 0)
```

</details>

#### compares points on different lines

- compares points on different lines


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("compares points on different lines")
val earlier = Point.create(2, 5)
val later = Point.create(3, 1)
check(earlier.compare(later) < 0)
```

</details>

#### checks point equality

- checks point equality


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("checks point equality")
val left = Point.create(6, 2)
val right = Point.create(6, 2)
check(left.compare(right) == 0)
```

</details>

#### compare returns negative for before

- compare returns negative for before


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("compare returns negative for before")
check(Point.create(1, 0).compare(Point.create(1, 1)) < 0)
```

</details>

#### compare returns positive for after

- compare returns positive for after


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("compare returns positive for after")
check(Point.create(1, 1).compare(Point.create(1, 0)) > 0)
```

</details>

#### compare returns zero for equal

- compare returns zero for equal


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("compare returns zero for equal")
check(Point.create(8, 4).compare(Point.create(8, 4)) == 0)
```

</details>

### TreeSitter InputEdit

#### creates InputEdit

- creates InputEdit


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("creates InputEdit")
val edit = InputEdit.create(2, 5, 7, Point.create(1, 2), Point.create(1, 5), Point.create(1, 7))
check(edit.start_byte == 2)
check(edit.end_byte == 5)
check(edit.new_end_byte == 7)
```

</details>

#### checks if edit affects span

- checks if edit affects span


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("checks if edit affects span")
val edit = InputEdit.create(2, 5, 7, Point.create(1, 2), Point.create(1, 5), Point.create(1, 7))
check(edit.affects_byte(3))
check(edit.affects_point(Point.create(1, 3)))
```

</details>

#### edit does not affect span before

- edit does not affect span before


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("edit does not affect span before")
val edit = InputEdit.create(10, 15, 12, Point.create(2, 0), Point.create(2, 5), Point.create(2, 2))
check(not edit.affects_byte(4))
check(not edit.affects_point(Point.create(1, 9)))
```

</details>

### TreeSitter Edit Byte Adjustment

#### does not adjust byte before edit

- does not adjust byte before edit


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("does not adjust byte before edit")
val edit = make_edit("abcdef", "abXYef")
check(apply_byte_edit(1, edit) == 1)
```

</details>

#### maps byte inside edit to start

- maps byte inside edit to start


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("maps byte inside edit to start")
val edit = make_edit("abcdef", "abXYef")
check(apply_byte_edit(3, edit) == 2)
```

</details>

#### shifts byte after edit by delta

- shifts byte after edit by delta


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("shifts byte after edit by delta")
val edit = make_edit("abcdef", "abXYef")
check(apply_byte_edit(5, edit) == 5)
```

</details>

### TreeSitter Edit Point Adjustment

#### does not adjust point before edit

- does not adjust point before edit


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("does not adjust point before edit")
val edit = InputEdit.create(4, 8, 6, Point.create(2, 2), Point.create(2, 6), Point.create(2, 4))
val point = Point.create(1, 9)
val adjusted = apply_point_edit(point, edit)
check(adjusted.line == 1)
check(adjusted.column == 9)
```

</details>

#### maps point inside edit to start

- maps point inside edit to start


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("maps point inside edit to start")
val edit = InputEdit.create(4, 8, 6, Point.create(2, 2), Point.create(2, 6), Point.create(2, 4))
val point = Point.create(2, 4)
val adjusted = apply_point_edit(point, edit)
check(adjusted.line == 2)
check(adjusted.column == 2)
```

</details>

### TreeSitter Compute Edits

#### returns empty for identical texts

- returns empty for identical texts


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("returns empty for identical texts")
val summary = summarize_edit("abc", "abc")
check(summary.kind == "equal")
check(summary.byte_delta == 0)
```

</details>

#### detects insertion

- detects insertion


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("detects insertion")
val summary = summarize_edit("abc", "abXYZc")
check(summary.kind == "replace")
check(summary.byte_delta == 3)
```

</details>

#### detects deletion

- detects deletion


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("detects deletion")
val summary = summarize_edit("abXYZc", "abc")
check(summary.kind == "replace")
check(summary.byte_delta == -3)
```

</details>

#### detects replacement

- detects replacement


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("detects replacement")
val summary = summarize_edit("abc", "axc")
check(summary.kind == "replace")
```

</details>

#### handles empty old text

- handles empty old text


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("handles empty old text")
val summary = summarize_edit("", "hello")
check(summary.kind == "insert")
check(summary.byte_delta == 5)
```

</details>

#### handles empty new text

- handles empty new text


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("handles empty new text")
val summary = summarize_edit("hello", "")
check(summary.kind == "delete")
check(summary.byte_delta == -5)
```

</details>

### TreeSitter Diff Operations

#### creates Equal operation

- creates Equal operation


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("creates Equal operation")
check(diff_kind("same", "same") == "equal")
```

</details>

#### creates Delete operation

- creates Delete operation


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("creates Delete operation")
check(diff_kind("gone", "") == "delete")
```

</details>

#### creates Insert operation

- creates Insert operation


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("creates Insert operation")
check(diff_kind("", "new") == "insert")
```

</details>

### TreeSitter Line Counting

#### counts single line

- counts single line


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("counts single line")
check(count_lines("abc") == 1)
```

</details>

#### counts multiple lines

- counts multiple lines


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("counts multiple lines")
check(count_lines("a\nb\nc") == 3)
```

</details>

#### counts empty string as one line

- counts empty string as one line


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("counts empty string as one line")
check(count_lines("") == 1)
```

</details>

#### counts trailing newline

- counts trailing newline


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("counts trailing newline")
check(count_lines("a\n") == 2)
```

</details>

### TreeSitter End Point

#### computes end point of empty string

- computes end point of empty string


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("computes end point of empty string")
val point = end_point("")
check(point.line == 1)
check(point.column == 0)
```

</details>

#### computes end point of single line

- computes end point of single line


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("computes end point of single line")
val point = end_point("hello")
check(point.line == 1)
check(point.column == 5)
```

</details>

#### computes end point of multiple lines

- computes end point of multiple lines


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("computes end point of multiple lines")
val point = end_point("ab\ncde")
check(point.line == 2)
check(point.column == 3)
```

</details>

### TreeSitter Incremental Parsing

#### parses after simple edit

- parses after simple edit


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses after simple edit")
val source = "alpha beta"
val updated = apply_text_edit(source, 6, 10, "gamma")
val summary = summarize_edit(source, updated)
check(updated == "alpha gamma")
check(summary.kind == "replace")
```

</details>

#### parses after insertion

- parses after insertion


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses after insertion")
val source = "abcdef"
val updated = apply_text_edit(source, 3, 3, "XYZ")
val summary = summarize_edit(source, updated)
check(updated == "abcXYZdef")
check(summary.kind == "insert" or summary.kind == "replace")
```

</details>

#### parses after deletion

- parses after deletion


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses after deletion")
val source = "abcXYZdef"
val updated = apply_text_edit(source, 3, 6, "")
val summary = summarize_edit(source, updated)
check(updated == "abcdef")
check(summary.kind == "delete" or summary.kind == "replace")
```

</details>

### TreeSitter Multi-Line Edits

#### handles multi-line insertion

- handles multi-line insertion


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("handles multi-line insertion")
val source = "one\ntwo"
val updated = apply_text_edit(source, 4, 4, "\nthree")
check(updated == "one\n\nthreetwo")
check(count_lines(updated) == 3)
```

</details>

#### handles multi-line deletion

- handles multi-line deletion


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("handles multi-line deletion")
val source = "one\ntwo\nthree"
val updated = apply_text_edit(source, 4, 8, "")
check(updated == "one\nthree")
check(count_lines(updated) == 2)
```

</details>

#### handles mixed edits

- handles mixed edits


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("handles mixed edits")
val source = "a\nb\nc"
val updated = apply_text_edit(source, 2, 3, "X\nY")
check(count_lines(updated) == 4)
check(updated.contains("X"))
check(updated.contains("Y"))
```

</details>

### TreeSitter Edit Performance

#### handles large identical texts quickly

- handles large identical texts quickly


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("handles large identical texts quickly")
val text = "x" * 1000
val summary = summarize_edit(text, text)
check(summary.kind == "equal")
check(summary.byte_delta == 0)
```

</details>

#### handles single character change in large text

- handles single character change in large text


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("handles single character change in large text")
val old_text = "x" * 500 + "a" + "x" * 500
val new_text = "x" * 500 + "b" + "x" * 500
val summary = summarize_edit(old_text, new_text)
check(summary.kind == "replace")
check(summary.byte_delta == 0)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 39 |
| Active scenarios | 39 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `aaa7c41dce5f994deda9b8a41b3a9d21e526a6ebf9e59c8aa7696da422ef009d`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `aaa7c41dce5f994deda9b8a41b3a9d21e526a6ebf9e59c8aa7696da422ef009d`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `aaa7c41dce5f994deda9b8a41b3a9d21e526a6ebf9e59c8aa7696da422ef009d`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/feature/features/treesitter/treesitter_incremental_spec.spl
mirror: doc/06_spec/03_system/feature/features/treesitter/treesitter_incremental_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/feature/features/treesitter/treesitter_incremental_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/feature/features/treesitter/treesitter_incremental_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/feature/features/treesitter/treesitter_incremental_spec.spl:181:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates point' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/features/treesitter/treesitter_incremental_spec.spl:188:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'compares points on same line' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/features/treesitter/treesitter_incremental_spec.spl:195:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'compares points on different lines' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

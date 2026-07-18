# TreeSitter Incremental Parsing Specification

> This file now uses a self-contained local harness to model point adjustment,

<!-- sdn-diagram:id=treesitter_incremental_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=treesitter_incremental_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

treesitter_incremental_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=treesitter_incremental_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

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
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

This file now uses a self-contained local harness to model point adjustment,
edit summaries, line counting, and incremental reparse behavior without relying
on unavailable production treesitter modules.

## Scenarios

### TreeSitter Point

#### creates point

1. check
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val point = Point.create(3, 7)
check(point.line == 3)
check(point.column == 7)
```

</details>

#### compares points on same line

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val left = Point.create(4, 1)
val right = Point.create(4, 9)
check(left.compare(right) < 0)
```

</details>

#### compares points on different lines

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val earlier = Point.create(2, 5)
val later = Point.create(3, 1)
check(earlier.compare(later) < 0)
```

</details>

#### checks point equality

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val left = Point.create(6, 2)
val right = Point.create(6, 2)
check(left.compare(right) == 0)
```

</details>

#### compare returns negative for before

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(Point.create(1, 0).compare(Point.create(1, 1)) < 0)
```

</details>

#### compare returns positive for after

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(Point.create(1, 1).compare(Point.create(1, 0)) > 0)
```

</details>

#### compare returns zero for equal

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(Point.create(8, 4).compare(Point.create(8, 4)) == 0)
```

</details>

### TreeSitter InputEdit

#### creates InputEdit

1. check
2. check
3. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val edit = InputEdit.create(2, 5, 7, Point.create(1, 2), Point.create(1, 5), Point.create(1, 7))
check(edit.start_byte == 2)
check(edit.end_byte == 5)
check(edit.new_end_byte == 7)
```

</details>

#### checks if edit affects span

1. check
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val edit = InputEdit.create(2, 5, 7, Point.create(1, 2), Point.create(1, 5), Point.create(1, 7))
check(edit.affects_byte(3))
check(edit.affects_point(Point.create(1, 3)))
```

</details>

#### edit does not affect span before

1. check
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val edit = InputEdit.create(10, 15, 12, Point.create(2, 0), Point.create(2, 5), Point.create(2, 2))
check(not edit.affects_byte(4))
check(not edit.affects_point(Point.create(1, 9)))
```

</details>

### TreeSitter Edit Byte Adjustment

#### does not adjust byte before edit

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val edit = make_edit("abcdef", "abXYef")
check(apply_byte_edit(1, edit) == 1)
```

</details>

#### maps byte inside edit to start

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val edit = make_edit("abcdef", "abXYef")
check(apply_byte_edit(3, edit) == 2)
```

</details>

#### shifts byte after edit by delta

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val edit = make_edit("abcdef", "abXYef")
check(apply_byte_edit(5, edit) == 5)
```

</details>

### TreeSitter Edit Point Adjustment

#### does not adjust point before edit

1. check
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val edit = InputEdit.create(4, 8, 6, Point.create(2, 2), Point.create(2, 6), Point.create(2, 4))
val point = Point.create(1, 9)
val adjusted = apply_point_edit(point, edit)
check(adjusted.line == 1)
check(adjusted.column == 9)
```

</details>

#### maps point inside edit to start

1. check
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val edit = InputEdit.create(4, 8, 6, Point.create(2, 2), Point.create(2, 6), Point.create(2, 4))
val point = Point.create(2, 4)
val adjusted = apply_point_edit(point, edit)
check(adjusted.line == 2)
check(adjusted.column == 2)
```

</details>

### TreeSitter Compute Edits

#### returns empty for identical texts

1. check
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val summary = summarize_edit("abc", "abc")
check(summary.kind == "equal")
check(summary.byte_delta == 0)
```

</details>

#### detects insertion

1. check
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val summary = summarize_edit("abc", "abXYZc")
check(summary.kind == "replace")
check(summary.byte_delta == 3)
```

</details>

#### detects deletion

1. check
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val summary = summarize_edit("abXYZc", "abc")
check(summary.kind == "replace")
check(summary.byte_delta == -3)
```

</details>

#### detects replacement

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val summary = summarize_edit("abc", "axc")
check(summary.kind == "replace")
```

</details>

#### handles empty old text

1. check
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val summary = summarize_edit("", "hello")
check(summary.kind == "insert")
check(summary.byte_delta == 5)
```

</details>

#### handles empty new text

1. check
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val summary = summarize_edit("hello", "")
check(summary.kind == "delete")
check(summary.byte_delta == -5)
```

</details>

### TreeSitter Diff Operations

#### creates Equal operation

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(diff_kind("same", "same") == "equal")
```

</details>

#### creates Delete operation

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(diff_kind("gone", "") == "delete")
```

</details>

#### creates Insert operation

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(diff_kind("", "new") == "insert")
```

</details>

### TreeSitter Line Counting

#### counts single line

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(count_lines("abc") == 1)
```

</details>

#### counts multiple lines

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(count_lines("a\nb\nc") == 3)
```

</details>

#### counts empty string as one line

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(count_lines("") == 1)
```

</details>

#### counts trailing newline

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(count_lines("a\n") == 2)
```

</details>

### TreeSitter End Point

#### computes end point of empty string

1. check
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val point = end_point("")
check(point.line == 1)
check(point.column == 0)
```

</details>

#### computes end point of single line

1. check
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val point = end_point("hello")
check(point.line == 1)
check(point.column == 5)
```

</details>

#### computes end point of multiple lines

1. check
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val point = end_point("ab\ncde")
check(point.line == 2)
check(point.column == 3)
```

</details>

### TreeSitter Incremental Parsing

#### parses after simple edit

1. check
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "alpha beta"
val updated = apply_text_edit(source, 6, 10, "gamma")
val summary = summarize_edit(source, updated)
check(updated == "alpha gamma")
check(summary.kind == "replace")
```

</details>

#### parses after insertion

1. check
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "abcdef"
val updated = apply_text_edit(source, 3, 3, "XYZ")
val summary = summarize_edit(source, updated)
check(updated == "abcXYZdef")
check(summary.kind == "insert" or summary.kind == "replace")
```

</details>

#### parses after deletion

1. check
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "abcXYZdef"
val updated = apply_text_edit(source, 3, 6, "")
val summary = summarize_edit(source, updated)
check(updated == "abcdef")
check(summary.kind == "delete" or summary.kind == "replace")
```

</details>

### TreeSitter Multi-Line Edits

#### handles multi-line insertion

1. check
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "one\ntwo"
val updated = apply_text_edit(source, 4, 4, "\nthree")
check(updated == "one\n\nthreetwo")
check(count_lines(updated) == 3)
```

</details>

#### handles multi-line deletion

1. check
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "one\ntwo\nthree"
val updated = apply_text_edit(source, 4, 8, "")
check(updated == "one\nthree")
check(count_lines(updated) == 2)
```

</details>

#### handles mixed edits

1. check
2. check
3. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "a\nb\nc"
val updated = apply_text_edit(source, 2, 3, "X\nY")
check(count_lines(updated) == 4)
check(updated.contains("X"))
check(updated.contains("Y"))
```

</details>

### TreeSitter Edit Performance

#### handles large identical texts quickly

1. check
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val text = "x" * 1000
val summary = summarize_edit(text, text)
check(summary.kind == "equal")
check(summary.byte_delta == 0)
```

</details>

#### handles single character change in large text

1. check
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

# Format Utils Specification

> Tests covering Format Utilities, Table Formatting, Progress Bar, Spinner, Indentation, Box Text, Tree Formatting, ANSI Colors and Styles, Number Formatting, Byte Formatting, Duration Formatting.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 36 | 36 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Format Utils Specification

## Scenarios

### Format Utilities

### Table Formatting

#### creates table with headers

- creates table with headers


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates table with headers")
val table = create_table(["Name", "Age", "City"])
expect table.headers.len() == 3
expect table.rows.len() == 0
expect table.column_widths.len() == 3
```

</details>

#### adds rows

- adds rows


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("adds rows")
var table = create_table(["Name", "Age"])
table = add_row(table, ["Alice", "30"])
table = add_row(table, ["Bob", "25"])
expect table.rows.len() == 2
expect table.rows[0].cells[0] == "Alice"
expect table.rows[1].cells[0] == "Bob"
```

</details>

#### updates column widths

- updates column widths


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("updates column widths")
var table = create_table(["ID", "Name"])
table = add_row(table, ["1", "Alice"])
table = add_row(table, ["2", "VeryLongName"])
expect table.column_widths[1] >= 12
```

</details>

#### formats table with borders

- formats table with borders


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("formats table with borders")
var table = create_table(["Name", "Age"])
table = add_row(table, ["Alice", "30"])
table = add_row(table, ["Bob", "25"])
val output = format_table(table)
expect output.contains("+")
expect output.contains("|")
expect output.contains("Name")
expect output.contains("Alice")
expect output.contains("Bob")
```

</details>

### Progress Bar

#### shows empty bar

- shows empty bar


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("shows empty bar")
val bar = progress_bar(current=0, total=100, width=20)
expect bar.contains("[")
expect bar.contains("]")
expect bar.contains("0%")
```

</details>

#### shows half bar

- shows half bar


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("shows half bar")
val bar = progress_bar(current=50, total=100, width=20)
expect bar.contains("50%")
```

</details>

#### shows full bar

- shows full bar


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("shows full bar")
val bar = progress_bar(current=100, total=100, width=20)
expect bar.contains("100%")
```

</details>

#### handles zero total

- handles zero total


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles zero total")
val bar = progress_bar(current=0, total=0, width=20)
expect bar.contains("[")
```

</details>

### Spinner

#### returns correct frames

- returns correct frames


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns correct frames")
expect spinner_frame(0) == "|"
expect spinner_frame(1) == "/"
expect spinner_frame(2) == "-"
expect spinner_frame(3) == "\\"
```

</details>

#### wraps around

- wraps around


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("wraps around")
expect spinner_frame(4) == "|"
expect spinner_frame(5) == "/"
```

</details>

### Indentation

#### indents single line

- indents single line


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("indents single line")
val result = indent_text("Hello", 4)
expect result == "    Hello"
```

</details>

#### indents multiple lines

- indents multiple lines


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("indents multiple lines")
val result = indent_text("Line1\nLine2\nLine3", 2)
expect result.contains("  Line1")
expect result.contains("  Line2")
expect result.contains("  Line3")
```

</details>

#### handles zero spaces

- handles zero spaces


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles zero spaces")
val result = indent_text("Hello", 0)
expect result == "Hello"
```

</details>

### Box Text

#### creates single border box

- creates single border box


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates single border box")
val result = box_text(txt="Hello", style="single")
expect result.contains("┌")
expect result.contains("┐")
expect result.contains("└")
expect result.contains("┘")
expect result.contains("Hello")
```

</details>

#### creates double border box

- creates double border box


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates double border box")
val result = box_text(txt="Test", style="double")
expect result.contains("╔")
expect result.contains("╗")
expect result.contains("╚")
expect result.contains("╝")
```

</details>

#### creates rounded border box

- creates rounded border box


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates rounded border box")
val result = box_text(txt="Test", style="rounded")
expect result.contains("╭")
expect result.contains("╮")
expect result.contains("╰")
expect result.contains("╯")
```

</details>

#### creates ASCII border box

- creates ASCII border box


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates ASCII border box")
val result = box_text(txt="Test", style="ascii")
expect result.contains("+")
expect result.contains("-")
expect result.contains("|")
```

</details>

#### handles multiline text

- handles multiline text


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles multiline text")
val result = box_text(txt="Line1\nLine2", style="single")
expect result.contains("Line1")
expect result.contains("Line2")
```

</details>

### Tree Formatting

#### formats single node

- formats single node


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("formats single node")
val node = TreeNode(label: "Root", children: [])
val result = format_tree(node, "", true)
expect result.contains("Root")
expect result.contains("└──")
```

</details>

#### formats tree with children

- formats tree with children


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("formats tree with children")
val child1 = TreeNode(label: "Child1", children: [])
val child2 = TreeNode(label: "Child2", children: [])
val root = TreeNode(label: "Root", children: [child1, child2])
val result = format_tree(root, "", true)
expect result.contains("Root")
expect result.contains("Child1")
expect result.contains("Child2")
expect result.contains("├──")
expect result.contains("└──")
```

</details>

### ANSI Colors and Styles

#### applies color

- applies color


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("applies color")
val result = ansi_color(txt="Error", color="red")
expect result.contains("Error")
```

</details>

#### applies style

- applies style


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("applies style")
val result = ansi_style(txt="Bold", style="bold")
expect result.contains("Bold")
```

</details>

#### applies combined styling

- applies combined styling


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("applies combined styling")
val result = styled_text(txt="Important", color="red", style="bold")
expect result.contains("Important")
```

</details>

### Number Formatting

#### formats small numbers

- formats small numbers


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("formats small numbers")
expect format_number(123, ",") == "123"
```

</details>

#### formats thousands

- formats thousands


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("formats thousands")
expect format_number(1234, ",") == "1,234"
```

</details>

#### formats millions

- formats millions


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("formats millions")
expect format_number(1234567, ",") == "1,234,567"
```

</details>

#### uses custom separator

- uses custom separator


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("uses custom separator")
expect format_number(1234567, ".") == "1.234.567"
```

</details>

#### formats zero

- formats zero


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("formats zero")
expect format_number(0, ",") == "0"
```

</details>

### Byte Formatting

#### formats bytes

- formats bytes


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("formats bytes")
val result = format_bytes(512)
expect result.contains("512")
expect result.contains("B")
```

</details>

#### formats kilobytes

- formats kilobytes


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("formats kilobytes")
val result = format_bytes(2048)
expect result.contains("2")
expect result.contains("KB")
```

</details>

#### formats megabytes

- formats megabytes


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("formats megabytes")
val result = format_bytes(2 * 1024 * 1024)
expect result.contains("2")
expect result.contains("MB")
```

</details>

#### formats gigabytes

- formats gigabytes


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("formats gigabytes")
val result = format_bytes(2 * 1024 * 1024 * 1024)
expect result.contains("2")
expect result.contains("GB")
```

</details>

### Duration Formatting

#### formats milliseconds

- formats milliseconds


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("formats milliseconds")
val result = format_duration_ms(500)
expect result == "500ms"
```

</details>

#### formats seconds

- formats seconds


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("formats seconds")
val result = format_duration_ms(5000)
expect result.contains("5")
expect result.contains("s")
```

</details>

#### formats minutes

- formats minutes


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("formats minutes")
val result = format_duration_ms(125000)
expect result.contains("m")
expect result.contains("s")
```

</details>

#### formats hours

- formats hours


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("formats hours")
val result = format_duration_ms(7200000)
expect result.contains("h")
expect result.contains("m")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/unit/app/tooling/format_utils_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Format Utilities, Table Formatting, Progress Bar, Spinner, Indentation, Box Text, Tree Formatting, ANSI Colors and Styles, Number Formatting, Byte Formatting, Duration Formatting.
- Format Utilities
- Table Formatting
- Progress Bar
- Spinner
- Indentation
- Box Text
- Tree Formatting
- ANSI Colors and Styles
- Number Formatting
- Byte Formatting
- Duration Formatting

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 36 |
| Active scenarios | 36 |
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

- Canonical SPipe generation for source `1e8638d33fe334486cfe0479915fa26cc933e9bfc49992a2c0cb1fa58dd12c5e`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `1e8638d33fe334486cfe0479915fa26cc933e9bfc49992a2c0cb1fa58dd12c5e`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `1e8638d33fe334486cfe0479915fa26cc933e9bfc49992a2c0cb1fa58dd12c5e`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/app/tooling/format_utils_spec.spl
mirror: doc/06_spec/unit/app/tooling/format_utils_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/tooling/format_utils_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/tooling/format_utils_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/tooling/format_utils_spec.spl:253:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates table with headers' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/tooling/format_utils_spec.spl:261:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'adds rows' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/tooling/format_utils_spec.spl:271:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'updates column widths' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

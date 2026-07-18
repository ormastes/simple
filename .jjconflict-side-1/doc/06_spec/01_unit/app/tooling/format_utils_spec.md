# Format Utils Specification

> 1. expect table headers len

<!-- sdn-diagram:id=format_utils_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=format_utils_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

format_utils_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=format_utils_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

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

1. expect table headers len
2. expect table rows len
3. expect table column widths len


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val table = create_table(["Name", "Age", "City"])
expect table.headers.len() == 3
expect table.rows.len() == 0
expect table.column_widths.len() == 3
```

</details>

#### adds rows

1. var table = create table
2. table = add row
3. table = add row
4. expect table rows len


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var table = create_table(["Name", "Age"])
table = add_row(table, ["Alice", "30"])
table = add_row(table, ["Bob", "25"])
expect table.rows.len() == 2
expect table.rows[0].cells[0] == "Alice"
expect table.rows[1].cells[0] == "Bob"
```

</details>

#### updates column widths

1. var table = create table
2. table = add row
3. table = add row


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var table = create_table(["ID", "Name"])
table = add_row(table, ["1", "Alice"])
table = add_row(table, ["2", "VeryLongName"])
expect table.column_widths[1] >= 12
```

</details>

#### formats table with borders

1. var table = create table
2. table = add row
3. table = add row
4. expect output contains
5. expect output contains
6. expect output contains
7. expect output contains
8. expect output contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. expect bar contains
2. expect bar contains
3. expect bar contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bar = progress_bar(current=0, total=100, width=20)
expect bar.contains("[")
expect bar.contains("]")
expect bar.contains("0%")
```

</details>

#### shows half bar

1. expect bar contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bar = progress_bar(current=50, total=100, width=20)
expect bar.contains("50%")
```

</details>

#### shows full bar

1. expect bar contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bar = progress_bar(current=100, total=100, width=20)
expect bar.contains("100%")
```

</details>

#### handles zero total

1. expect bar contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bar = progress_bar(current=0, total=0, width=20)
expect bar.contains("[")
```

</details>

### Spinner

#### returns correct frames

1. expect spinner frame
2. expect spinner frame
3. expect spinner frame
4. expect spinner frame


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect spinner_frame(0) == "|"
expect spinner_frame(1) == "/"
expect spinner_frame(2) == "-"
expect spinner_frame(3) == "\\"
```

</details>

#### wraps around

1. expect spinner frame
2. expect spinner frame


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect spinner_frame(4) == "|"
expect spinner_frame(5) == "/"
```

</details>

### Indentation

#### indents single line

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = indent_text("Hello", 4)
expect result == "    Hello"
```

</details>

#### indents multiple lines

1. expect result contains
2. expect result contains
3. expect result contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = indent_text("Line1\nLine2\nLine3", 2)
expect result.contains("  Line1")
expect result.contains("  Line2")
expect result.contains("  Line3")
```

</details>

#### handles zero spaces

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = indent_text("Hello", 0)
expect result == "Hello"
```

</details>

### Box Text

#### creates single border box

1. expect result contains
2. expect result contains
3. expect result contains
4. expect result contains
5. expect result contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = box_text(txt="Hello", style="single")
expect result.contains("┌")
expect result.contains("┐")
expect result.contains("└")
expect result.contains("┘")
expect result.contains("Hello")
```

</details>

#### creates double border box

1. expect result contains
2. expect result contains
3. expect result contains
4. expect result contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = box_text(txt="Test", style="double")
expect result.contains("╔")
expect result.contains("╗")
expect result.contains("╚")
expect result.contains("╝")
```

</details>

#### creates rounded border box

1. expect result contains
2. expect result contains
3. expect result contains
4. expect result contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = box_text(txt="Test", style="rounded")
expect result.contains("╭")
expect result.contains("╮")
expect result.contains("╰")
expect result.contains("╯")
```

</details>

#### creates ASCII border box

1. expect result contains
2. expect result contains
3. expect result contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = box_text(txt="Test", style="ascii")
expect result.contains("+")
expect result.contains("-")
expect result.contains("|")
```

</details>

#### handles multiline text

1. expect result contains
2. expect result contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = box_text(txt="Line1\nLine2", style="single")
expect result.contains("Line1")
expect result.contains("Line2")
```

</details>

### Tree Formatting

#### formats single node

1. expect result contains
2. expect result contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val node = TreeNode(label: "Root", children: [])
val result = format_tree(node, "", true)
expect result.contains("Root")
expect result.contains("└──")
```

</details>

#### formats tree with children

1. expect result contains
2. expect result contains
3. expect result contains
4. expect result contains
5. expect result contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. expect result contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = ansi_color(txt="Error", color="red")
expect result.contains("Error")
```

</details>

#### applies style

1. expect result contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = ansi_style(txt="Bold", style="bold")
expect result.contains("Bold")
```

</details>

#### applies combined styling

1. expect result contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = styled_text(txt="Important", color="red", style="bold")
expect result.contains("Important")
```

</details>

### Number Formatting

#### formats small numbers

1. expect format number


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect format_number(123, ",") == "123"
```

</details>

#### formats thousands

1. expect format number


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect format_number(1234, ",") == "1,234"
```

</details>

#### formats millions

1. expect format number


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect format_number(1234567, ",") == "1,234,567"
```

</details>

#### uses custom separator

1. expect format number


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect format_number(1234567, ".") == "1.234.567"
```

</details>

#### formats zero

1. expect format number


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect format_number(0, ",") == "0"
```

</details>

### Byte Formatting

#### formats bytes

1. expect result contains
2. expect result contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = format_bytes(512)
expect result.contains("512")
expect result.contains("B")
```

</details>

#### formats kilobytes

1. expect result contains
2. expect result contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = format_bytes(2048)
expect result.contains("2")
expect result.contains("KB")
```

</details>

#### formats megabytes

1. expect result contains
2. expect result contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = format_bytes(2 * 1024 * 1024)
expect result.contains("2")
expect result.contains("MB")
```

</details>

#### formats gigabytes

1. expect result contains
2. expect result contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = format_bytes(2 * 1024 * 1024 * 1024)
expect result.contains("2")
expect result.contains("GB")
```

</details>

### Duration Formatting

#### formats milliseconds

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = format_duration_ms(500)
expect result == "500ms"
```

</details>

#### formats seconds

1. expect result contains
2. expect result contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = format_duration_ms(5000)
expect result.contains("5")
expect result.contains("s")
```

</details>

#### formats minutes

1. expect result contains
2. expect result contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = format_duration_ms(125000)
expect result.contains("m")
expect result.contains("s")
```

</details>

#### formats hours

1. expect result contains
2. expect result contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
| Source | `test/01_unit/app/tooling/format_utils_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
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

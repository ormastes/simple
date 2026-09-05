# Csv Utils Specification

> 1. expect fields len

<!-- sdn-diagram:id=csv_utils_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=csv_utils_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

csv_utils_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=csv_utils_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 23 | 23 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Csv Utils Specification

## Scenarios

### CSV Utilities

### CSV Parsing

#### parses simple CSV line

1. expect fields len


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fields = parse_csv_line_quoted("apple,banana,cherry")
expect fields.len() == 3
expect fields[0] == "apple"
expect fields[1] == "banana"
expect fields[2] == "cherry"
```

</details>

#### parses quoted fields

1. expect fields len


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fields = parse_csv_line_quoted("\"John Doe\",30,\"New York\"")
expect fields.len() == 3
expect fields[0] == "John Doe"
expect fields[1] == "30"
expect fields[2] == "New York"
```

</details>

#### parses comma in quoted field

1. expect fields len


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fields = parse_csv_line_quoted("\"Smith, John\",Engineer")
expect fields.len() == 2
expect fields[0] == "Smith, John"
```

</details>

#### parses multiple rows

1. expect rows len


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val text_content = "Name,Age\nAlice,30\nBob,25"
val rows = parse_csv(text_content)
expect rows.len() == 3
expect rows[0][0] == "Name"
expect rows[1][0] == "Alice"
expect rows[2][0] == "Bob"
```

</details>

#### parses with headers

1. expect data headers len
2. expect data rows len


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val text_content = "Name,Age,City\nAlice,30,NYC\nBob,25,LA"
match parse_csv_with_headers(text_content):
    case Some(data):
        expect data.headers.len() == 3
        expect data.headers[0] == "Name"
        expect data.rows.len() == 2
        expect data.rows[0][0] == "Alice"
    case nil:
        expect false
```

</details>

### CSV Formatting

#### formats simple line

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val line = format_csv_line(["apple", "banana", "cherry"])
expect line == "apple,banana,cherry"
```

</details>

#### quotes field with comma

1. expect line contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val line = format_csv_line(["Smith, John", "30"])
expect line.contains("\"Smith, John\"")
```

</details>

#### quotes field only when needed

1. expect quote csv field


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect quote_csv_field("simple") == "simple"
```

</details>

#### quotes field with comma

1. expect quoted starts with
2. expect quoted ends with


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val quoted = quote_csv_field("Smith, John")
expect quoted.starts_with("\"")
expect quoted.ends_with("\"")
```

</details>

#### formats full CSV

1. expect csv contains
2. expect csv contains
3. expect csv contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rows = [
    ["Name", "Age"],
    ["Alice", "30"],
    ["Bob", "25"]
]
val csv = format_csv(rows)
expect csv.contains("Name,Age")
expect csv.contains("Alice,30")
expect csv.contains("Bob,25")
```

</details>

### CSV Validation

#### detects rectangular CSV

1. expect is rectangular csv


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rows = [
    ["A", "B", "C"],
    ["1", "2", "3"],
    ["4", "5", "6"]
]
expect is_rectangular_csv(rows)
```

</details>

#### detects non-rectangular CSV

1. expect not is rectangular csv


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rows = [
    ["A", "B", "C"],
    ["1", "2"],
    ["4", "5", "6"]
]
expect not is_rectangular_csv(rows)
```

</details>

#### counts columns

1. expect get column count


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rows = [["A", "B", "C"]]
expect get_column_count(rows) == 3
```

</details>

#### counts rows

1. expect get row count


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rows = [["A"], ["B"], ["C"]]
expect get_row_count(rows) == 3
```

</details>

### CSV Transformation

#### gets column by index

1. expect names len


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rows = [
    ["Name", "Age"],
    ["Alice", "30"],
    ["Bob", "25"]
]
val names = get_column(rows, 0)
expect names.len() == 3
expect names[0] == "Name"
expect names[1] == "Alice"
expect names[2] == "Bob"
```

</details>

#### gets column by name

1. expect ages len


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val data = CsvData(
    headers: ["Name", "Age", "City"],
    rows: [
        ["Alice", "30", "NYC"],
        ["Bob", "25", "LA"]
    ]
)
match get_column_by_name(data, "Age"):
    case Some(ages):
        expect ages.len() == 2
        expect ages[0] == "30"
        expect ages[1] == "25"
    case nil:
        expect false
```

</details>

#### returns nil for unknown column name

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val data = CsvData(headers: ["Name", "Age"], rows: [])
match get_column_by_name(data, "Country"):
    case Some(_): expect false
    case nil: expect true
```

</details>

#### transposes CSV

1. expect transposed len


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rows = [
    ["A", "B"],
    ["1", "2"],
    ["3", "4"]
]
val transposed = transpose_csv(rows)
expect transposed.len() == 2
expect transposed[0][0] == "A"
expect transposed[0][1] == "1"
expect transposed[0][2] == "3"
```

</details>

#### filters rows

1. expect filtered rows len


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val data = CsvData(
    headers: ["Name", "Age"],
    rows: [
        ["Alice", "30"],
        ["Bob", "25"],
        ["Charlie", "35"]
    ]
)
val filtered = filter_rows(data, _1[0].starts_with("A"))
expect filtered.rows.len() == 1
expect filtered.rows[0][0] == "Alice"
```

</details>

### CSV Statistics

#### counts non-empty cells

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rows = [
    ["A", "B", ""],
    ["1", "", "3"]
]
val count = count_non_empty_cells(rows)
expect count == 4
```

</details>

#### finds max field length

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rows = [
    ["Short", "Medium text", "X"],
    ["A", "Very long text here", "Y"]
]
val max_len = max_field_length(rows)
expect max_len >= 19
```

</details>

### Table Formatting

#### formats as table

1. expect table contains
2. expect table contains
3. expect table contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rows = [
    ["Name", "Age"],
    ["Alice", "30"],
    ["Bob", "25"]
]
val table = format_csv_table(rows)
expect table.contains("Name")
expect table.contains("Alice")
expect table.contains("|")
```

</details>

#### formats table with headers

1. expect table contains
2. expect table contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val data = CsvData(
    headers: ["ID", "Name"],
    rows: [["1", "Alice"], ["2", "Bob"]]
)
val table = format_csv_table_with_headers(data)
expect table.contains("ID")
expect table.contains("---")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/tooling/csv_utils_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- CSV Utilities
- CSV Parsing
- CSV Formatting
- CSV Validation
- CSV Transformation
- CSV Statistics
- Table Formatting

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 23 |
| Active scenarios | 23 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

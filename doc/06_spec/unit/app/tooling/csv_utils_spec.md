# Csv Utils Specification

> Tests covering CSV Utilities, CSV Parsing, CSV Formatting, CSV Validation, CSV Transformation, CSV Statistics, Table Formatting.

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

- parses simple CSV line


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses simple CSV line")
val fields = parse_csv_line_quoted("apple,banana,cherry")
expect fields.len() == 3
expect fields[0] == "apple"
expect fields[1] == "banana"
expect fields[2] == "cherry"
```

</details>

#### parses quoted fields

- parses quoted fields


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses quoted fields")
val fields = parse_csv_line_quoted("\"John Doe\",30,\"New York\"")
expect fields.len() == 3
expect fields[0] == "John Doe"
expect fields[1] == "30"
expect fields[2] == "New York"
```

</details>

#### parses comma in quoted field

- parses comma in quoted field


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses comma in quoted field")
val fields = parse_csv_line_quoted("\"Smith, John\",Engineer")
expect fields.len() == 2
expect fields[0] == "Smith, John"
```

</details>

#### parses multiple rows

- parses multiple rows


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses multiple rows")
val text_content = "Name,Age\nAlice,30\nBob,25"
val rows = parse_csv(text_content)
expect rows.len() == 3
expect rows[0][0] == "Name"
expect rows[1][0] == "Alice"
expect rows[2][0] == "Bob"
```

</details>

#### parses with headers

- parses with headers


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses with headers")
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

- formats simple line


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("formats simple line")
val line = format_csv_line(["apple", "banana", "cherry"])
expect line == "apple,banana,cherry"
```

</details>

#### quotes field with comma

- quotes field with comma


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("quotes field with comma")
val line = format_csv_line(["Smith, John", "30"])
expect line.contains("\"Smith, John\"")
```

</details>

#### quotes field only when needed

- quotes field only when needed


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("quotes field only when needed")
expect quote_csv_field("simple") == "simple"
```

</details>

#### quotes field with comma

- quotes field with comma


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("quotes field with comma")
val quoted = quote_csv_field("Smith, John")
expect quoted.starts_with("\"")
expect quoted.ends_with("\"")
```

</details>

#### formats full CSV

- formats full CSV


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("formats full CSV")
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

- detects rectangular CSV


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects rectangular CSV")
val rows = [
    ["A", "B", "C"],
    ["1", "2", "3"],
    ["4", "5", "6"]
]
expect is_rectangular_csv(rows)
```

</details>

#### detects non-rectangular CSV

- detects non-rectangular CSV


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects non-rectangular CSV")
val rows = [
    ["A", "B", "C"],
    ["1", "2"],
    ["4", "5", "6"]
]
expect not is_rectangular_csv(rows)
```

</details>

#### counts columns

- counts columns


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("counts columns")
val rows = [["A", "B", "C"]]
expect get_column_count(rows) == 3
```

</details>

#### counts rows

- counts rows


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("counts rows")
val rows = [["A"], ["B"], ["C"]]
expect get_row_count(rows) == 3
```

</details>

### CSV Transformation

#### gets column by index

- gets column by index


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("gets column by index")
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

- gets column by name


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("gets column by name")
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

- returns nil for unknown column name


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns nil for unknown column name")
val data = CsvData(headers: ["Name", "Age"], rows: [])
match get_column_by_name(data, "Country"):
    case Some(_): expect false
    case nil: expect true
```

</details>

#### transposes CSV

- transposes CSV


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("transposes CSV")
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

- filters rows


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("filters rows")
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

- counts non-empty cells


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("counts non-empty cells")
val rows = [
    ["A", "B", ""],
    ["1", "", "3"]
]
val count = count_non_empty_cells(rows)
expect count == 4
```

</details>

#### finds max field length

- finds max field length


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("finds max field length")
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

- formats as table


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("formats as table")
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

- formats table with headers


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("formats table with headers")
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
| Source | `test/unit/app/tooling/csv_utils_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering CSV Utilities, CSV Parsing, CSV Formatting, CSV Validation, CSV Transformation, CSV Statistics, Table Formatting.
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `0f18fa02131cd256b3c8ba86aec4e19d35fe5cab7eb57a78c4876ab67de901b8`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `0f18fa02131cd256b3c8ba86aec4e19d35fe5cab7eb57a78c4876ab67de901b8`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `0f18fa02131cd256b3c8ba86aec4e19d35fe5cab7eb57a78c4876ab67de901b8`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/app/tooling/csv_utils_spec.spl
mirror: doc/06_spec/unit/app/tooling/csv_utils_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/tooling/csv_utils_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/tooling/csv_utils_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/tooling/csv_utils_spec.spl:208:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses simple CSV line' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/tooling/csv_utils_spec.spl:217:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses quoted fields' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/tooling/csv_utils_spec.spl:226:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses comma in quoted field' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

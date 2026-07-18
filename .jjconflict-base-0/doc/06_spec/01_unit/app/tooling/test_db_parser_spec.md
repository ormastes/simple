# Test DB Parser Specification

> Tests SDN parser robustness: field parsing, table detection. Note: Full parse_stable_db/parse_volatile_db are tested via integration (the build system) due to interpreter limitations with StringInterner mutation.

<!-- sdn-diagram:id=test_db_parser_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=test_db_parser_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

test_db_parser_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=test_db_parser_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 34 | 34 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Test DB Parser Specification

Tests SDN parser robustness: field parsing, table detection. Note: Full parse_stable_db/parse_volatile_db are tested via integration (the build system) due to interpreter limitations with StringInterner mutation.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #DB-PARSER |
| Category | Tooling |
| Status | Implemented |
| Source | `test/01_unit/app/tooling/test_db_parser_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests SDN parser robustness: field parsing, table detection.
Note: Full parse_stable_db/parse_volatile_db are tested via integration
(the build system) due to interpreter limitations with StringInterner mutation.

## Scenarios

### parse_fields

#### parses comma-separated values

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fields = parse_fields("  1, 2, 3  ")
expect(fields.len()).to_equal(3)
expect(fields[0]).to_equal("1")
expect(fields[1]).to_equal("2")
expect(fields[2]).to_equal("3")
```

</details>

#### handles quoted strings with commas

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fields = parse_fields("1, \"hello, world\", 3")
expect(fields.len()).to_equal(3)
expect(fields[1]).to_equal("hello, world")
```

</details>

#### handles escaped quotes inside strings

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fields = parse_fields("1, \"say \\\"hi\\\"\", 3")
expect(fields.len()).to_equal(3)
expect(fields[1]).to_equal("say \"hi\"")
```

</details>

#### handles empty fields

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fields = parse_fields(",, ,")
expect(fields.len()).to_equal(4)
```

</details>

#### handles single field

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fields = parse_fields("hello")
expect(fields.len()).to_equal(1)
expect(fields[0]).to_equal("hello")
```

</details>

#### trims whitespace from fields

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fields = parse_fields("  a  ,  b  ,  c  ")
expect(fields[0]).to_equal("a")
expect(fields[1]).to_equal("b")
expect(fields[2]).to_equal("c")
```

</details>

#### handles many fields

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fields = parse_fields("0, 10, 8, 2, 1, no_change, \"pass,fail\", 20.0")
expect(fields.len()).to_equal(8)
expect(fields[6]).to_equal("pass,fail")
```

</details>

#### handles empty string

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fields = parse_fields("")
expect(fields.len()).to_equal(1)
expect(fields[0]).to_equal("")
```

</details>

#### parses timing-like row with many float fields

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fields = parse_fields("0, 100.5, 95.0, 110.0, 120.0, 90.0, 130.0, 80.0, 140.0, 15.0, 98.0, 12.0, 12.2, 95.0, 10.0, 10.5, \"2026-01-01\", 10, initial")
expect(fields.len()).to_equal(19)
expect(fields[0]).to_equal("0")
expect(fields[16]).to_equal("2026-01-01")
expect(fields[18]).to_equal("initial")
```

</details>

### detect_table

#### detects strings table

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(detect_table("strings |id, value|")).to_equal("strings")
```

</details>

#### detects files table

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(detect_table("files |file_id, path_str|")).to_equal("files")
```

</details>

#### detects suites table

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(detect_table("suites |suite_id, file_id, name_str|")).to_equal("suites")
```

</details>

#### detects tests table

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(detect_table("tests |test_id, suite_id|")).to_equal("tests")
```

</details>

#### detects counters table

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(detect_table("counters |test_id|")).to_equal("counters")
```

</details>

#### detects timing table

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(detect_table("timing |test_id|")).to_equal("timing")
```

</details>

#### detects timing_runs table

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(detect_table("timing_runs |test_id|")).to_equal("timing_runs")
```

</details>

#### detects changes table

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(detect_table("changes |test_id|")).to_equal("changes")
```

</details>

#### detects test_runs table

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(detect_table("test_runs |run_id|")).to_equal("test_runs")
```

</details>

#### returns empty for non-table lines

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(detect_table("just a comment")).to_equal("")
expect(detect_table("")).to_equal("")
```

</details>

#### returns empty for comments

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(detect_table("# version: 3.0")).to_equal("")
```

</details>

#### handles indented table headers

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(detect_table("  strings |id, value|")).to_equal("strings")
```

</details>

### parse_fields edge cases

#### handles unclosed quote at end

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fields = parse_fields("a, \"unclosed")
expect(fields.len()).to_equal(2)
expect(fields[1]).to_equal("unclosed")
```

</details>

#### handles quote in middle of unquoted field

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fields = parse_fields("a, b\"c, d")
# Quote starts quoted mode, so "c, d" is one field
expect(fields.len()).to_equal(2)
```

</details>

#### handles multiple consecutive commas

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fields = parse_fields("a,,,b")
expect(fields.len()).to_equal(4)
expect(fields[0]).to_equal("a")
expect(fields[3]).to_equal("b")
```

</details>

#### handles tab characters

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fields = parse_fields("a\t,\tb")
expect(fields.len()).to_equal(2)
```

</details>

#### handles newline in unquoted field

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fields = parse_fields("a,b")
expect(fields.len()).to_equal(2)
```

</details>

#### handles long unquoted field

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val long_field = "xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx"
val fields = parse_fields(long_field)
expect(fields.len()).to_equal(1)
expect(fields[0].len()).to_equal(50)
```

</details>

#### handles mixed quoted and unquoted

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fields = parse_fields("a, \"b\", c, \"d,e\", f")
expect(fields.len()).to_equal(5)
expect(fields[3]).to_equal("d,e")
```

</details>

#### handles escaped backslash

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fields = parse_fields("\"a\\\\b\"")
expect(fields.len()).to_equal(1)
expect(fields[0]).to_equal("a\\b")
```

</details>

### detect_table edge cases

#### handles whitespace-only line

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(detect_table("   ")).to_equal("")
```

</details>

#### handles table name without pipe

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(detect_table("strings id value")).to_equal("")
```

</details>

#### handles partial table name

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(detect_table("str |id|")).to_equal("")
```

</details>

#### case sensitive table names

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(detect_table("STRINGS |id|")).to_equal("")
```

</details>

#### handles table with extra spaces

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Extra spaces break the pattern match "strings |"
expect(detect_table("strings  |id|")).to_equal("")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 34 |
| Active scenarios | 34 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

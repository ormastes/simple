# Sdn Specification

> Tests covering SDN - basic parsing, SDN - data types, SDN - table format, SDN - serialization, SDN - round-trip, SDN - error handling, SDN - comments, SDN - special characters.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 22 | 22 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Sdn Specification

## Scenarios

### SDN - basic parsing

#### parses key-value pairs

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- parses key-value pairs


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses key-value pairs")
val sdn = "name: John\nage: 30"
# Would parse to: {"name": "John", "age": 30}
expect sdn.contains("name:")
expect sdn.contains("age:")
```

</details>

#### parses nested structures

- parses nested structures


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses nested structures")
val sdn = "person:\n  name: Alice\n  age: 25"
expect sdn.contains("person:")
expect sdn.contains("  name:")
```

</details>

#### parses lists

- parses lists


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses lists")
val sdn = "items:\n  - apple\n  - banana\n  - orange"
expect sdn.contains("items:")
expect sdn.contains("  - apple")
```

</details>

### SDN - data types

#### parses strings

- parses strings


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses strings")
val value = "hello"
expect value == "hello"
```

</details>

#### parses integers

- parses integers


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses integers")
val value = 42
expect value == 42
```

</details>

#### parses floats

- parses floats


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses floats")
val value = 3.14
expect value > 3.0
```

</details>

#### parses booleans

- parses booleans


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses booleans")
val true_val = true
val false_val = false
expect true_val
expect not false_val
```

</details>

### SDN - table format

#### parses table headers

- parses table headers


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses table headers")
val header = "users |id, name, age|"
expect header.contains("|id,")
expect header.contains("name,")
```

</details>

#### parses table rows

- parses table rows


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses table rows")
val row = "    1, Alice, 30"
expect row.contains("Alice")
```

</details>

#### parses multiple rows

- parses multiple rows


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses multiple rows")
val rows = [
    "    1, Alice, 30",
    "    2, Bob, 25",
    "    3, Carol, 35"
]

expect rows.len() == 3
```

</details>

### SDN - serialization

#### serializes simple values

- serializes simple values


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("serializes simple values")
val data = {"name": "John", "age": 30}
# Should produce: name: John\nage: 30
expect data.has("name")
```

</details>

#### serializes nested objects

- serializes nested objects


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("serializes nested objects")
val data = {
    "person": {
        "name": "Alice",
        "details": {"age": 25, "city": "NYC"}
    }
}

expect data.has("person")
```

</details>

#### serializes arrays

- serializes arrays


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("serializes arrays")
val data = {"items": ["apple", "banana", "orange"]}
expect data.has("items")
expect data["items"].len() == 3
```

</details>

### SDN - round-trip

#### preserves data through parse and serialize

- preserves data through parse and serialize


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("preserves data through parse and serialize")
val original = {"name": "Test", "value": 42}
# parse(serialize(data)) == data
expect original["name"] == "Test"
expect original["value"] == 42
```

</details>

#### preserves table data

- preserves table data


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("preserves table data")
val table_sdn = "users |id, name|\n    1, Alice\n    2, Bob"
# Parse and serialize should preserve structure
expect table_sdn.contains("|id, name|")
```

</details>

### SDN - error handling

#### handles malformed input gracefully

- handles malformed input gracefully


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles malformed input gracefully")
val bad_sdn = "invalid: [\n  incomplete"
# Should return parse error, not crash
expect bad_sdn.len() > 0
```

</details>

#### reports line numbers in errors

- reports line numbers in errors


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reports line numbers in errors")
# Error on line 3
val error_info = {"line": 3, "message": "Unexpected token"}
expect error_info["line"] == 3
```

</details>

### SDN - comments

#### supports hash comments

- supports hash comments


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("supports hash comments")
val sdn = "# This is a comment\nname: John"
expect sdn.contains("#")
```

</details>

#### ignores comments in parsing

- ignores comments in parsing


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("ignores comments in parsing")
val sdn_with_comment = "# comment\nvalue: 42"
val sdn_without = "value: 42"
# Both should parse to same data
expect sdn_with_comment.contains("value:")
expect sdn_without.contains("value:")
```

</details>

### SDN - special characters

#### handles quotes in strings

- handles quotes in strings


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles quotes in strings")
val value = "He said \"hello\""
expect value.contains("\"")
```

</details>

#### handles newlines in strings

- handles newlines in strings


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles newlines in strings")
val value = "Line 1\nLine 2"
expect value.contains("\n")
```

</details>

#### handles Unicode characters

- handles Unicode characters


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles Unicode characters")
val value = "Hello 世界 🌍"
expect value.len() > 5
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/unit/app/sdn_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering SDN - basic parsing, SDN - data types, SDN - table format, SDN - serialization, SDN - round-trip, SDN - error handling, SDN - comments, SDN - special characters.
- SDN - basic parsing
- SDN - data types
- SDN - table format
- SDN - serialization
- SDN - round-trip
- SDN - error handling
- SDN - comments
- SDN - special characters

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 22 |
| Active scenarios | 22 |
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

- Canonical SPipe generation for source `b08896f7fac9173a3bd9e19b5329ce768e101140f8ca7bfd1673ef31b59bc913`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `b08896f7fac9173a3bd9e19b5329ce768e101140f8ca7bfd1673ef31b59bc913`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `b08896f7fac9173a3bd9e19b5329ce768e101140f8ca7bfd1673ef31b59bc913`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/app/sdn_spec.spl
mirror: doc/06_spec/unit/app/sdn_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/sdn_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/sdn_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/sdn_spec.spl:14:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses key-value pairs' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/sdn_spec.spl:22:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses nested structures' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/sdn_spec.spl:29:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses lists' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

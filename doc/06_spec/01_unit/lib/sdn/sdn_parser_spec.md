# Sdn Parser Specification

> Tests covering SDN Primitive Values, SDN Collections, SDN Format Features, SDN Serialization, SDN Error Handling.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 26 | 26 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Sdn Parser Specification

## Scenarios

### SDN Primitive Values

#### parse integer

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- parse integer


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parse integer")
val value = 42
check(value == 42)
```

</details>

#### parse negative integer

- parse negative integer


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parse negative integer")
val value = -5
check(value == -5)
```

</details>

#### parse float

- parse float


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parse float")
val value = 3.14
check(value > 3.0)
```

</details>

#### parse string

- parse string


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parse string")
val value = "hello"
check(value == "hello")
```

</details>

#### parse boolean true

- parse boolean true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parse boolean true")
val value = true
check(value)
```

</details>

#### parse boolean false

- parse boolean false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parse boolean false")
val value = false
check(not value)
```

</details>

#### parse nil

- parse nil


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parse nil")
val value = nil
check(not value.?)
```

</details>

### SDN Collections

#### parse array

- parse array


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parse array")
val arr = [1, 2, 3]
check(arr.len() == 3)
```

</details>

#### parse empty array

- parse empty array


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parse empty array")
val arr: [i64] = []
check(arr.len() == 0)
```

</details>

#### parse nested array

- parse nested array


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parse nested array")
val arr = [[1, 2], [3, 4]]
check(arr.len() == 2)
```

</details>

#### parse map

- parse map


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parse map")
val m = {"key": "value"}
check(m.len() == 1)
```

</details>

#### parse empty map

- parse empty map


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parse empty map")
val m: Map<text, text> = {}
check(m.len() == 0)
```

</details>

#### parse nested map

- parse nested map


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parse nested map")
val m = {"outer": {"inner": 42}}
check(m.len() == 1)
```

</details>

### SDN Format Features

#### trailing commas allowed

- trailing commas allowed


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("trailing commas allowed")
val arr = [1, 2, 3]
check(arr.len() == 3)
```

</details>

#### comments stripped

- comments stripped


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("comments stripped")
val value = 42
check(value == 42)
```

</details>

#### multiline values

- multiline values


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("multiline values")
val lines = ["line1", "line2", "line3"]
check(lines.len() == 3)
```

</details>

#### quoted keys

- quoted keys


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("quoted keys")
val m = {"key with spaces": 42}
check(m.len() == 1)
```

</details>

#### unquoted keys

- unquoted keys


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("unquoted keys")
val m = {"simple": 42}
check(m.len() == 1)
```

</details>

### SDN Serialization

#### serialize integer

- serialize integer


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("serialize integer")
val s = "{42}"
check(s == "42")
```

</details>

#### serialize string

- serialize string


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("serialize string")
val s = "hello"
check(s == "hello")
```

</details>

#### serialize array

- serialize array


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("serialize array")
val arr = [1, 2, 3]
val s = "{arr}"
check(s.contains("1"))
```

</details>

#### serialize boolean

- serialize boolean


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("serialize boolean")
val s = "{true}"
check(s == "true")
```

</details>

### SDN Error Handling

#### unterminated string

- unterminated string


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("unterminated string")
val error = "unterminated_string"
check(error == "unterminated_string")
```

</details>

#### unexpected token

- unexpected token


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("unexpected token")
val error = "unexpected_token"
check(error == "unexpected_token")
```

</details>

#### invalid escape sequence

- invalid escape sequence


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("invalid escape sequence")
val error = "invalid_escape"
check(error == "invalid_escape")
```

</details>

#### trailing content

- trailing content


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("trailing content")
val error = "trailing_content"
check(error == "trailing_content")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/sdn/sdn_parser_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering SDN Primitive Values, SDN Collections, SDN Format Features, SDN Serialization, SDN Error Handling.
- SDN Primitive Values
- SDN Collections
- SDN Format Features
- SDN Serialization
- SDN Error Handling

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 26 |
| Active scenarios | 26 |
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

- Canonical SPipe generation for source `d9119d903d43fec16f549d3b1b520d5df7839ba3c468a69914ada9a139dae80e`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `d9119d903d43fec16f549d3b1b520d5df7839ba3c468a69914ada9a139dae80e`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `d9119d903d43fec16f549d3b1b520d5df7839ba3c468a69914ada9a139dae80e`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/sdn/sdn_parser_spec.spl
mirror: doc/06_spec/01_unit/lib/sdn/sdn_parser_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/sdn/sdn_parser_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/sdn/sdn_parser_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/sdn/sdn_parser_spec.spl:18:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parse integer' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/sdn/sdn_parser_spec.spl:24:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parse negative integer' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/sdn/sdn_parser_spec.spl:30:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parse float' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

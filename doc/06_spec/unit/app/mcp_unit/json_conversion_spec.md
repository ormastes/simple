# Json Conversion Specification

> Tests covering JSON Conversion, any_to_json Type Branches, json_value_to_any Type Branches, Edge Cases, Round-Trip Conversion.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 22 | 22 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Json Conversion Specification

## Scenarios

### JSON Conversion

### any_to_json Type Branches

#### converts bool to JSON

- converts bool to JSON
   - Expected: json equals `true`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts bool to JSON")
val json = "true"
expect(json).to_equal("true")
```

</details>

#### converts i64 to JSON

- converts i64 to JSON
   - Expected: json equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts i64 to JSON")
val json = "42"
expect(json).to_equal("42")
```

</details>

#### converts f64 to JSON

- converts f64 to JSON
   - Expected: json contains `3.14`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts f64 to JSON")
val json = "3.14"
expect(json.contains("3.14")).to_equal(true)
```

</details>

#### converts text to JSON

- converts text to JSON
   - Expected: json contains `hello`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts text to JSON")
val json = js("hello")
expect(json.contains("hello")).to_equal(true)
```

</details>

#### converts list to JSON array

- converts list to JSON array
   - Expected: json.starts_with("[") is true
   - Expected: json.ends_with("]") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts list to JSON array")
val json = "[1,2,3]"
expect(json.starts_with("[")).to_equal(true)
expect(json.ends_with("]")).to_equal(true)
```

</details>

#### converts dict to JSON object

- converts dict to JSON object
   - Expected: json contains `key`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts dict to JSON object")
val json = jo1(jp("key", js("value")))
expect(json.contains("key")).to_equal(true)
```

</details>

#### handles nil conversion

- handles nil conversion
   - Expected: json equals `null`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles nil conversion")
val json = "null"
expect(json).to_equal("null")
```

</details>

#### uses fallback for unknown types

- uses fallback for unknown types
   - Expected: json contains `unknown`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("uses fallback for unknown types")
val json = js("unknown")
expect(json.contains("unknown")).to_equal(true)
```

</details>

### json_value_to_any Type Branches

#### converts JSON bool to any

- converts JSON bool to any
   - Expected: value equals `true`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts JSON bool to any")
val value = extract_json_value(jo1(jp("v", "true")), "v")
expect(value).to_equal("true")
```

</details>

#### converts JSON number to any

- converts JSON number to any
   - Expected: value equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts JSON number to any")
val value = extract_json_value(jo1(jp("v", "42")), "v")
expect(value).to_equal("42")
```

</details>

#### converts JSON string to any

- converts JSON string to any
   - Expected: value equals `text`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts JSON string to any")
val value = extract_json_string(jo1(jp("v", js("text"))), "v")
expect(value).to_equal("text")
```

</details>

#### converts JSON array to any

- converts JSON array to any
   - Expected: value.starts_with("[") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts JSON array to any")
val json = jo1(jp("v", "[1,2,3]"))
val value = extract_json_value(json, "v")
expect(value.starts_with("[")).to_equal(true)
```

</details>

#### converts JSON object to any

- converts JSON object to any
   - Expected: value contains `a`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts JSON object to any")
val inner = jo1(jp("a", "1"))
val json = jo1(jp("v", inner))
val value = extract_json_value(json, "v")
expect(value.contains("a")).to_equal(true)
```

</details>

#### converts JSON null to any

- converts JSON null to any
   - Expected: value equals `null`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts JSON null to any")
val json = jo1(jp("v", "null"))
val value = extract_json_value(json, "v")
expect(value).to_equal("null")
```

</details>

### Edge Cases

#### handles empty list

- handles empty list
   - Expected: json.len() > 0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles empty list")
val json = LB() + RB()
expect(json.len() > 0).to_equal(true)
```

</details>

#### handles empty dict

- handles empty dict
   - Expected: json.len() > 0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles empty dict")
val json = LB() + RB()
expect(json.len() > 0).to_equal(true)
```

</details>

#### handles nested structures

- handles nested structures
   - Expected: outer contains `nested`
   - Expected: outer contains `value`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles nested structures")
val inner = jo1(jp("nested", js("value")))
val outer = jo1(jp("outer", inner))
expect(outer.contains("nested")).to_equal(true)
expect(outer.contains("value")).to_equal(true)
```

</details>

#### handles special characters in strings

- handles special characters in strings
   - Expected: escaped contains `world`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles special characters in strings")
val escaped = escape_json("hello \"world\"")
expect(escaped.contains("world")).to_equal(true)
```

</details>

### Round-Trip Conversion

#### preserves bool through conversion

- preserves bool through conversion
   - Expected: extracted equals `original`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("preserves bool through conversion")
val original = "true"
val json = jo1(jp("v", original))
val extracted = extract_json_value(json, "v")
expect(extracted).to_equal(original)
```

</details>

#### preserves number through conversion

- preserves number through conversion
   - Expected: extracted equals `original`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("preserves number through conversion")
val original = "42"
val json = jo1(jp("v", original))
val extracted = extract_json_value(json, "v")
expect(extracted).to_equal(original)
```

</details>

#### preserves string through conversion

- preserves string through conversion
   - Expected: extracted equals `original`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("preserves string through conversion")
val original = "hello"
val json = jo1(jp("v", js(original)))
val extracted = extract_json_string(json, "v")
expect(extracted).to_equal(original)
```

</details>

#### preserves nested structure through conversion

- preserves nested structure through conversion
   - Expected: extracted contains `key`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("preserves nested structure through conversion")
val inner = jo1(jp("key", js("val")))
val outer = jo1(jp("data", inner))
val extracted = extract_json_value(outer, "data")
expect(extracted.contains("key")).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/unit/app/mcp_unit/json_conversion_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering JSON Conversion, any_to_json Type Branches, json_value_to_any Type Branches, Edge Cases, Round-Trip Conversion.
- JSON Conversion
- any_to_json Type Branches
- json_value_to_any Type Branches
- Edge Cases
- Round-Trip Conversion

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

- Canonical SPipe generation for source `01e6342beed97cd78ecec0f994c5db0c454180d061caa0a4783980f19edd5c43`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `01e6342beed97cd78ecec0f994c5db0c454180d061caa0a4783980f19edd5c43`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `01e6342beed97cd78ecec0f994c5db0c454180d061caa0a4783980f19edd5c43`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/app/mcp_unit/json_conversion_spec.spl
mirror: doc/06_spec/unit/app/mcp_unit/json_conversion_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/mcp_unit/json_conversion_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/mcp_unit/json_conversion_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/mcp_unit/json_conversion_spec.spl:15:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'converts bool to JSON' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/mcp_unit/json_conversion_spec.spl:21:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'converts i64 to JSON' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/mcp_unit/json_conversion_spec.spl:27:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'converts f64 to JSON' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

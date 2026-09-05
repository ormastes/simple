# Mcp Json Parser Specification

> Tests covering JSON String Extraction, JSON Value Extraction, Nested JSON Extraction, JSON Parser Edge Cases, JSON Builder Round-Trip.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 20 | 20 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Mcp Json Parser Specification

## Scenarios

### JSON String Extraction

#### when extracting simple string values

#### extracts method from JSON-RPC request

- extracts method from JSON-RPC request
   - Expected: method equals `initialize`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("extracts method from JSON-RPC request")
val json = jo3(jp("jsonrpc", js("2.0")), jp("id", js("1")), jp("method", js("initialize")))
val method = extract_json_string(json, "method")
expect(method).to_equal("initialize")
```

</details>

#### extracts jsonrpc version

- extracts jsonrpc version
   - Expected: version equals `2.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("extracts jsonrpc version")
val json = jo2(jp("jsonrpc", js("2.0")), jp("id", js("1")))
val version = extract_json_string(json, "jsonrpc")
expect(version).to_equal("2.0")
```

</details>

#### returns empty string for missing key

- returns empty string for missing key
   - Expected: missing equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns empty string for missing key")
val json = jo1(jp("jsonrpc", js("2.0")))
val missing = extract_json_string(json, "nonexistent")
expect(missing).to_equal("")
```

</details>

#### when handling special characters

#### handles strings with slashes

- handles strings with slashes
   - Expected: path equals `src/app/mcp/main.spl`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles strings with slashes")
val json = jo1(jp("path", js("src/app/mcp/main.spl")))
val path = extract_json_string(json, "path")
expect(path).to_contain("/")
expect(path).to_equal("src/app/mcp/main.spl")
```

</details>

#### handles empty string values

- handles empty string values
   - Expected: empty equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles empty string values")
val json = jo1(jp("empty", js("")))
val empty = extract_json_string(json, "empty")
expect(empty).to_equal("")
```

</details>

### JSON Value Extraction

#### when extracting numeric values

#### extracts numeric ID

- extracts numeric ID
   - Expected: id equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("extracts numeric ID")
val json = jo2(jp("jsonrpc", js("2.0")), jp("id", "42"))
val id = extract_json_value(json, "id")
expect(id).to_equal("42")
```

</details>

#### extracts boolean-like values

- extracts boolean-like values
   - Expected: value equals `true`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("extracts boolean-like values")
val json = jo1(jp("isError", "true"))
val value = extract_json_value(json, "isError")
expect(value).to_equal("true")
```

</details>

#### when extracting object values

#### stops at comma delimiter

- stops at comma delimiter
   - Expected: id equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("stops at comma delimiter")
val json = jo2(jp("id", "1"), jp("method", js("test")))
val id = extract_json_value(json, "id")
expect(id).to_equal("1")
```

</details>

#### returns null for missing key

- returns null for missing key
   - Expected: missing equals `null`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns null for missing key")
val json = jo1(jp("method", js("test")))
val missing = extract_json_value(json, "nonexistent")
expect(missing).to_equal("null")
```

</details>

### Nested JSON Extraction

#### when accessing nested objects

#### extracts nested string value

- extracts nested string value
   - Expected: name equals `read_code`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("extracts nested string value")
val inner = jo1(jp("name", js("read_code")))
val json = jo1(jp("params", inner))
val name = extract_nested_string(json, "params", "name")
expect(name).to_equal("read_code")
```

</details>

#### extracts nested path

- extracts nested path


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("extracts nested path")
val inner = jo1(jp("uri", js("file:///path/to/file.spl")))
val json = jo1(jp("params", inner))
val uri = extract_nested_string(json, "params", "uri")
expect(uri).to_contain("file://")
```

</details>

#### returns empty for missing nested key

- returns empty for missing nested key
   - Expected: missing equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns empty for missing nested key")
val json = jo1(jp("params", LB() + RB()))
val missing = extract_nested_string(json, "params", "nonexistent")
expect(missing).to_equal("")
```

</details>

### JSON Parser Edge Cases

#### when handling escape characters

#### escapes newlines

- escapes newlines
   - Expected: escaped does not contain `NL`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("escapes newlines")
val escaped = escape_json("line1{NL}line2")
expect(escaped.contains(NL)).to_equal(false)
```

</details>

#### escapes tabs

- escapes tabs
   - Expected: escaped does not contain `\t`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("escapes tabs")
val escaped = escape_json("col1\tcol2")
expect(escaped.contains("\t")).to_equal(false)
```

</details>

#### preserves normal strings

- preserves normal strings
   - Expected: escaped equals `hello world`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("preserves normal strings")
val escaped = escape_json("hello world")
expect(escaped).to_equal("hello world")
```

</details>

#### handles empty string

- handles empty string
   - Expected: escaped equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles empty string")
val escaped = escape_json("")
expect(escaped).to_equal("")
```

</details>

#### when building search patterns

#### builds quoted key pattern

- builds quoted key pattern
   - Expected: pattern contains `method`
   - Expected: pattern contains `:`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("builds quoted key pattern")
val key = "method"
val pattern = Q() + key + Q() + ":"
expect(pattern.contains("method")).to_equal(true)
expect(pattern.contains(":")).to_equal(true)
```

</details>

### JSON Builder Round-Trip

#### when building and extracting

#### round-trips string values

- round-trips string values
   - Expected: extracted equals `Alice`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("round-trips string values")
val json = jo1(jp("name", js("Alice")))
val extracted = extract_json_string(json, "name")
expect(extracted).to_equal("Alice")
```

</details>

#### round-trips nested values

- round-trips nested values
   - Expected: file equals `test.spl`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("round-trips nested values")
val inner = jo2(jp("file", js("test.spl")), jp("line", "42"))
val json = jo1(jp("params", inner))
val file = extract_nested_string(json, "params", "file")
expect(file).to_equal("test.spl")
```

</details>

#### round-trips multiple fields

- round-trips multiple fields
   - Expected: extract_json_string(json, "a") equals `1`
   - Expected: extract_json_string(json, "b") equals `2`
   - Expected: extract_json_string(json, "c") equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("round-trips multiple fields")
val json = jo3(jp("a", js("1")), jp("b", js("2")), jp("c", js("3")))
expect(extract_json_string(json, "a")).to_equal("1")
expect(extract_json_string(json, "b")).to_equal("2")
expect(extract_json_string(json, "c")).to_equal("3")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/unit/app/mcp_unit/mcp_json_parser_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering JSON String Extraction, JSON Value Extraction, Nested JSON Extraction, JSON Parser Edge Cases, JSON Builder Round-Trip.
- JSON String Extraction
- JSON Value Extraction
- Nested JSON Extraction
- JSON Parser Edge Cases
- JSON Builder Round-Trip

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 20 |
| Active scenarios | 20 |
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

- Canonical SPipe generation for source `a5199799eb0f9ff887d679b2dc7c3537a77e17624fd19a136dac425b6aff0c76`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `a5199799eb0f9ff887d679b2dc7c3537a77e17624fd19a136dac425b6aff0c76`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `a5199799eb0f9ff887d679b2dc7c3537a77e17624fd19a136dac425b6aff0c76`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/app/mcp_unit/mcp_json_parser_spec.spl
mirror: doc/06_spec/unit/app/mcp_unit/mcp_json_parser_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/mcp_unit/mcp_json_parser_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/mcp_unit/mcp_json_parser_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/mcp_unit/mcp_json_parser_spec.spl:18:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'extracts method from JSON-RPC request' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/mcp_unit/mcp_json_parser_spec.spl:25:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'extracts jsonrpc version' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/mcp_unit/mcp_json_parser_spec.spl:32:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns empty string for missing key' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

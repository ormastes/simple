# Lsp Json Specification

> Tests covering LSP JSON helpers, escape_json, extract_field, extract_id, extract_nested, make_json_result, JSON builders.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 13 | 13 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Lsp Json Specification

## Scenarios

### LSP JSON helpers

### escape_json

#### escapes quotes

- escapes quotes


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("escapes quotes")
val result = escape_json("hello \"world\"")
expect(result).to_contain("\\\"")
```

</details>

#### escapes newlines

- escapes newlines


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("escapes newlines")
val result = escape_json("line1\nline2")
expect(result).to_contain("\\n")
```

</details>

#### passes through plain text

- passes through plain text
   - Expected: result equals `hello world`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("passes through plain text")
val result = escape_json("hello world")
expect(result).to_equal("hello world")
```

</details>

### extract_field

#### extracts string field

- extracts string field
   - Expected: result equals `Alice`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("extracts string field")
val json = "{\"name\":\"Alice\",\"age\":30}"
val result = extract_field(json, "name")
expect(result).to_equal("Alice")
```

</details>

#### extracts numeric field

- extracts numeric field
   - Expected: result equals `30`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("extracts numeric field")
val json = "{\"name\":\"Alice\",\"age\":30}"
val result = extract_field(json, "age")
expect(result).to_equal("30")
```

</details>

#### returns empty for missing field

- returns empty for missing field
   - Expected: result equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns empty for missing field")
val json = "{\"name\":\"Alice\"}"
val result = extract_field(json, "missing")
expect(result).to_equal("")
```

</details>

### extract_id

#### extracts numeric id

- extracts numeric id
   - Expected: result equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("extracts numeric id")
val json = "{\"jsonrpc\":\"2.0\",\"id\":42,\"method\":\"initialize\"}"
val result = extract_id(json)
expect(result).to_equal("42")
```

</details>

#### extracts string id

- extracts string id
   - Expected: result equals `"abc"`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("extracts string id")
val json = "{\"jsonrpc\":\"2.0\",\"id\":\"abc\",\"method\":\"test\"}"
val result = extract_id(json)
expect(result).to_equal("\"abc\"")
```

</details>

### extract_nested

#### extracts field from params

- extracts field from params
   - Expected: result equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("extracts field from params")
val json = "{\"method\":\"hover\",\"params\":{\"textDocument\":{\"uri\":\"file:///test.spl\"},\"position\":{\"line\":5}}}"
val result = extract_nested(json, "line")
expect(result).to_equal("5")
```

</details>

### make_json_result

#### creates valid JSON-RPC response

- creates valid JSON-RPC response


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates valid JSON-RPC response")
val result = make_json_result("1", "null")
expect(result).to_contain("jsonrpc")
expect(result).to_contain("2.0")
expect(result).to_contain("\"id\":1")
expect(result).to_contain("\"result\":null")
```

</details>

### JSON builders

#### js wraps in quotes

- js wraps in quotes
   - Expected: result equals `"hello"`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("js wraps in quotes")
val result = js("hello")
expect(result).to_equal("\"hello\"")
```

</details>

#### jp creates key-value pair

- jp creates key-value pair
   - Expected: result equals `"name":"Alice"`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("jp creates key-value pair")
val result = jp("name", js("Alice"))
expect(result).to_equal("\"name\":\"Alice\"")
```

</details>

#### jo1 wraps single property

- jo1 wraps single property
   - Expected: result equals `{"x":1}`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("jo1 wraps single property")
val result = jo1(jp("x", "1"))
expect(result).to_equal("{\"x\":1}")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/unit/app/lsp_json_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering LSP JSON helpers, escape_json, extract_field, extract_id, extract_nested, make_json_result, JSON builders.
- LSP JSON helpers
- escape_json
- extract_field
- extract_id
- extract_nested
- make_json_result
- JSON builders

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 13 |
| Active scenarios | 13 |
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

- Canonical SPipe generation for source `730c53d24d07b4da26b95e242242eb454e913af1fbae1d3108f5bbdd8a594719`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `730c53d24d07b4da26b95e242242eb454e913af1fbae1d3108f5bbdd8a594719`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `730c53d24d07b4da26b95e242242eb454e913af1fbae1d3108f5bbdd8a594719`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/app/lsp_json_spec.spl
mirror: doc/06_spec/unit/app/lsp_json_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/lsp_json_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/lsp_json_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/lsp_json_spec.spl:14:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'escapes quotes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/lsp_json_spec.spl:20:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'escapes newlines' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/lsp_json_spec.spl:26:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'passes through plain text' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

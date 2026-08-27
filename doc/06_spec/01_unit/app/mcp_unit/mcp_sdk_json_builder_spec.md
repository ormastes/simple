# Mcp Sdk Json Builder Specification

> Tests covering jo1-jo5 output structure (main_lazy_json), escape_json round-trips via js/extract_json_string, first_n_chars uses native substring, _char_at guards invalid indexes, make_tool_result and make_tool_error JSON structure, JSON-RPC builders (mcp_sdk.core.jsonrpc, rewritten).

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 26 | 26 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Mcp Sdk Json Builder Specification

## Scenarios

### jo1-jo5 output structure (main_lazy_json)

#### jo1 produces well-formed single-pair object

#### wraps pair in braces

- wraps pair in braces
   - Expected: got equals `LB() + pair + RB()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("wraps pair in braces")
val pair = jp("k", js("v"))
val got = jo1(pair)
expect(got).to_equal(LB() + pair + RB())
```

</details>

#### round-trips string field via extract_json_string

- round-trips string field via extract_json_string
   - Expected: extracted equals `alice`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("round-trips string field via extract_json_string")
val built = jo1(jp("name", js("alice")))
val extracted = extract_json_string(built, "name")
expect(extracted).to_equal("alice")
```

</details>

#### jo2 places comma between pairs

#### produces correct structure

- produces correct structure
   - Expected: got equals `LB() + p1 + "," + p2 + RB()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("produces correct structure")
val p1 = jp("a", js("1"))
val p2 = jp("b", js("2"))
val got = jo2(p1, p2)
expect(got).to_equal(LB() + p1 + "," + p2 + RB())
```

</details>

#### round-trips both fields

- round-trips both fields
   - Expected: extract_json_string(built, "x") equals `foo`
   - Expected: extract_json_string(built, "y") equals `bar`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("round-trips both fields")
val built = jo2(jp("x", js("foo")), jp("y", js("bar")))
expect(extract_json_string(built, "x")).to_equal("foo")
expect(extract_json_string(built, "y")).to_equal("bar")
```

</details>

#### jo3 round-trips three fields

#### all three fields extractable

- all three fields extractable
   - Expected: extract_json_string(built, "a") equals `1`
   - Expected: extract_json_string(built, "b") equals `2`
   - Expected: extract_json_string(built, "c") equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("all three fields extractable")
val built = jo3(jp("a", js("1")), jp("b", js("2")), jp("c", js("3")))
expect(extract_json_string(built, "a")).to_equal("1")
expect(extract_json_string(built, "b")).to_equal("2")
expect(extract_json_string(built, "c")).to_equal("3")
```

</details>

#### jo4 round-trips four fields

#### all four fields extractable

- all four fields extractable
   - Expected: extract_json_string(built, "w") equals `1`
   - Expected: extract_json_string(built, "x") equals `2`
   - Expected: extract_json_string(built, "y") equals `3`
   - Expected: extract_json_string(built, "z") equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("all four fields extractable")
val built = jo4(jp("w", js("1")), jp("x", js("2")), jp("y", js("3")), jp("z", js("4")))
expect(extract_json_string(built, "w")).to_equal("1")
expect(extract_json_string(built, "x")).to_equal("2")
expect(extract_json_string(built, "y")).to_equal("3")
expect(extract_json_string(built, "z")).to_equal("4")
```

</details>

### escape_json round-trips via js/extract_json_string

#### special characters survive encode-decode

#### encodes newline in escaped JSON form

- encodes newline in escaped JSON form
   - Expected: got does not contain `\n`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("encodes newline in escaped JSON form")
# extract_json_string returns the raw JSON-escaped form (no unescape step);
# verify the encoded form is present and newlines are eliminated.
val raw = "line1\nline2"
val built = jo1(jp("body", js(raw)))
val got = extract_json_string(built, "body")
# The extracted value is the JSON-escaped content (backslash-n, not real newline)
expect(got.contains("\n")).to_equal(false)
```

</details>

#### encodes tab in escaped JSON form

- encodes tab in escaped JSON form
   - Expected: got does not contain `\t`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("encodes tab in escaped JSON form")
val raw = "col1\tcol2"
val built = jo1(jp("tsv", js(raw)))
val got = extract_json_string(built, "tsv")
expect(got.contains("\t")).to_equal(false)
```

</details>

#### escape_json removes raw newlines

- escape_json removes raw newlines
   - Expected: escaped does not contain `\n`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("escape_json removes raw newlines")
val escaped = escape_json("a\nb")
expect(escaped.contains("\n")).to_equal(false)
```

</details>

#### escape_json removes raw tabs

- escape_json removes raw tabs
   - Expected: escaped does not contain `\t`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("escape_json removes raw tabs")
val escaped = escape_json("a\tb")
expect(escaped.contains("\t")).to_equal(false)
```

</details>

#### escape_json preserves plain strings

- escape_json preserves plain strings
   - Expected: escaped equals `hello world`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("escape_json preserves plain strings")
val escaped = escape_json("hello world")
expect(escaped).to_equal("hello world")
```

</details>

### first_n_chars uses native substring

#### boundary cases

#### returns first n chars

- returns first n chars
   - Expected: first_n_chars("hello", 3) equals `hel`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns first n chars")
expect(first_n_chars("hello", 3)).to_equal("hel")
```

</details>

#### returns whole string when n >= len

- returns whole string when n >= len
   - Expected: first_n_chars("abc", 10) equals `abc`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns whole string when n >= len")
expect(first_n_chars("abc", 10)).to_equal("abc")
```

</details>

#### returns empty string for n=0

- returns empty string for n=0
   - Expected: first_n_chars("hello", 0) equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns empty string for n=0")
expect(first_n_chars("hello", 0)).to_equal("")
```

</details>

#### handles single-char string

- handles single-char string
   - Expected: first_n_chars("x", 1) equals `x`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles single-char string")
expect(first_n_chars("x", 1)).to_equal("x")
```

</details>

### _char_at guards invalid indexes

#### returns empty text for negative index

- returns empty text for negative index
   - Expected: _char_at("abc", -1) equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns empty text for negative index")
expect(_char_at("abc", -1)).to_equal("")
```

</details>

#### returns empty text for past-end index

- returns empty text for past-end index
   - Expected: _char_at("abc", 3) equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns empty text for past-end index")
expect(_char_at("abc", 3)).to_equal("")
```

</details>

### make_tool_result and make_tool_error JSON structure

#### make_tool_result output shape

#### contains content key

- contains content key
   - Expected: r contains `content`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("contains content key")
val r = make_tool_result("1", "hello world")
expect(r.contains("content")).to_equal(true)
```

</details>

#### contains structuredContent key

- contains structuredContent key
   - Expected: r contains `structuredContent`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("contains structuredContent key")
val r = make_tool_result("1", "hello world")
expect(r.contains("structuredContent")).to_equal(true)
```

</details>

#### is well-formed JSON object

- is well-formed JSON object
   - Expected: r.starts_with(LB()) is true
   - Expected: r.ends_with(RB()) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("is well-formed JSON object")
val r = make_tool_result("2", "data")
expect(r.starts_with(LB())).to_equal(true)
expect(r.ends_with(RB())).to_equal(true)
```

</details>

#### make_tool_error output shape

#### contains isError

- contains isError
   - Expected: r contains `isError`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("contains isError")
val r = make_tool_error("1", -1, "boom")
expect(r.contains("isError")).to_equal(true)
```

</details>

#### isError value is true

- isError value is true
   - Expected: r contains `true`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("isError value is true")
val r = make_tool_error("1", -1, "boom")
expect(r.contains("true")).to_equal(true)
```

</details>

#### contains the error message text

- contains the error message text
   - Expected: r contains `something went wrong`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("contains the error message text")
val r = make_tool_error("1", -1, "something went wrong")
expect(r.contains("something went wrong")).to_equal(true)
```

</details>

### JSON-RPC builders (mcp_sdk.core.jsonrpc, rewritten)

#### jsonrpc_request builds the exact envelope

- jsonrpc_request builds the exact envelope
   - Expected: r contains `interior`
   - Expected: r.len() equals `interior.len() + 2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("jsonrpc_request builds the exact envelope")
val r = jsonrpc_request("7", "tools/list", "42")
val interior = "\"jsonrpc\":\"2.0\",\"id\":7,\"method\":\"tools/list\",\"params\":42"
expect(r.contains(interior)).to_equal(true)
expect(r.len()).to_equal(interior.len() + 2)
```

</details>

#### jsonrpc_notification builds the exact envelope

- jsonrpc_notification builds the exact envelope
   - Expected: r contains `interior`
   - Expected: r.len() equals `interior.len() + 2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("jsonrpc_notification builds the exact envelope")
val r = jsonrpc_notification("initialized", "1")
val interior = "\"jsonrpc\":\"2.0\",\"method\":\"initialized\",\"params\":1"
expect(r.contains(interior)).to_equal(true)
expect(r.len()).to_equal(interior.len() + 2)
```

</details>

#### jsonrpc_error_with_data nests the error object exactly

- jsonrpc_error_with_data nests the error object exactly
   - Expected: r contains `head_interior`
   - Expected: r contains `err_interior`
   - Expected: r.len() equals `head_interior.len() + err_interior.len() + 4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("jsonrpc_error_with_data nests the error object exactly")
val r = jsonrpc_error_with_data("3", -32600, "bad request", "9")
val head_interior = "\"jsonrpc\":\"2.0\",\"id\":3,\"error\":"
val err_interior = "\"code\":-32600,\"message\":\"bad request\",\"data\":9"
expect(r.contains(head_interior)).to_equal(true)
expect(r.contains(err_interior)).to_equal(true)
expect(r.len()).to_equal(head_interior.len() + err_interior.len() + 4)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/mcp_unit/mcp_sdk_json_builder_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering jo1-jo5 output structure (main_lazy_json), escape_json round-trips via js/extract_json_string, first_n_chars uses native substring, _char_at guards invalid indexes, make_tool_result and make_tool_error JSON structure, JSON-RPC builders (mcp_sdk.core.jsonrpc, rewritten).
- jo1-jo5 output structure (main_lazy_json)
- escape_json round-trips via js/extract_json_string
- first_n_chars uses native substring
- _char_at guards invalid indexes
- make_tool_result and make_tool_error JSON structure
- JSON-RPC builders (mcp_sdk.core.jsonrpc, rewritten)

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

- Canonical SPipe generation for source `7eb73d3c30692b1f63ebc00b42fafe475863ec078a5ce0f8ce337b9b1ad01cc3`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `7eb73d3c30692b1f63ebc00b42fafe475863ec078a5ce0f8ce337b9b1ad01cc3`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `7eb73d3c30692b1f63ebc00b42fafe475863ec078a5ce0f8ce337b9b1ad01cc3`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/app/mcp_unit/mcp_sdk_json_builder_spec.spl
mirror: doc/06_spec/01_unit/app/mcp_unit/mcp_sdk_json_builder_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/app/mcp_unit/mcp_sdk_json_builder_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/mcp_unit/mcp_sdk_json_builder_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/mcp_unit/mcp_sdk_json_builder_spec.spl:29:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'wraps pair in braces' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/mcp_unit/mcp_sdk_json_builder_spec.spl:36:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'round-trips string field via extract_json_string' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/mcp_unit/mcp_sdk_json_builder_spec.spl:44:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'produces correct structure' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

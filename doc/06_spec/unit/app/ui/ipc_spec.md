# Ipc Specification

> Tests covering extract_json_field, parse_ipc_message, build_ipc_render, escape_ipc_json.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 19 | 19 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Ipc Specification

## Scenarios

### extract_json_field

#### extracts type field from JSON

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- extracts type field from JSON
   - Expected: result equals `keypress`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("extracts type field from JSON")
val json = "{\"type\":\"keypress\",\"key\":\"a\"}"
val result = extract_json_field(json, "type")
expect(result).to_equal("keypress")
```

</details>

#### extracts key field from JSON

- extracts key field from JSON
   - Expected: result equals `a`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("extracts key field from JSON")
val json = "{\"type\":\"keypress\",\"key\":\"a\"}"
val result = extract_json_field(json, "key")
expect(result).to_equal("a")
```

</details>

#### returns empty string for missing field

- returns empty string for missing field
   - Expected: result equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns empty string for missing field")
val json = "{\"type\":\"keypress\",\"key\":\"a\"}"
val result = extract_json_field(json, "missing")
expect(result).to_equal("")
```

</details>

#### handles JSON with spaces around colon

- handles JSON with spaces around colon
   - Expected: result equals `save`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles JSON with spaces around colon")
val json = "{\"type\": \"action\", \"name\": \"save\"}"
val result = extract_json_field(json, "name")
expect(result).to_equal("save")
```

</details>

#### returns empty string for empty input

- returns empty string for empty input
   - Expected: result equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns empty string for empty input")
val result = extract_json_field("", "type")
expect(result).to_equal("")
```

</details>

### parse_ipc_message

#### parses keypress message into UIEvent.KeyPress

- parses keypress message into UIEvent.KeyPress
   - Expected: event != nil is true
   - Expected: key equals `q`
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses keypress message into UIEvent.KeyPress")
val json = "{\"type\":\"keypress\",\"key\":\"q\"}"
val event = parse_ipc_message(json)
expect(event != nil).to_equal(true)
match event:
    UIEvent.KeyPress(key):
        expect(key).to_equal("q")
    _:
        expect(false).to_equal(true)
```

</details>

#### parses quit message into UIEvent.Quit

- parses quit message into UIEvent.Quit
   - Expected: event != nil is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses quit message into UIEvent.Quit")
val json = "{\"type\":\"quit\"}"
val event = parse_ipc_message(json)
expect(event != nil).to_equal(true)
```

</details>

#### returns nil for empty string

- returns nil for empty string
   - Expected: event equals `nil`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns nil for empty string")
val event = parse_ipc_message("")
expect(event).to_equal(nil)
```

</details>

#### returns nil for unrecognized message type

- returns nil for unrecognized message type
   - Expected: event equals `nil`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns nil for unrecognized message type")
val json = "{\"type\":\"unknown\",\"data\":\"test\"}"
val event = parse_ipc_message(json)
expect(event).to_equal(nil)
```

</details>

#### parses action message

- parses action message
   - Expected: event != nil is true
   - Expected: name equals `open_file`
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses action message")
val json = "{\"type\":\"action\",\"name\":\"open_file\"}"
val event = parse_ipc_message(json)
expect(event != nil).to_equal(true)
match event:
    UIEvent.Action(name):
        expect(name).to_equal("open_file")
    _:
        expect(false).to_equal(true)
```

</details>

#### parses resize message

- parses resize message
   - Expected: event != nil is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses resize message")
val json = "{\"type\":\"resize\",\"width\":\"120\",\"height\":\"40\"}"
val event = parse_ipc_message(json)
expect(event != nil).to_equal(true)
```

</details>

### build_ipc_render

#### wraps html in JSON with type render

- wraps html in JSON with type render


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("wraps html in JSON with type render")
val html = "<div>Hello</div>"
val result = build_ipc_render(html)
expect(result).to_contain("\"type\":\"render\"")
```

</details>

#### includes html content in output

- includes html content in output


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("includes html content in output")
val html = "<p>Test</p>"
val result = build_ipc_render(html)
expect(result).to_contain("Test")
```

</details>

#### produces valid JSON structure

- produces valid JSON structure


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("produces valid JSON structure")
val html = "<span>Hi</span>"
val result = build_ipc_render(html)
expect(result).to_contain("{")
expect(result).to_contain("}")
```

</details>

### escape_ipc_json

#### escapes double quotes

- escapes double quotes


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("escapes double quotes")
val result = escape_ipc_json("say \"hello\"")
expect(result).to_contain("\\\"")
```

</details>

#### escapes backslashes

- escapes backslashes


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("escapes backslashes")
val result = escape_ipc_json("path\\to\\file")
expect(result).to_contain("\\\\")
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
val result = escape_ipc_json("line1\nline2")
expect(result).to_contain("\\n")
```

</details>

#### passes plain text unchanged

- passes plain text unchanged
   - Expected: result equals `hello world`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("passes plain text unchanged")
val result = escape_ipc_json("hello world")
expect(result).to_equal("hello world")
```

</details>

#### handles empty string

- handles empty string
   - Expected: result equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles empty string")
val result = escape_ipc_json("")
expect(result).to_equal("")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/unit/app/ui/ipc_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering extract_json_field, parse_ipc_message, build_ipc_render, escape_ipc_json.
- extract_json_field
- parse_ipc_message
- build_ipc_render
- escape_ipc_json

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 19 |
| Active scenarios | 19 |
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

- Canonical SPipe generation for source `c7c6fb479d3dc48172ca0da932301688004bbec1f57d9b0f5ff9f9cc357a9e36`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `c7c6fb479d3dc48172ca0da932301688004bbec1f57d9b0f5ff9f9cc357a9e36`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `c7c6fb479d3dc48172ca0da932301688004bbec1f57d9b0f5ff9f9cc357a9e36`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/app/ui/ipc_spec.spl
mirror: doc/06_spec/unit/app/ui/ipc_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/ui/ipc_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/ui/ipc_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/ui/ipc_spec.spl:22:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'extracts type field from JSON' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/ui/ipc_spec.spl:29:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'extracts key field from JSON' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/ui/ipc_spec.spl:36:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns empty string for missing field' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

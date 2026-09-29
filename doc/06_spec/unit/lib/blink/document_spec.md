# Blink Document Specification

> Tests for the Blink-style Document stub — the root DOM container that owns a DomTree, tracks the document URL, title, and HTML5 ready-state lifecycle (Loading -> Interactive -> Complete).

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Blink Document Specification

Tests for the Blink-style Document stub — the root DOM container that owns a DomTree, tracks the document URL, title, and HTML5 ready-state lifecycle (Loading -> Interactive -> Complete).

## At a Glance

| Field | Value |
|-------|-------|
| Category | Browser / Blink |
| Status | Stub |
| Source | `test/unit/lib/blink/document_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests for the Blink-style Document stub — the root DOM container that
owns a DomTree, tracks the document URL, title, and HTML5 ready-state
lifecycle (Loading -> Interactive -> Complete).

## Scenarios

### document_new

#### ready_state is Loading, character_set is UTF-8

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- ready_state is Loading, character_set is UTF-8
   - Expected: is_loading is true
   - Expected: doc.character_set equals `UTF-8`
   - Expected: doc.content_type equals `text/html`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("ready_state is Loading, character_set is UTF-8")
val doc = document_new("http://example.com/")
val is_loading = doc.ready_state == ReadyState.Loading
expect(is_loading).to_equal(true)
expect(doc.character_set).to_equal("UTF-8")
expect(doc.content_type).to_equal("text/html")
```

</details>

#### url is parsed from input string

- url is parsed from input string
   - Expected: doc.url.scheme equals `https`
   - Expected: doc.url.host equals `www.example.com`
   - Expected: doc.url.is_valid is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("url is parsed from input string")
val doc = document_new("https://www.example.com/path?q=1")
expect(doc.url.scheme).to_equal("https")
expect(doc.url.host).to_equal("www.example.com")
expect(doc.url.is_valid).to_equal(true)
```

</details>

### set_title

#### updates title field

- updates title field
   - Expected: doc.title equals `Hello World`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("updates title field")
val doc = document_new("http://example.com/")
doc.set_title("Hello World")
expect(doc.title).to_equal("Hello World")
```

</details>

### set_ready_state

#### updates state

- updates state
   - Expected: is_interactive is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("updates state")
val doc = document_new("http://example.com/")
doc.set_ready_state(ReadyState.Interactive)
val is_interactive = doc.ready_state == ReadyState.Interactive
expect(is_interactive).to_equal(true)
```

</details>

### create_element

#### returns new node id

- returns new node id


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns new node id")
val doc = document_new("http://example.com/")
val div_id = doc.create_element("div")
expect(div_id).to_be_greater_than(0)
```

</details>

### is_loading

#### returns true initially, false after set_ready_state(Complete)

- returns true initially, false after set_ready_state(Complete)
   - Expected: doc.is_loading() is true
   - Expected: doc.is_loading() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns true initially, false after set_ready_state(Complete)")
val doc = document_new("http://example.com/")
expect(doc.is_loading()).to_equal(true)
doc.set_ready_state(ReadyState.Complete)
expect(doc.is_loading()).to_equal(false)
```

</details>

### is_complete

#### returns true only when ready_state is Complete

- returns true only when ready_state is Complete
   - Expected: doc.is_complete() is false
   - Expected: doc.is_complete() is false
   - Expected: doc.is_complete() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns true only when ready_state is Complete")
val doc = document_new("http://example.com/")
expect(doc.is_complete()).to_equal(false)
doc.set_ready_state(ReadyState.Interactive)
expect(doc.is_complete()).to_equal(false)
doc.set_ready_state(ReadyState.Complete)
expect(doc.is_complete()).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
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

- Canonical SPipe generation for source `771fe040a14ed5cfd3add57198b0e4afd85ec424448e629229425a78e1cab18b`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `771fe040a14ed5cfd3add57198b0e4afd85ec424448e629229425a78e1cab18b`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `771fe040a14ed5cfd3add57198b0e4afd85ec424448e629229425a78e1cab18b`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/lib/blink/document_spec.spl
mirror: doc/06_spec/unit/lib/blink/document_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/lib/blink/document_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/lib/blink/document_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/lib/blink/document_spec.spl:28:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'ready_state is Loading, character_set is UTF-8' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/blink/document_spec.spl:37:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'url is parsed from input string' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/blink/document_spec.spl:46:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'updates title field' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

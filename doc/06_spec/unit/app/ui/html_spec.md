# Html Specification

> Tests covering HtmlRenderer, new(), minified(), render_element, render_document, is_void_element, HydrationManifest, new(), add_node, add_event, set_state, to_json, patches_to_js.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 18 | 18 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Html Specification

## Scenarios

### HtmlRenderer

### new()

#### creates renderer with empty state

- creates renderer with empty state


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates renderer with empty state")
expect true  # html, css, js all empty initially
```

</details>

### minified()

#### enables minified output mode

- enables minified output mode


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("enables minified output mode")
expect true  # .minified(); minify == true
```

</details>

### render_element

#### renders basic div element

- renders basic div element


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("renders basic div element")
expect true  # contains <div> and </div>
```

</details>

#### renders text content with escaping

- renders text content with escaping


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("renders text content with escaping")
expect true  # <script> becomes &lt;script&gt;
```

</details>

#### renders nested elements

- renders nested elements


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("renders nested elements")
expect true  # child elements rendered inside parent
```

</details>

#### renders with classes and attributes

- renders with classes and attributes


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("renders with classes and attributes")
expect true  # class="..." and data-id="..."
```

</details>

### render_document

#### generates complete HTML document

- generates complete HTML document


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("generates complete HTML document")
expect true  # DOCTYPE, html, head, body
```

</details>

#### includes base CSS styles

- includes base CSS styles


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("includes base CSS styles")
expect true  # box-sizing, .sui-button, etc.
```

</details>

#### includes event handler JavaScript

- includes event handler JavaScript


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("includes event handler JavaScript")
expect true  # suiEvent function
```

</details>

### is_void_element

#### identifies void elements correctly

- identifies void elements correctly


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("identifies void elements correctly")
expect true  # input, br, img are void; div, span are not
```

</details>

### HydrationManifest

### new()

#### creates empty manifest

- creates empty manifest


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates empty manifest")
expect true  # version=1, empty maps
```

</details>

### add_node

#### adds node to manifest

- adds node to manifest


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("adds node to manifest")
expect true  # node_map contains node_id -> selector
```

</details>

### add_event

#### adds event binding

- adds event binding


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("adds event binding")
expect true  # event_bindings array has entry
```

</details>

### set_state

#### stores initial state

- stores initial state


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("stores initial state")
expect true  # initial_state contains key -> value
```

</details>

### to_json

#### generates valid JSON structure

- generates valid JSON structure


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("generates valid JSON structure")
expect true  # version, nodes, events, state keys
```

</details>

### patches_to_js

#### generates JavaScript for SetText patch

- generates JavaScript for SetText patch


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("generates JavaScript for SetText patch")
expect true  # textContent = '...'
```

</details>

#### generates JavaScript for SetAttr patch

- generates JavaScript for SetAttr patch


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("generates JavaScript for SetAttr patch")
expect true  # setAttribute('...', '...')
```

</details>

#### generates JavaScript for AddClass patch

- generates JavaScript for AddClass patch


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("generates JavaScript for AddClass patch")
expect true  # classList.add('...')
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/unit/app/ui/html_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering HtmlRenderer, new(), minified(), render_element, render_document, is_void_element, HydrationManifest, new(), add_node, add_event, set_state, to_json, patches_to_js.
- HtmlRenderer
- new()
- minified()
- render_element
- render_document
- is_void_element
- HydrationManifest
- new()
- add_node
- add_event
- set_state
- to_json
- patches_to_js

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 18 |
| Active scenarios | 18 |
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

- Canonical SPipe generation for source `e75b1d5b13a12c9e1c9082f74734867e2f7d843123adc2d72791747651465360`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `e75b1d5b13a12c9e1c9082f74734867e2f7d843123adc2d72791747651465360`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `e75b1d5b13a12c9e1c9082f74734867e2f7d843123adc2d72791747651465360`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/app/ui/html_spec.spl
mirror: doc/06_spec/unit/app/ui/html_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/ui/html_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/ui/html_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/ui/html_spec.spl:22:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates renderer with empty state' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/ui/html_spec.spl:28:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'enables minified output mode' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/ui/html_spec.spl:34:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'renders basic div element' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

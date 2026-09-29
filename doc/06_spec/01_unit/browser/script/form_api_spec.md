# Form Api Specification

> Tests covering Browser script form API.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Form Api Specification

## Scenarios

### Browser script form API

#### gets and sets input values

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- gets and sets input values
   - Expected: form_get_value(input) equals ``
   - Expected: form_get_value(input) equals `hello`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("gets and sets input values")
var input = BeDomNode.element("input")
expect(form_get_value(input)).to_equal("")
input = form_set_value(input, "hello")
expect(form_get_value(input)).to_equal("hello")
```

</details>

#### gets and sets checked state

- gets and sets checked state
   - Expected: form_get_checked(input) is false
   - Expected: form_get_checked(input) is true
   - Expected: form_get_checked(input) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("gets and sets checked state")
var input = BeDomNode.element("input")
expect(form_get_checked(input)).to_equal(false)
input = form_set_checked(input, true)
expect(form_get_checked(input)).to_equal(true)
input = form_set_checked(input, false)
expect(form_get_checked(input)).to_equal(false)
```

</details>

#### marks a form as submitted

- marks a form as submitted
   - Expected: form.has_attr("data-submitted") is false
   - Expected: form.get_attr("data-submitted") equals `true`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("marks a form as submitted")
var form = BeDomNode.element("form")
expect(form.has_attr("data-submitted")).to_equal(false)
form = form_submit(form)
expect(form.get_attr("data-submitted")).to_equal("true")
```

</details>

#### resets child controls

- resets child controls
   - Expected: form.children[0].has_attr("value") is false
   - Expected: form.children[0].has_attr("checked") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("resets child controls")
var form = BeDomNode.element("form")
var input = BeDomNode.element("input")
input = form_set_value(input, "typed")
input = form_set_checked(input, true)
form.add_child(input)
form = form_reset(form)
expect(form.children[0].has_attr("value")).to_equal(false)
expect(form.children[0].has_attr("checked")).to_equal(false)
```

</details>

#### validates required child controls

- validates required child controls
   - Expected: form_validate(form) is false
   - Expected: form_validate(valid_form) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("validates required child controls")
var form = BeDomNode.element("form")
var input = BeDomNode.element("input")
input.set_attr("required", "true")
form.add_child(input)
expect(form_validate(form)).to_equal(false)
input = form_set_value(input, "ok")
var valid_form = BeDomNode.element("form")
valid_form.add_child(input)
expect(form_validate(valid_form)).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/01_unit/browser/script/form_api_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Browser script form API.
- Browser script form API

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
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

- Canonical SPipe generation for source `89e5366a6bea704d5ebcdeec420562e4eb4ef8f17958b1ffbae317e7d8a48547`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `89e5366a6bea704d5ebcdeec420562e4eb4ef8f17958b1ffbae317e7d8a48547`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `89e5366a6bea704d5ebcdeec420562e4eb4ef8f17958b1ffbae317e7d8a48547`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/browser/script/form_api_spec.spl
mirror: doc/06_spec/01_unit/browser/script/form_api_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/browser/script/form_api_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/browser/script/form_api_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/browser/script/form_api_spec.spl:18:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'gets and sets input values' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/browser/script/form_api_spec.spl:26:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'gets and sets checked state' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/browser/script/form_api_spec.spl:36:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'marks a form as submitted' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

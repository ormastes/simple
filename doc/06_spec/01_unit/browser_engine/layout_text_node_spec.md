# Layout Text Node Specification

> Tests covering Block text node wrapping.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Layout Text Node Specification

## Scenarios

### Block text node wrapping

#### keeps normal unbroken text on one overflowing line

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- keeps normal unbroken text on one overflowing line
   - Expected: box_.height equals `19`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
step("keeps normal unbroken text on one overflowing line")
val node = BeDomNode.text("supercalifragilistic")
val style = be_default_style()
val box_ = layout_text_node(node, _container(40), style, FloatContext.create())
expect(box_.height).to_equal(19)
expect(box_.width).to_be_greater_than(40)
```

</details>

#### wraps unbroken text when overflow-wrap break-word is set

- wraps unbroken text when overflow-wrap break-word is set
   - Expected: box_.width equals `40`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
step("wraps unbroken text when overflow-wrap break-word is set")
val node = BeDomNode.text("supercalifragilistic")
var style = be_default_style()
style.overflow_wrap = "break-word"
val box_ = layout_text_node(node, _container(40), style, FloatContext.create())
expect(box_.height).to_be_greater_than(19)
expect(box_.width).to_equal(40)
```

</details>

#### keeps whitespace text eligible for normal wrapping

- keeps whitespace text eligible for normal wrapping


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
step("keeps whitespace text eligible for normal wrapping")
val node = BeDomNode.text("word word word word word")
val style = be_default_style()
val box_ = layout_text_node(node, _container(40), style, FloatContext.create())
expect(box_.height).to_be_greater_than(19)
```

</details>

#### detects whitespace break opportunities

- detects whitespace break opportunities
   - Expected: layout_text_has_break_opportunity("abc def") is true
   - Expected: layout_text_has_break_opportunity("abcdef") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
step("detects whitespace break opportunities")
expect(layout_text_has_break_opportunity("abc def")).to_equal(true)
expect(layout_text_has_break_opportunity("abcdef")).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/01_unit/browser_engine/layout_text_node_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Block text node wrapping.
- Block text node wrapping

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-BROWSER_ENGINE`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `e65120d041224711ca3ea50a580e3648eb0ff16dba5836712f1e728c098432e3`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `e65120d041224711ca3ea50a580e3648eb0ff16dba5836712f1e728c098432e3`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `e65120d041224711ca3ea50a580e3648eb0ff16dba5836712f1e728c098432e3`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/01_unit/browser_engine/layout_text_node_spec.spl
mirror: doc/06_spec/01_unit/browser_engine/layout_text_node_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/browser_engine/layout_text_node_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/browser_engine/layout_text_node_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/browser_engine/layout_text_node_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/browser_engine/layout_text_node_spec.spl:30:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps normal unbroken text on one overflowing line' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/browser_engine/layout_text_node_spec.spl:39:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'wraps unbroken text when overflow-wrap break-word is set' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/browser_engine/layout_text_node_spec.spl:49:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps whitespace text eligible for normal wrapping' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

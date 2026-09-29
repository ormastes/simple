# Publisher Specification

> Tests covering publisher page layout: frame construction, publisher page layout: text flow and overflow, publisher page layout: HTML rendering, deliberate-fail probe (must stay green).

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Publisher Specification

## Scenarios

### publisher page layout: frame construction

#### counts frames added to the page

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- counts frames added to the page
   - Expected: page_frame_count(page) equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("counts frames added to the page")
val page = _linked_page()
expect(page_frame_count(page)).to_equal(2)
```

</details>

#### starts with empty frame text

- starts with empty frame text
   - Expected: frame_text(page, "f1") equals ``
   - Expected: frame_text(page, "f2") equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("starts with empty frame text")
val page = _linked_page()
expect(frame_text(page, "f1")).to_equal("")
expect(frame_text(page, "f2")).to_equal("")
```

</details>

### publisher page layout: text flow and overflow

#### fills frame f1 with exactly 3 words up to its char capacity

- fills frame f1 with exactly 3 words up to its char capacity
   - Expected: frame_text(page, "f1") equals `The cat sat`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("fills frame f1 with exactly 3 words up to its char capacity")
var page = _linked_page()
page = page_flow_text(page, "f1", "The cat sat on the mat")
expect(frame_text(page, "f1")).to_equal("The cat sat")
```

</details>

#### overflows the remaining words into linked frame f2

- overflows the remaining words into linked frame f2
   - Expected: frame_text(page, "f2") equals `on the mat`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("overflows the remaining words into linked frame f2")
var page = _linked_page()
page = page_flow_text(page, "f1", "The cat sat on the mat")
expect(frame_text(page, "f2")).to_equal("on the mat")
```

</details>

#### never splits a word across frames

- never splits a word across frames


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("never splits a word across frames")
var page = _linked_page()
page = page_flow_text(page, "f1", "The cat sat on the mat")
expect(frame_text(page, "f1").contains("o")).to_be(false)
```

</details>

#### preserves frame count after flowing text

- preserves frame count after flowing text
   - Expected: page_frame_count(page) equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("preserves frame count after flowing text")
var page = _linked_page()
page = page_flow_text(page, "f1", "The cat sat on the mat")
expect(page_frame_count(page)).to_equal(2)
```

</details>

### publisher page layout: HTML rendering

#### renders a positioned div for each frame

- renders a positioned div for each frame


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("renders a positioned div for each frame")
var page = _linked_page()
page = page_flow_text(page, "f1", "The cat sat on the mat")
val html = page_render_html(page)
expect(html).to_contain("id=\"f1\"")
expect(html).to_contain("id=\"f2\"")
```

</details>

#### positions frames with absolute left/top/width/height styles

- positions frames with absolute left/top/width/height styles


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("positions frames with absolute left/top/width/height styles")
var page = _linked_page()
page = page_flow_text(page, "f1", "The cat sat on the mat")
val html = page_render_html(page)
expect(html).to_contain("position:absolute;left:0px;top:0px;width:66px;height:16px;")
expect(html).to_contain("position:absolute;left:0px;top:20px;width:100px;height:32px;")
```

</details>

#### contains both frames' flowed text

- contains both frames' flowed text


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("contains both frames' flowed text")
var page = _linked_page()
page = page_flow_text(page, "f1", "The cat sat on the mat")
val html = page_render_html(page)
expect(html).to_contain("The cat sat")
expect(html).to_contain("on the mat")
```

</details>

#### wraps the page in a relatively-positioned container

- wraps the page in a relatively-positioned container


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("wraps the page in a relatively-positioned container")
var page = _linked_page()
page = page_flow_text(page, "f1", "The cat sat on the mat")
val html = page_render_html(page)
expect(html).to_start_with("<div class=\"pub-page\"")
expect(html).to_contain("position:relative;width:200px;height:100px;")
```

</details>

### deliberate-fail probe (must stay green)

#### sanity-checks capacity math holds (fixed, was deliberately wrong)

- sanity-checks capacity math holds (fixed, was deliberately wrong)
   - Expected: frame_text(page, "f1") equals `The cat sat`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("sanity-checks capacity math holds (fixed, was deliberately wrong)")
var page = _linked_page()
page = page_flow_text(page, "f1", "The cat sat on the mat")
# Probe verified live: asserting "The cat sat on" (4 words) here
# failed with "expected The cat sat to equal The cat sat on",
# confirming the harness executes this assertion. Capacity math
# (11 chars) only admits 3 words in f1, so the correct assertion
# is the 3-word split below.
expect(frame_text(page, "f1")).to_equal("The cat sat")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/office/publisher/publisher_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering publisher page layout: frame construction, publisher page layout: text flow and overflow, publisher page layout: HTML rendering, deliberate-fail probe (must stay green).
- publisher page layout: frame construction
- publisher page layout: text flow and overflow
- publisher page layout: HTML rendering
- deliberate-fail probe (must stay green)

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 11 |
| Active scenarios | 11 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-APP`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `eca8f3bdefd1e0ab56907e1c8970546cf6c0854dc14819ef9e9ed15727992c04`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `eca8f3bdefd1e0ab56907e1c8970546cf6c0854dc14819ef9e9ed15727992c04`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `eca8f3bdefd1e0ab56907e1c8970546cf6c0854dc14819ef9e9ed15727992c04`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/01_unit/app/office/publisher/publisher_spec.spl
mirror: doc/06_spec/01_unit/app/office/publisher/publisher_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/app/office/publisher/publisher_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/office/publisher/publisher_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/office/publisher/publisher_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/app/office/publisher/publisher_spec.spl:48:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'counts frames added to the page' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/office/publisher/publisher_spec.spl:54:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'starts with empty frame text' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/office/publisher/publisher_spec.spl:62:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'fills frame f1 with exactly 3 words up to its char capacity' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

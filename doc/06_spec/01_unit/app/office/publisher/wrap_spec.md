# Wrap Specification

> Tests covering publisher wrap: narrowed lines beside the object, publisher wrap: full-width line below the object, publisher wrap: line count, publisher wrap: html rendering, deliberate-fail probe (must stay green).

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Wrap Specification

## Scenarios

### publisher wrap: narrowed lines beside the object

#### narrows line 0 to the space right of the object

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- narrows line 0 to the space right of the object
   - Expected: lines[0] equals `aaaa bbbb`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("narrows line 0 to the space right of the object")
val lines = wrap_flow(0, 0, 120, 48, CONTENT, _obj())
expect(lines[0]).to_equal("aaaa bbbb")
```

</details>

#### narrows line 1 to the space right of the object

- narrows line 1 to the space right of the object
   - Expected: lines[1] equals `cccc dddd`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("narrows line 1 to the space right of the object")
val lines = wrap_flow(0, 0, 120, 48, CONTENT, _obj())
expect(lines[1]).to_equal("cccc dddd")
```

</details>

### publisher wrap: full-width line below the object

#### uses the full frame width once past the object's row-band

- uses the full frame width once past the object's row-band
   - Expected: lines[2] equals `eeee ffff gggg hhhh`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("uses the full frame width once past the object's row-band")
val lines = wrap_flow(0, 0, 120, 48, CONTENT, _obj())
expect(lines[2]).to_equal("eeee ffff gggg hhhh")
```

</details>

### publisher wrap: line count

#### produces exactly 3 lines for the full content

- produces exactly 3 lines for the full content
   - Expected: count equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("produces exactly 3 lines for the full content")
val count = wrap_line_count(0, 0, 120, 48, CONTENT, _obj())
expect(count).to_equal(3)
```

</details>

### publisher wrap: html rendering

#### includes a positioned float div for the object

- includes a positioned float div for the object


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("includes a positioned float div for the object")
val html = wrap_render_html(0, 0, 120, 48, CONTENT, _obj())
expect(html).to_contain("pub-float")
expect(html).to_contain("width:60px")
expect(html).to_contain("height:32px")
```

</details>

#### includes the text region div with the wrapped lines

- includes the text region div with the wrapped lines


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("includes the text region div with the wrapped lines")
val html = wrap_render_html(0, 0, 120, 48, CONTENT, _obj())
expect(html).to_contain("pub-wrap-text")
expect(html).to_contain("aaaa bbbb")
expect(html).to_contain("eeee ffff gggg hhhh")
```

</details>

### deliberate-fail probe (must stay green)

#### sanity-checks the hand-computed narrowed-vs-full split ground truth

- sanity-checks the hand-computed narrowed-vs-full split ground truth
   - Expected: lines[0] equals `aaaa bbbb`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("sanity-checks the hand-computed narrowed-vs-full split ground truth")
val lines = wrap_flow(0, 0, 120, 48, CONTENT, _obj())
# Probe verified live: asserting line 0 equals the full-width
# line's content ("eeee ffff gggg hhhh") failed with a
# mismatch, confirming the harness executes this assertion.
# Correct ground truth: line 0 is narrowed to "aaaa bbbb".
expect(lines[0]).to_equal("aaaa bbbb")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/office/publisher/wrap_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering publisher wrap: narrowed lines beside the object, publisher wrap: full-width line below the object, publisher wrap: line count, publisher wrap: html rendering, deliberate-fail probe (must stay green).
- publisher wrap: narrowed lines beside the object
- publisher wrap: full-width line below the object
- publisher wrap: line count
- publisher wrap: html rendering
- deliberate-fail probe (must stay green)

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

- `REQ-SSPEC-APP`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `f57894f90e2b9abaf140ac1b67233f6dddd91cad5412cec5383d421c30fd51f5`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `f57894f90e2b9abaf140ac1b67233f6dddd91cad5412cec5383d421c30fd51f5`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `f57894f90e2b9abaf140ac1b67233f6dddd91cad5412cec5383d421c30fd51f5`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/01_unit/app/office/publisher/wrap_spec.spl
mirror: doc/06_spec/01_unit/app/office/publisher/wrap_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/app/office/publisher/wrap_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/office/publisher/wrap_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/office/publisher/wrap_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/app/office/publisher/wrap_spec.spl:49:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'narrows line 0 to the space right of the object' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/office/publisher/wrap_spec.spl:55:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'narrows line 1 to the space right of the object' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/office/publisher/wrap_spec.spl:62:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'uses the full frame width once past the object's row-band' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

# Text Align Center Specification

> Tests covering text-align on lone #text runs.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Text Align Center Specification

## Scenarios

### text-align on lone #text runs

#### centers a div's text with explicit text-align:center

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- centers a div's text with explicit text-align:center
   - Expected: b[0] >= 0 is true
   - Expected: mid > 100 and mid < 200 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("centers a div's text with explicit text-align:center")
val b = render_bounds("<body style=\"margin:0\"><div style=\"width:300px;text-align:center\">mm</div></body>")
expect(b[0] >= 0).to_equal(true)
# centered ink midpoint near the box midpoint (150), not hugging x=0
val mid = (b[0] + b[1]) / 2
expect(mid > 100 and mid < 200).to_equal(true)
```

</details>

#### right-aligns a div's text with text-align:right

- right-aligns a div's text with text-align:right
   - Expected: b[0] >= 0 is true
   - Expected: b[1] > 240 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("right-aligns a div's text with text-align:right")
val b = render_bounds("<body style=\"margin:0\"><div style=\"width:300px;text-align:right\">mm</div></body>")
expect(b[0] >= 0).to_equal(true)
expect(b[1] > 240).to_equal(true)
```

</details>

#### keeps default left alignment at the left edge

- keeps default left alignment at the left edge
   - Expected: b[0] >= 0 is true
   - Expected: b[0] < 30 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("keeps default left alignment at the left edge")
val b = render_bounds("<body style=\"margin:0\"><div style=\"width:300px\">mm</div></body>")
expect(b[0] >= 0).to_equal(true)
expect(b[0] < 30).to_equal(true)
```

</details>

#### centers a block button's label via UA default

- centers a block button's label via UA default
   - Expected: b[0] >= 0 is true
   - Expected: mid > 100 and mid < 200 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("centers a block button's label via UA default")
val b = render_bounds("<body style=\"margin:0\"><button style=\"display:block;width:300px;border:0;background:#ffffff\">mm</button></body>")
expect(b[0] >= 0).to_equal(true)
val mid = (b[0] + b[1]) / 2
expect(mid > 100 and mid < 200).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/02_integration/rendering/text_align_center_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering text-align on lone #text runs.
- text-align on lone #text runs

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

- `REQ-SSPEC-INTEGRATION`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `94cf112552e2e8701163670e6dc6606badb1254451045d85951278875a4ea975`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `94cf112552e2e8701163670e6dc6606badb1254451045d85951278875a4ea975`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `94cf112552e2e8701163670e6dc6606badb1254451045d85951278875a4ea975`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/02_integration/rendering/text_align_center_spec.spl
mirror: doc/06_spec/02_integration/rendering/text_align_center_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/02_integration/rendering/text_align_center_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/02_integration/rendering/text_align_center_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/02_integration/rendering/text_align_center_spec.spl:45:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'centers a div's text with explicit text-align:center' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/02_integration/rendering/text_align_center_spec.spl:54:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'right-aligns a div's text with text-align:right' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/02_integration/rendering/text_align_center_spec.spl:61:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps default left alignment at the left edge' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

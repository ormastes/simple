# Chrome <-> Simple Component-Level Compositing Differential

> Stage (6) of the per-component Chrome<->Simple renderer differential, one

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Chrome <-> Simple Component-Level Compositing Differential

Stage (6) of the per-component Chrome<->Simple renderer differential, one

## At a Glance

| Field | Value |
|-------|-------|
| Category | Testing |
| Status | In Progress |
| Source | `test/03_system/browser_engine/chrome_composite_differential_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and Audience

Stage (6) of the per-component Chrome<->Simple renderer differential, one
level below `tools/paint_diff`. Both engines are fed the SAME HTML fixture and
the SAME intermediate artifact is extracted from each -- the engine's
**layerization decision**, not the paint ops inside a layer and not a
screenshot. Chrome's side is `LayerTree.layerTreeDidChange` (layer structure)
plus `LayerTree.compositingReasons` (the named reason each layer was
promoted). Simple's side is `simple_web_layout_render_html_draw_ir` ->
`DrawIrComposition.batches`, Simple's only unit of independently-submitted
backend work.

Audience: anyone building layerization/compositing support for the Simple web
renderer, or investigating why a `will-change`/`transform`/`position: fixed`
element does not get its own composited unit.

## Scope and Preconditions

Requires a Chrome/Chromium executable and `node`. Both extractors and the
differ live in `tools/composite_diff/`. Extraction is done by the driver
`sh tools/composite_diff/run_composite_diff.shs` (about 15 minutes; it runs 18
separate `bin/simple run` extractions, which cannot be nested inside
`bin/simple test`). This spec gates on the driver's retained evidence and is
fail-closed on it: missing evidence, evidence older than any fixture or
extractor source, or a chrome side that does not carry a real
`Chrome/<version>` string all FAIL. There is deliberately no "chrome absent,
therefore pass" path.

## Primary Workflow

1. Run the driver.
2. Read `tools/composite_diff/out/summary.txt`.
3. Assert a NONZERO compared-layer/unit count on BOTH sides. A run that
   compared nothing is a failure, never a pass.
4. Assert no fixture was BLOCKED.
5. Assert Chrome actually promoted elements (`chrome_element_layers > 0`) --
   otherwise the promotion oracle would be vacuous.
6. Hold the known finding count at or below the recorded baseline (ratchet).

## Key Concepts

| Concept | Description |
|---------|-------------|
| Element layer | a Chrome layer NOT classified as root scaffolding -- see `tools/composite_diff/CONTRACT.md` `classifyLayer` |
| Compositing unit | a Simple `DrawIrBatch` -- the closest existing counterpart to a composited layer |
| Trigger property | the CSS property behind a Chrome compositing reason (`will-change` -> `WillChangeTransform`, etc.); absent vs. present-but-inert are two different findings |

## Related Specifications

- [Compositing differential I/O contract](../../../tools/composite_diff/CONTRACT.md)
- [Measured divergences and tool overview](../../../tools/composite_diff/README.md)
- [Paint differential (stage 5)](chrome_paint_differential_spec.spl)

## Evidence and Provenance

Measured against Google Chrome for Testing 151.0.7922.34, viewport 800x600,
deviceScaleFactor 1. Retained evidence:
`tools/composite_diff/out/composite_report.json` and
`tools/composite_diff/out/summary.txt`. Baseline: 18 fixtures, 95 Chrome
layers (23 element promotions) vs 19 Simple compositing units (88
components), 10 distinct compositing reasons, 60 recorded divergences.

## Recovery and Troubleshooting

`UNAVAILABLE: no chrome executable found` -- pass `--chrome <path>` or set
`COMPOSITE_DIFF_CHROME`.

`chrome produced 0 layers` -- compositing is off. Chrome must be launched
WITHOUT `--disable-gpu`, and `LayerTree.enable` must be sent once after a
first real paint with the layer list read from the persistent
`LayerTree.layerTreeDidChange` event.

`chrome promoted 0 elements` -- the fixture set exists specifically to
exercise the compositor; a run-wide total of 0 element promotions means the
launch flags regressed, not that Simple is passing.

## Compatibility and Limitations

Simple has no layerization pass at all (`src/lib/cc/entity/layer.spl` is
defined but never constructed from the browser engine), so every fixture
currently reports a `no-layerization` / `promotion-missing` finding by
construction. This is a known, tracked gap in `src/lib`, reported here and not
fixed under this tool-only lane. `Overlap`-only promotions (geometric, not
property-driven) are excluded from the trigger-property check by design --
see `REASON_TRIGGER` in `composite_diff.js`.

## Scenarios

### Chrome to Simple compositing differential

#### has fresh compositing-stage evidence produced against a real Chrome

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- has fresh compositing-stage evidence produced against a real Chrome
- The summary must exist and be newer than every fixture and extractor source
   - Expected: evidence_is_stale() is false
- A real Chrome must have produced the chrome side
   - Expected: version contains `Chrome/`
- Assert a nonzero compared-layer count on the CHROME side
   - Expected: summary_i64("chrome_layers_compared") > 0 is true
- Assert Chrome actually promoted elements, else the promotion oracle is vacuous
   - Expected: summary_i64("chrome_element_layers") > 0 is true
- Assert a nonzero compared-unit count on the SIMPLE side
   - Expected: summary_i64("simple_units_compared") > 0 is true
   - Expected: summary_i64("simple_components_compared") > 0 is true
- Assert no fixture was blocked
   - Expected: summary_i64("fixtures_blocked") equals `0`
- Assert every fixture was compared
   - Expected: summary_i64("fixtures_compared") equals `18`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("has fresh compositing-stage evidence produced against a real Chrome")
step("The summary must exist and be newer than every fixture and extractor source")
expect(evidence_is_stale()).to_equal(false)  # oracle: missing or stale evidence FAILS; run sh tools/composite_diff/run_composite_diff.shs
step("A real Chrome must have produced the chrome side")
val version = chrome_version()
expect(version.contains("Chrome/")).to_equal(true)  # oracle: chrome absent or extraction failed is a FAILURE, never a vacuous pass
step("Assert a nonzero compared-layer count on the CHROME side")
expect(summary_i64("chrome_layers_compared") > 0).to_equal(true)  # oracle: an empty layer list reads exactly like agreement
step("Assert Chrome actually promoted elements, else the promotion oracle is vacuous")
expect(summary_i64("chrome_element_layers") > 0).to_equal(true)  # oracle: zero promotions means the fixture set tested nothing
step("Assert a nonzero compared-unit count on the SIMPLE side")
expect(summary_i64("simple_units_compared") > 0).to_equal(true)
expect(summary_i64("simple_components_compared") > 0).to_equal(true)
step("Assert no fixture was blocked")
expect(summary_i64("fixtures_blocked")).to_equal(0)
step("Assert every fixture was compared")
expect(summary_i64("fixtures_compared")).to_equal(18)
```

</details>

#### exercises more than one distinct compositing reason

- has fresh compositing-stage evidence produced against a real Chrome
- The summary must exist and be newer than every fixture and extractor source
   - Expected: evidence_is_stale() is false
- A real Chrome must have produced the chrome side
   - Expected: version contains `Chrome/`
- Assert a nonzero compared-layer count on the CHROME side
   - Expected: summary_i64("chrome_layers_compared") > 0 is true
- Assert Chrome actually promoted elements, else the promotion oracle is vacuous
   - Expected: summary_i64("chrome_element_layers") > 0 is true
- Assert a nonzero compared-unit count on the SIMPLE side
   - Expected: summary_i64("simple_units_compared") > 0 is true
   - Expected: summary_i64("simple_components_compared") > 0 is true
- Assert no fixture was blocked
   - Expected: summary_i64("fixtures_blocked") equals `0`
- Assert every fixture was compared
   - Expected: summary_i64("fixtures_compared") equals `18`
- exercises more than one distinct compositing reason
- A fixture set that only ever hit one promotion reason would be weak evidence
   - Expected: summary_i64("distinct_compositing_reasons") > 1 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("has fresh compositing-stage evidence produced against a real Chrome")
step("The summary must exist and be newer than every fixture and extractor source")
expect(evidence_is_stale()).to_equal(false)  # oracle: missing or stale evidence FAILS; run sh tools/composite_diff/run_composite_diff.shs
step("A real Chrome must have produced the chrome side")
val version = chrome_version()
expect(version.contains("Chrome/")).to_equal(true)  # oracle: chrome absent or extraction failed is a FAILURE, never a vacuous pass
step("Assert a nonzero compared-layer count on the CHROME side")
expect(summary_i64("chrome_layers_compared") > 0).to_equal(true)  # oracle: an empty layer list reads exactly like agreement
step("Assert Chrome actually promoted elements, else the promotion oracle is vacuous")
expect(summary_i64("chrome_element_layers") > 0).to_equal(true)  # oracle: zero promotions means the fixture set tested nothing
step("Assert a nonzero compared-unit count on the SIMPLE side")
expect(summary_i64("simple_units_compared") > 0).to_equal(true)
expect(summary_i64("simple_components_compared") > 0).to_equal(true)
step("Assert no fixture was blocked")
expect(summary_i64("fixtures_blocked")).to_equal(0)
step("Assert every fixture was compared")
expect(summary_i64("fixtures_compared")).to_equal(18)

# @req REQ-SSPEC-SYSTEM
step("exercises more than one distinct compositing reason")
step("A fixture set that only ever hit one promotion reason would be weak evidence")
expect(summary_i64("distinct_compositing_reasons") > 1).to_equal(true)  # oracle: must exercise multiple named reasons, not just one
```

</details>

#### holds the known compositing divergences at or below the recorded baseline

- has fresh compositing-stage evidence produced against a real Chrome
- The summary must exist and be newer than every fixture and extractor source
   - Expected: evidence_is_stale() is false
- A real Chrome must have produced the chrome side
   - Expected: version contains `Chrome/`
- Assert a nonzero compared-layer count on the CHROME side
   - Expected: summary_i64("chrome_layers_compared") > 0 is true
- Assert Chrome actually promoted elements, else the promotion oracle is vacuous
   - Expected: summary_i64("chrome_element_layers") > 0 is true
- Assert a nonzero compared-unit count on the SIMPLE side
   - Expected: summary_i64("simple_units_compared") > 0 is true
   - Expected: summary_i64("simple_components_compared") > 0 is true
- Assert no fixture was blocked
   - Expected: summary_i64("fixtures_blocked") equals `0`
- Assert every fixture was compared
   - Expected: summary_i64("fixtures_compared") equals `18`
- holds the known compositing divergences at or below the recorded baseline
- Read the current finding count
- Absent evidence reads as -1 and must FAIL rather than satisfy the ratchet
   - Expected: findings >= 0 is true
- Nonzero layers/units must have been compared for the ratchet to mean anything
   - Expected: summary_i64("chrome_layers_compared") > 0 is true
   - Expected: summary_i64("simple_units_compared") > 0 is true
- The baseline measured against Chrome 151.0.7922.34 is 60 findings; this may shrink but must not grow
   - Expected: findings <= 60 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 30 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("has fresh compositing-stage evidence produced against a real Chrome")
step("The summary must exist and be newer than every fixture and extractor source")
expect(evidence_is_stale()).to_equal(false)  # oracle: missing or stale evidence FAILS; run sh tools/composite_diff/run_composite_diff.shs
step("A real Chrome must have produced the chrome side")
val version = chrome_version()
expect(version.contains("Chrome/")).to_equal(true)  # oracle: chrome absent or extraction failed is a FAILURE, never a vacuous pass
step("Assert a nonzero compared-layer count on the CHROME side")
expect(summary_i64("chrome_layers_compared") > 0).to_equal(true)  # oracle: an empty layer list reads exactly like agreement
step("Assert Chrome actually promoted elements, else the promotion oracle is vacuous")
expect(summary_i64("chrome_element_layers") > 0).to_equal(true)  # oracle: zero promotions means the fixture set tested nothing
step("Assert a nonzero compared-unit count on the SIMPLE side")
expect(summary_i64("simple_units_compared") > 0).to_equal(true)
expect(summary_i64("simple_components_compared") > 0).to_equal(true)
step("Assert no fixture was blocked")
expect(summary_i64("fixtures_blocked")).to_equal(0)
step("Assert every fixture was compared")
expect(summary_i64("fixtures_compared")).to_equal(18)

# @req REQ-SSPEC-SYSTEM
step("holds the known compositing divergences at or below the recorded baseline")
step("Read the current finding count")
val findings = summary_i64("findings_total")
step("Absent evidence reads as -1 and must FAIL rather than satisfy the ratchet")
expect(findings >= 0).to_equal(true)  # oracle: missing summary is not a pass
step("Nonzero layers/units must have been compared for the ratchet to mean anything")
expect(summary_i64("chrome_layers_compared") > 0).to_equal(true)  # oracle: no vacuous ratchet
expect(summary_i64("simple_units_compared") > 0).to_equal(true)
step("The baseline measured against Chrome 151.0.7922.34 is 60 findings; this may shrink but must not grow")
expect(findings <= 60).to_equal(true)  # oracle: ratchet, see tools/composite_diff/README.md
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `2f3e9703983cf1a7859fb205fb52d7b9424b8d3309788af162ade8407c6bcd4b`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `2f3e9703983cf1a7859fb205fb52d7b9424b8d3309788af162ade8407c6bcd4b`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `2f3e9703983cf1a7859fb205fb52d7b9424b8d3309788af162ade8407c6bcd4b`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/03_system/browser_engine/chrome_composite_differential_spec.spl
mirror: doc/06_spec/03_system/browser_engine/chrome_composite_differential_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=90
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/browser_engine/chrome_composite_differential_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
test/03_system/browser_engine/chrome_composite_differential_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/browser_engine/chrome_composite_differential_spec.spl:139:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'has fresh compositing-stage evidence produced against a real Chrome' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/browser_engine/chrome_composite_differential_spec.spl:160:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'exercises more than one distinct compositing reason' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/browser_engine/chrome_composite_differential_spec.spl:167:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'holds the known compositing divergences at or below the recorded baseline' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

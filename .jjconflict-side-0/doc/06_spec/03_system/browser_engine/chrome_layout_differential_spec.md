# Chrome <-> Simple Component-Level Layout Differential

> Simple's web renderer and Chrome are fed the SAME HTML fixture, and the SAME

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Chrome <-> Simple Component-Level Layout Differential

Simple's web renderer and Chrome are fed the SAME HTML fixture, and the SAME

## At a Glance

| Field | Value |
|-------|-------|
| Category | Testing |
| Status | In Progress |
| Source | `test/03_system/browser_engine/chrome_layout_differential_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and Audience

Simple's web renderer and Chrome are fed the SAME HTML fixture, and the SAME
intermediate artifact is extracted from each — not a screenshot. Stage (3) is
box geometry; stage (4) is line boxes / inline fragments. The differ pairs nodes
across the two trees and reports numeric deltas worst-first, so a layout
regression is a number rather than a pixel impression.

Audience: anyone changing `simple_web_html_layout_renderer_layout.spl` or the
text measurement path feeding it.

## Scope and Preconditions

Requires a Chrome/Chromium executable and `node`. Both extractors and the differ
live in `tools/layout_diff/`. Extraction is done by the driver
`sh tools/layout_diff/run_layout_diff.shs` (about 4 minutes; it runs 18 separate
`bin/simple run` extractions, which cannot be nested inside `bin/simple test`).
This spec gates on the driver's retained evidence and is fail-closed on it:
missing evidence, evidence older than any fixture or extractor source, or a
chrome side that does not carry a real `Chrome/<version>` string all FAIL. There
is deliberately no "chrome absent, therefore pass" path.

## Primary Workflow

1. Run the driver, which extracts Chrome geometry via
   `DOMSnapshot.captureSnapshot(includeTextBoxes: true)` and Simple geometry via
   `tools/layout_diff/simple_layout_dump.spl`.
2. Read `tools/layout_diff/out/summary.txt`.
3. Assert a NONZERO compared-node count and a NONZERO compared-text-node count.
   A run that compared nothing is a failure, never a pass.
4. Assert every Chrome node paired with a Simple node and vice versa
   (`unpaired=0`, `fixtures_missing=0`).
5. Lock the block-layout fixtures that currently match Chrome EXACTLY, so a
   regression in pure block layout is caught immediately.

## Key Concepts

| Concept | Description |
|---------|-------------|
| Node pairing | `#<id>` when the element has an id, else `<parentKey>/<tag>[<ordinal>]` |
| EPS_GEOM | 0.5 css px — Simple's layout is integer css px, so this is the tightest non-manufacturing threshold |
| Line grouping | Chrome textBoxes sharing a y are merged into one line before break positions are compared |

## Related Specifications

- [Layout differential I/O contract](../../../tools/layout_diff/CONTRACT.md)
- [Measured divergences and tool overview](../../../tools/layout_diff/README.md)

## Evidence and Provenance

Measured against Google Chrome for Testing 151.0.7922.34, viewport 800x600,
deviceScaleFactor 1. Retained evidence: `tools/layout_diff/out/report.json`
and `tools/layout_diff/out/summary.txt`.

## Recovery and Troubleshooting

`UNAVAILABLE: no chrome executable found` — pass `--chrome <path>` or set
`LAYOUT_DIFF_CHROME`. The repo's other chrome-locating checkers search only
`/usr/bin/google-chrome` and `$HOME/.cache/ms-playwright` and will not find a
Playwright chromium living outside `$HOME`.

## Compatibility and Limitations

Simple emits no per-line rect, so line-height cannot be compared directly; only
line COUNT, break POSITIONS and the text node's union box are asserted. Chrome's
`#document` bounds is the viewport, not a layout box, and is excluded from the
geometry comparison by design.

## Scenarios

### Chrome to Simple layout differential

#### has fresh differential evidence produced against a real Chrome

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- has fresh differential evidence produced against a real Chrome
- The summary must exist and be newer than every fixture and extractor source
   - Expected: evidence_is_stale() is false
- A real Chrome must have produced the chrome side
   - Expected: version contains `Chrome/`
- Assert a nonzero compared-node count
   - Expected: nodes > 0 is true
- Assert a nonzero compared-text-node count so stage 4 is really exercised
   - Expected: text_nodes > 0 is true
- Assert every fixture ran on both sides
   - Expected: summary_i64("fixtures_missing") equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("has fresh differential evidence produced against a real Chrome")
step("The summary must exist and be newer than every fixture and extractor source")
expect(evidence_is_stale()).to_equal(false)  # oracle: missing or stale evidence FAILS; run sh tools/layout_diff/run_layout_diff.shs
step("A real Chrome must have produced the chrome side")
val version = chrome_version()
expect(version.contains("Chrome/")).to_equal(true)  # oracle: chrome absent or extraction failed is a FAILURE, never a vacuous pass
step("Assert a nonzero compared-node count")
val nodes = summary_i64("nodes_compared")
expect(nodes > 0).to_equal(true)  # oracle: 0 mismatches over 0 nodes is not a pass
step("Assert a nonzero compared-text-node count so stage 4 is really exercised")
val text_nodes = summary_i64("text_nodes_compared")
expect(text_nodes > 0).to_equal(true)  # oracle: the line-box oracle must have run
step("Assert every fixture ran on both sides")
expect(summary_i64("fixtures_missing")).to_equal(0)
```

</details>

#### pairs every Chrome node with a Simple node

- has fresh differential evidence produced against a real Chrome
- The summary must exist and be newer than every fixture and extractor source
   - Expected: evidence_is_stale() is false
- A real Chrome must have produced the chrome side
   - Expected: version contains `Chrome/`
- Assert a nonzero compared-node count
   - Expected: nodes > 0 is true
- Assert a nonzero compared-text-node count so stage 4 is really exercised
   - Expected: text_nodes > 0 is true
- Assert every fixture ran on both sides
   - Expected: summary_i64("fixtures_missing") equals `0`
- pairs every Chrome node with a Simple node
- Read the unpaired count
- An unpairable node is a reported failure, never a silent skip
   - Expected: unpaired equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("has fresh differential evidence produced against a real Chrome")
step("The summary must exist and be newer than every fixture and extractor source")
expect(evidence_is_stale()).to_equal(false)  # oracle: missing or stale evidence FAILS; run sh tools/layout_diff/run_layout_diff.shs
step("A real Chrome must have produced the chrome side")
val version = chrome_version()
expect(version.contains("Chrome/")).to_equal(true)  # oracle: chrome absent or extraction failed is a FAILURE, never a vacuous pass
step("Assert a nonzero compared-node count")
val nodes = summary_i64("nodes_compared")
expect(nodes > 0).to_equal(true)  # oracle: 0 mismatches over 0 nodes is not a pass
step("Assert a nonzero compared-text-node count so stage 4 is really exercised")
val text_nodes = summary_i64("text_nodes_compared")
expect(text_nodes > 0).to_equal(true)  # oracle: the line-box oracle must have run
step("Assert every fixture ran on both sides")
expect(summary_i64("fixtures_missing")).to_equal(0)

# @req REQ-SSPEC-SYSTEM
step("pairs every Chrome node with a Simple node")
step("Read the unpaired count")
val unpaired = summary_i64("unpaired")
step("An unpairable node is a reported failure, never a silent skip")
expect(unpaired).to_equal(0)  # oracle: node correspondence is total
```

</details>

#### keeps pure block layout byte-exact against Chrome

- has fresh differential evidence produced against a real Chrome
- The summary must exist and be newer than every fixture and extractor source
   - Expected: evidence_is_stale() is false
- A real Chrome must have produced the chrome side
   - Expected: version contains `Chrome/`
- Assert a nonzero compared-node count
   - Expected: nodes > 0 is true
- Assert a nonzero compared-text-node count so stage 4 is really exercised
   - Expected: text_nodes > 0 is true
- Assert every fixture ran on both sides
   - Expected: summary_i64("fixtures_missing") equals `0`
- keeps pure block layout byte-exact against Chrome
- Read the set of fixtures with zero findings
- Block stacking, margin collapse, padding/border, box-sizing, nesting, percent widths and auto margins must stay exact
   - Expected: clean contains `01_block_stacking`
   - Expected: clean contains `02_margin_collapse`
   - Expected: clean contains `03_padding_border`
   - Expected: clean contains `04_box_sizing_border`
   - Expected: clean contains `05_nested_offsets`
   - Expected: clean contains `15_width_percent`
   - Expected: clean contains `16_margin_auto`
   - Expected: clean contains `18_nested_block_height`


<details>
<summary>Executable SSpec</summary>

Runnable source: 29 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("has fresh differential evidence produced against a real Chrome")
step("The summary must exist and be newer than every fixture and extractor source")
expect(evidence_is_stale()).to_equal(false)  # oracle: missing or stale evidence FAILS; run sh tools/layout_diff/run_layout_diff.shs
step("A real Chrome must have produced the chrome side")
val version = chrome_version()
expect(version.contains("Chrome/")).to_equal(true)  # oracle: chrome absent or extraction failed is a FAILURE, never a vacuous pass
step("Assert a nonzero compared-node count")
val nodes = summary_i64("nodes_compared")
expect(nodes > 0).to_equal(true)  # oracle: 0 mismatches over 0 nodes is not a pass
step("Assert a nonzero compared-text-node count so stage 4 is really exercised")
val text_nodes = summary_i64("text_nodes_compared")
expect(text_nodes > 0).to_equal(true)  # oracle: the line-box oracle must have run
step("Assert every fixture ran on both sides")
expect(summary_i64("fixtures_missing")).to_equal(0)

# @req REQ-SSPEC-SYSTEM
step("keeps pure block layout byte-exact against Chrome")
step("Read the set of fixtures with zero findings")
val clean = summary_value("clean_fixtures")
step("Block stacking, margin collapse, padding/border, box-sizing, nesting, percent widths and auto margins must stay exact")
expect(clean.contains("01_block_stacking")).to_equal(true)
expect(clean.contains("02_margin_collapse")).to_equal(true)
expect(clean.contains("03_padding_border")).to_equal(true)
expect(clean.contains("04_box_sizing_border")).to_equal(true)
expect(clean.contains("05_nested_offsets")).to_equal(true)
expect(clean.contains("15_width_percent")).to_equal(true)
expect(clean.contains("16_margin_auto")).to_equal(true)
expect(clean.contains("18_nested_block_height")).to_equal(true)
```

</details>

#### holds the known text and float divergences at or below the recorded baseline

- has fresh differential evidence produced against a real Chrome
- The summary must exist and be newer than every fixture and extractor source
   - Expected: evidence_is_stale() is false
- A real Chrome must have produced the chrome side
   - Expected: version contains `Chrome/`
- Assert a nonzero compared-node count
   - Expected: nodes > 0 is true
- Assert a nonzero compared-text-node count so stage 4 is really exercised
   - Expected: text_nodes > 0 is true
- Assert every fixture ran on both sides
   - Expected: summary_i64("fixtures_missing") equals `0`
- holds the known text and float divergences at or below the recorded baseline
- Read the current finding count
- Absent evidence reads as -1 and must FAIL rather than satisfy the ratchet
   - Expected: findings >= 0 is true
- Nonzero nodes must have been compared for the ratchet to mean anything
   - Expected: summary_i64("nodes_compared") > 0 is true
- The baseline measured against Chrome 151.0.7922.34 is 73 findings; this may shrink but must not grow
   - Expected: findings <= 73 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 26 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("has fresh differential evidence produced against a real Chrome")
step("The summary must exist and be newer than every fixture and extractor source")
expect(evidence_is_stale()).to_equal(false)  # oracle: missing or stale evidence FAILS; run sh tools/layout_diff/run_layout_diff.shs
step("A real Chrome must have produced the chrome side")
val version = chrome_version()
expect(version.contains("Chrome/")).to_equal(true)  # oracle: chrome absent or extraction failed is a FAILURE, never a vacuous pass
step("Assert a nonzero compared-node count")
val nodes = summary_i64("nodes_compared")
expect(nodes > 0).to_equal(true)  # oracle: 0 mismatches over 0 nodes is not a pass
step("Assert a nonzero compared-text-node count so stage 4 is really exercised")
val text_nodes = summary_i64("text_nodes_compared")
expect(text_nodes > 0).to_equal(true)  # oracle: the line-box oracle must have run
step("Assert every fixture ran on both sides")
expect(summary_i64("fixtures_missing")).to_equal(0)

# @req REQ-SSPEC-SYSTEM
step("holds the known text and float divergences at or below the recorded baseline")
step("Read the current finding count")
val findings = summary_i64("findings_total")
step("Absent evidence reads as -1 and must FAIL rather than satisfy the ratchet")
expect(findings >= 0).to_equal(true)  # oracle: missing summary is not a pass
step("Nonzero nodes must have been compared for the ratchet to mean anything")
expect(summary_i64("nodes_compared") > 0).to_equal(true)  # oracle: no vacuous ratchet
step("The baseline measured against Chrome 151.0.7922.34 is 73 findings; this may shrink but must not grow")
expect(findings <= 73).to_equal(true)  # oracle: ratchet, see tools/layout_diff/README.md
```

</details>

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

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `2ec3098f7d0b3a85be62bed62dc248df3e5696c386f4b12cccaa2737dbfc664d`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `2ec3098f7d0b3a85be62bed62dc248df3e5696c386f4b12cccaa2737dbfc664d`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `2ec3098f7d0b3a85be62bed62dc248df3e5696c386f4b12cccaa2737dbfc664d`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/browser_engine/chrome_layout_differential_spec.spl
mirror: doc/06_spec/03_system/browser_engine/chrome_layout_differential_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=90
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/browser_engine/chrome_layout_differential_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
test/03_system/browser_engine/chrome_layout_differential_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/browser_engine/chrome_layout_differential_spec.spl:121:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'has fresh differential evidence produced against a real Chrome' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/browser_engine/chrome_layout_differential_spec.spl:139:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'pairs every Chrome node with a Simple node' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/browser_engine/chrome_layout_differential_spec.spl:148:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps pure block layout byte-exact against Chrome' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

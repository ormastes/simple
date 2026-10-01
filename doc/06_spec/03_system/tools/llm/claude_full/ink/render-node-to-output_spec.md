# Claude Full Ink Render Node Slice

> Focused Simple/TUI-compatible coverage for render-node text shaping helpers from

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full Ink Render Node Slice

Focused Simple/TUI-compatible coverage for render-node text shaping helpers from

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/ink/render-node-to-output_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Focused Simple/TUI-compatible coverage for render-node text shaping helpers from
ink/render-node-to-output.ts.

## Scenarios

### Claude full ink render node parity

#### should model segment maps

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- should model segment maps
- Check char to segment map
   - Expected: buildCharToSegmentMapRoute("3") equals `0,0,0`
   - Expected: buildCharToSegmentMapRoute("2,3") equals `0,0,1,1,1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should model segment maps")
step("Check char to segment map")
expect(buildCharToSegmentMapRoute("3")).to_equal("0,0,0")
expect(buildCharToSegmentMapRoute("2,3")).to_equal("0,0,1,1,1")
```

</details>

#### should model style and hyperlink application

- should model style and hyperlink application
- Check style application
   - Expected: applyStylesToWrappedTextRoute(1, false, true) equals `styles 1 trimmed`
   - Expected: applyStylesToWrappedTextRoute(2, false, false) equals `styles 2 preserved`
   - Expected: applyStylesToWrappedTextRoute(2, true, true) equals `styles 2 hyperlink per line trimmed`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should model style and hyperlink application")
step("Check style application")
expect(applyStylesToWrappedTextRoute(1, false, true)).to_equal("styles 1 trimmed")
expect(applyStylesToWrappedTextRoute(2, false, false)).to_equal("styles 2 preserved")
expect(applyStylesToWrappedTextRoute(2, true, true)).to_equal("styles 2 hyperlink per line trimmed")
```

</details>

#### should model soft wrapping padding and empty output

- should model soft wrapping padding and empty output
- Check wrap and padding
   - Expected: wrapWithSoftWrapRoute("wrap", 2) equals `soft wraps`
   - Expected: wrapWithSoftWrapRoute("truncate", 2) equals `softWrap undefined`
   - Expected: applyPaddingToTextRoute(2, 4, 3) equals `top 2 left 4 lines 5`
   - Expected: emptyPlainTextOutputRoute("") equals `no write output`
   - Expected: emptyPlainTextOutputRoute("text") equals `write output`
   - Expected: renderNodeToOutputSourceLinesModeled() equals `1462`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should model soft wrapping padding and empty output")
step("Check wrap and padding")
expect(wrapWithSoftWrapRoute("wrap", 2)).to_equal("soft wraps")
expect(wrapWithSoftWrapRoute("truncate", 2)).to_equal("softWrap undefined")
expect(applyPaddingToTextRoute(2, 4, 3)).to_equal("top 2 left 4 lines 5")
expect(emptyPlainTextOutputRoute("")).to_equal("no write output")
expect(emptyPlainTextOutputRoute("text")).to_equal("write output")
expect(renderNodeToOutputSourceLinesModeled()).to_equal(1462)
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

- Canonical SPipe generation for source `811ea36e3af9d3ad0f0fe70b4aa1ff5d74a72944cc396dbdb60c4b67d1e464e5`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `811ea36e3af9d3ad0f0fe70b4aa1ff5d74a72944cc396dbdb60c4b67d1e464e5`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `811ea36e3af9d3ad0f0fe70b4aa1ff5d74a72944cc396dbdb60c4b67d1e464e5`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/03_system/tools/llm/claude_full/ink/render-node-to-output_spec.spl
mirror: doc/06_spec/03_system/tools/llm/claude_full/ink/render-node-to-output_spec.md (current)
findings: 9 blockers: 0
  narrative=100 structure=85 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/tools/llm/claude_full/ink/render-node-to-output_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/tools/llm/claude_full/ink/render-node-to-output_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/tools/llm/claude_full/ink/render-node-to-output_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/tools/llm/claude_full/ink/render-node-to-output_spec.spl:19:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should model segment maps' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/ink/render-node-to-output_spec.spl:19:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should model segment maps' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/ink/render-node-to-output_spec.spl:26:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should model style and hyperlink application' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/ink/render-node-to-output_spec.spl:26:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should model style and hyperlink application' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/ink/render-node-to-output_spec.spl:34:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should model soft wrapping padding and empty output' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/ink/render-node-to-output_spec.spl:34:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should model soft wrapping padding and empty output' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

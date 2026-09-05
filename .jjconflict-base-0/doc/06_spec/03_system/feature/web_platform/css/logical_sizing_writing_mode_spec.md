# CSS Logical Sizing And Writing Mode

> This bounded integer-pixel scenario proves that logical size declarations map

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# CSS Logical Sizing And Writing Mode

This bounded integer-pixel scenario proves that logical size declarations map

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/feature/web_platform/css/logical_sizing_writing_mode_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

This bounded integer-pixel scenario proves that logical size declarations map
to the physical axis selected by writing-mode before canonical Web layout,
Draw IR, and Engine2D execution.

## Scenarios

### REQ-WEB-BROWSER-003/004/021: CSS logical sizing

#### should map logical sizes through writing mode into exact pixels

**Scenario capture:** artifact after_step


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-WEB-BROWSER-003/004/021
```

</details>

#### should preserve empty cell winners while pre-resolving writing mode

- should preserve empty cell winners while pre-resolving writing mode
- Let stylesheet-important hide beat inline-normal show
- Let inline-important show beat stylesheet-important hide
   - Expected: inline_important_pixels[4 * 48 + 5] equals `0xFFEF4444u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 29 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should preserve empty cell winners while pre-resolving writing mode")
step("Let stylesheet-important hide beat inline-normal show")
val stylesheet_important = _logical_document(
    "table{width:40px;background:#dbeafe}" +
    "td{display:block;width:20px;height:8px;background:#ef4444;" +
    "empty-cells:hide!important}",
    "<table><tr><td id='box' style='empty-cells:show'></td></tr></table>"
)
val stylesheet_important_pixels = _logical_pixels(
    stylesheet_important
)
expect(stylesheet_important.composition.batches[0].source.source_kind).to_equal(
    "html_ast"
)
expect(stylesheet_important_pixels[4 * 48 + 5]).to_equal(
    0xFFDBEAFEu32
)

step("Let inline-important show beat stylesheet-important hide")
val inline_important = _logical_document(
    "table{width:40px;background:#dbeafe}" +
    "td{display:block;width:20px;height:8px;background:#ef4444;" +
    "empty-cells:hide!important}",
    "<table><tr><td id='box' " +
    "style='empty-cells:show!important'></td></tr></table>"
)
val inline_important_pixels = _logical_pixels(inline_important)
expect(inline_important_pixels[4 * 48 + 5]).to_equal(0xFFEF4444u32)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
- `REQ-WEB-BROWSER-003/004/021`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `823494a7685de0875668d14d367b99ed070c06e593ee79b73bb21ec961207859`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `823494a7685de0875668d14d367b99ed070c06e593ee79b73bb21ec961207859`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `823494a7685de0875668d14d367b99ed070c06e593ee79b73bb21ec961207859`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/feature/web_platform/css/logical_sizing_writing_mode_spec.spl
mirror: doc/06_spec/03_system/feature/web_platform/css/logical_sizing_writing_mode_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=80 oracle=100
  traceability=100 evidence=90 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/feature/web_platform/css/logical_sizing_writing_mode_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/feature/web_platform/css/logical_sizing_writing_mode_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/feature/web_platform/css/logical_sizing_writing_mode_spec.spl:71:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'should map logical sizes through writing mode into exact pixels' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/03_system/feature/web_platform/css/logical_sizing_writing_mode_spec.spl:71:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should map logical sizes through writing mode into exact pixels' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/feature/web_platform/css/logical_sizing_writing_mode_spec.spl:190:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should preserve empty cell winners while pre-resolving writing mode' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/feature/web_platform/css/logical_sizing_writing_mode_spec.spl:190:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should preserve empty cell winners while pre-resolving writing mode' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

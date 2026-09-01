# RenderDoc Log Compare

> Purpose: Prove that RenderDoc render-log compare.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# RenderDoc Log Compare

Purpose: Prove that RenderDoc render-log compare.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/renderdoc/renderdoc_log_compare_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Prove that RenderDoc render-log compare.
Audience: compiler and tooling engineers who maintain this spec.

## Scenarios

### RenderDoc render-log compare

#### should report zero findings for identical command logs

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- Compare two identical three-command logs
   - Expected: result.equal is true
   - Expected: result.findings.len() equals `0`
   - Expected: result.aligned_count equals `3`
   - Expected: result.missing_count equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-COMMON-001
step("Compare two identical three-command logs")
val result = compare_render_logs(baseline_record("gui-widget"), baseline_record("chrome-web"))
expect(result.equal).to_equal(true)
expect(result.findings.len()).to_equal(0)  # oracle: 0 — named expected value from the requirement
expect(result.aligned_count).to_equal(3)  # oracle: 3 — named expected value from the requirement
expect(result.missing_count).to_equal(0)  # oracle: 0 — named expected value from the requirement
```

</details>

#### should name a missing draw as missing_call

- should name a missing draw as missing_call
- Drop the indexed draw from the actual log
   - Expected: result.equal is false
   - Expected: result.missing_count equals `1`
   - Expected: result.extra_count equals `0`
   - Expected: result.findings.len() equals `1`
   - Expected: result.findings[0].finding_class equals `missing_call`
   - Expected: result.findings[0].call equals `vkCmdDrawIndexed`
   - Expected: result.findings[0].kind equals `draw`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should name a missing draw as missing_call")
step("Drop the indexed draw from the actual log")
val expected = baseline_record("gui-widget")
val actual = record_of("chrome-web", [
    cmd_fields("000", "bind", "vkCmdBindPipeline", ["pipeline=7"]),
    cmd_fields("001", "draw", "vkCmdDraw", ["vertex_count=6", "instance_count=1"])
])
val result = compare_render_logs(expected, actual)
expect(result.equal).to_equal(false)
expect(result.missing_count).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(result.extra_count).to_equal(0)  # oracle: 0 — named expected value from the requirement
expect(result.findings.len()).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(result.findings[0].finding_class).to_equal("missing_call")
expect(result.findings[0].call).to_equal("vkCmdDrawIndexed")
expect(result.findings[0].kind).to_equal("draw")
```

</details>

#### should classify a changed parameter as param_drift naming the field

- should classify a changed parameter as param_drift naming the field
- Change vertex_count on the plain draw
   - Expected: result.drift_count equals `1`
   - Expected: result.missing_count equals `0`
   - Expected: result.extra_count equals `0`
   - Expected: drift_detail contains `vertex_count`
   - Expected: drift_detail does not contain `instance_count`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should classify a changed parameter as param_drift naming the field")
step("Change vertex_count on the plain draw")
val expected = baseline_record("gui-widget")
val actual = record_of("chrome-web", [
    cmd_fields("000", "bind", "vkCmdBindPipeline", ["pipeline=7"]),
    cmd_fields("001", "draw", "vkCmdDraw", ["vertex_count=4", "instance_count=1"]),
    cmd_fields("002", "draw", "vkCmdDrawIndexed", ["index_count=36", "instance_count=1"])
])
val result = compare_render_logs(expected, actual)
expect(result.drift_count).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(result.missing_count).to_equal(0)  # oracle: 0 — named expected value from the requirement
expect(result.extra_count).to_equal(0)  # oracle: 0 — named expected value from the requirement
var drift_detail = ""
for finding in result.findings:
    if finding.finding_class == "param_drift":
        drift_detail = finding.detail
expect(drift_detail.contains("vertex_count")).to_equal(true)
expect(drift_detail.contains("instance_count")).to_equal(false)
```

</details>

#### should detect swapped call order as order_swap

- should detect swapped call order as order_swap
- Swap the two draws in the actual log
   - Expected: result.swap_count > 0 is true
   - Expected: result.missing_count equals `0`
   - Expected: result.extra_count equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should detect swapped call order as order_swap")
step("Swap the two draws in the actual log")
val expected = baseline_record("gui-widget")
val actual = record_of("chrome-web", [
    cmd_fields("000", "bind", "vkCmdBindPipeline", ["pipeline=7"]),
    cmd_fields("001", "draw", "vkCmdDrawIndexed", ["index_count=36", "instance_count=1"]),
    cmd_fields("002", "draw", "vkCmdDraw", ["vertex_count=6", "instance_count=1"])
])
val result = compare_render_logs(expected, actual)
expect(result.swap_count > 0).to_equal(true)
expect(result.missing_count).to_equal(0)  # oracle: 0 — named expected value from the requirement
expect(result.extra_count).to_equal(0)  # oracle: 0 — named expected value from the requirement
```

</details>

#### should adapt RenderDoc replay XML chunks into command field paths

- should adapt RenderDoc replay XML chunks into command field paths
- Feed a small synthetic RDC-XML fragment to the adapter
   - Expected: fields.len() equals `7`
   - Expected: fields[0].path equals `commands.000.call`
   - Expected: fields[0].value equals `vkCreateShaderModule`
   - Expected: fields[1].path equals `commands.000.kind`
   - Expected: fields[1].value equals `resource`
   - Expected: fields[3].value equals `bind`
   - Expected: fields[4].path equals `commands.002.call`
   - Expected: fields[4].value equals `vkCmdDraw`
   - Expected: fields[6].path equals `commands.count`
   - Expected: fields[6].value equals `3`
- Round-trip through a record and extraction
   - Expected: calls.len() equals `3`
   - Expected: calls[2].kind equals `draw`


<details>
<summary>Executable SSpec</summary>

Runnable source: 26 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should adapt RenderDoc replay XML chunks into command field paths")
step("Feed a small synthetic RDC-XML fragment to the adapter")
val xml = "<rdc><chunks version=\"1\">" +
    "<chunk name=\"vkCreateShaderModule\"></chunk>" +
    "<chunk name=\"vkCmdBindPipeline\"></chunk>" +
    "<chunk name=\"vkCmdDraw\"></chunk>" +
    "<chunk name=\"vkQueueSubmit\"></chunk>" +
    "</chunks></rdc>"
val fields = renderdoc_xml_command_fields(xml)
# 3 relevant chunks x 2 fields + commands.count; vkQueueSubmit skipped.
expect(fields.len()).to_equal(7)  # oracle: 7 — named expected value from the requirement
expect(fields[0].path).to_equal("commands.000.call")
expect(fields[0].value).to_equal("vkCreateShaderModule")
expect(fields[1].path).to_equal("commands.000.kind")
expect(fields[1].value).to_equal("resource")
expect(fields[3].value).to_equal("bind")
expect(fields[4].path).to_equal("commands.002.call")
expect(fields[4].value).to_equal("vkCmdDraw")
expect(fields[6].path).to_equal("commands.count")
expect(fields[6].value).to_equal("3")
step("Round-trip through a record and extraction")
val record = renderdoc_xml_to_record(xml, "renderdoc-replay")
val calls = extract_render_calls(record)
expect(calls.len()).to_equal(3)  # oracle: 3 — named expected value from the requirement
expect(calls[2].kind).to_equal("draw")
```

</details>

#### should render a text report with counts and detailed findings

- should render a text report with counts and detailed findings
- Compare chrome-web vs gui with one missing draw
   - Expected: report contains `MISMATCH`
   - Expected: report contains `missing_call=1`
   - Expected: report contains `vkCmdDrawIndexed`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should render a text report with counts and detailed findings")
step("Compare chrome-web vs gui with one missing draw")
val gui = baseline_record("gui-widget")
val web = record_of("chrome-web", [
    cmd_fields("000", "bind", "vkCmdBindPipeline", ["pipeline=7"]),
    cmd_fields("001", "draw", "vkCmdDraw", ["vertex_count=6", "instance_count=1"])
])
val result = compare_chrome_web_vs_gui(gui, web)
val report = render_log_compare_report(result, 5)
expect(report.contains("MISMATCH")).to_equal(true)
expect(report.contains("missing_call=1")).to_equal(true)
expect(report.contains("vkCmdDrawIndexed")).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
- `REQ-LIB-COMMON-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `d66c695472f52a357f311c7532df7469e04beb3052341331a21849ed976cfdbb`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `d66c695472f52a357f311c7532df7469e04beb3052341331a21849ed976cfdbb`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `d66c695472f52a357f311c7532df7469e04beb3052341331a21849ed976cfdbb`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/01_unit/lib/common/renderdoc/renderdoc_log_compare_spec.spl
mirror: doc/06_spec/01_unit/lib/common/renderdoc/renderdoc_log_compare_spec.md (current)
findings: 11 blockers: 0
  narrative=100 structure=70 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/common/renderdoc/renderdoc_log_compare_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/renderdoc/renderdoc_log_compare_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/renderdoc/renderdoc_log_compare_spec.spl:63:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should report zero findings for identical command logs' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/lib/common/renderdoc/renderdoc_log_compare_spec.spl:63:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should report zero findings for identical command logs' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/renderdoc/renderdoc_log_compare_spec.spl:72:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should name a missing draw as missing_call' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/lib/common/renderdoc/renderdoc_log_compare_spec.spl:72:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should name a missing draw as missing_call' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/renderdoc/renderdoc_log_compare_spec.spl:90:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should classify a changed parameter as param_drift naming the field' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/lib/common/renderdoc/renderdoc_log_compare_spec.spl:90:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should classify a changed parameter as param_drift naming the field' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/renderdoc/renderdoc_log_compare_spec.spl:111:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should detect swapped call order as order_swap' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/lib/common/renderdoc/renderdoc_log_compare_spec.spl:126:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should adapt RenderDoc replay XML chunks into command field paths' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/lib/common/renderdoc/renderdoc_log_compare_spec.spl:154:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should render a text report with counts and detailed findings' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->

# RenderDoc Replay XML Inspection

> Validates capture-content parsing independently from a local RenderDoc install.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# RenderDoc Replay XML Inspection

Validates capture-content parsing independently from a local RenderDoc install.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/renderdoc_replay_inspect_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Validates capture-content parsing independently from a local RenderDoc install.

## Scenarios

### RenderDoc replay XML inspection

#### should accept Vulkan actions pipeline shaders and resources

- should accept Vulkan actions pipeline shaders and resources
- Parse a converted Vulkan capture
   - Expected: result.status equals `pass`
   - Expected: result.driver equals `vulkan`
   - Expected: result.relevant_action_count equals `1`
   - Expected: result.pipeline_count equals `1`
   - Expected: result.shader_count equals `1`
   - Expected: result.resource_count equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("should accept Vulkan actions pipeline shaders and resources")
step("Parse a converted Vulkan capture")
val result = parse_renderdoc_capture_xml(valid_xml(), "capture.rdc", "capture.xml", 0, "")
expect(result.status).to_equal("pass")
expect(result.driver).to_equal("vulkan")
expect(result.relevant_action_count).to_equal(1)
expect(result.pipeline_count).to_equal(1)
expect(result.shader_count).to_equal(1)
expect(result.resource_count).to_equal(1)
```

</details>

#### should retain replay and owner agreement evidence

- should retain replay and owner agreement evidence


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("should retain replay and owner agreement evidence")
val result = parse_renderdoc_capture_xml(
    valid_xml(), "capture.rdc", "capture.xml", 0, "")
val evidence = renderdoc_replay_evidence_text(
    result, "vulkan", "frame-7", "frame-7")
expect(evidence).to_contain("rdoc_simple_replay_status=pass")
expect(evidence).to_contain("rdoc_simple_replay_driver=vulkan")
expect(evidence).to_contain("rdoc_simple_replay_capture_path=capture.rdc")
expect(evidence).to_contain("rdoc_simple_replay_xml_hash=")
expect(evidence).to_contain("rdoc_simple_replay_relevant_action_count=1")
expect(evidence).to_contain("rdoc_simple_owner_agreement_status=pass")
expect(evidence).to_contain("rdoc_simple_owner_frame_id=frame-7")
expect(evidence).to_contain("rdoc_simple_capture_frame_id=frame-7")
```

</details>

<details>
<summary>Advanced: should reject magic or text without RenderDoc XML structure</summary>

#### should reject magic or text without RenderDoc XML structure

- should reject magic or text without RenderDoc XML structure
- Parse a magic-only synthetic capture conversion
   - Expected: parse_renderdoc_capture_xml("RDOCsynthetic", "fake.rdc", "fake.xml", 0, "").reason equals `invalid-renderdoc-xml`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("should reject magic or text without RenderDoc XML structure")
step("Parse a magic-only synthetic capture conversion")
expect(parse_renderdoc_capture_xml("RDOCsynthetic", "fake.rdc", "fake.xml", 0, "").reason).to_equal("invalid-renderdoc-xml")
```

</details>


</details>

<details>
<summary>Advanced: should reject conversion failure</summary>

#### should reject conversion failure

- should reject conversion failure
- Report a nonzero RenderDoc conversion result
   - Expected: parse_renderdoc_capture_xml("", "bad.rdc", "bad.xml", 2, "open failed").reason equals `capture-open-failed`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("should reject conversion failure")
step("Report a nonzero RenderDoc conversion result")
expect(parse_renderdoc_capture_xml("", "bad.rdc", "bad.xml", 2, "open failed").reason).to_equal("capture-open-failed")
```

</details>


</details>

<details>
<summary>Advanced: should reject captures without relevant rendering actions</summary>

#### should reject captures without relevant rendering actions

- should reject captures without relevant rendering actions
- Remove draw and dispatch actions
   - Expected: parse_renderdoc_capture_xml(xml, "empty.rdc", "empty.xml", 0, "").reason equals `missing-relevant-actions`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("should reject captures without relevant rendering actions")
step("Remove draw and dispatch actions")
val xml = valid_xml().replace("<chunk name=\"vkCmdDispatch\"></chunk>", "")
expect(parse_renderdoc_capture_xml(xml, "empty.rdc", "empty.xml", 0, "").reason).to_equal("missing-relevant-actions")
```

</details>


</details>

#### should reject command names outside RenderDoc chunk records

- should reject command names outside RenderDoc chunk records
- Place action and resource names only in metadata
   - Expected: parse_renderdoc_capture_xml(xml, "metadata.rdc", "metadata.xml", 0, "").reason equals `missing-relevant-actions`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("should reject command names outside RenderDoc chunk records")
step("Place action and resource names only in metadata")
val xml = "<?xml version=\"1.0\"?><rdc><header><driver id=\"8\">Vulkan</driver></header><chunks version=\"32\">" +
    "<chunk name=\"marker\"><metadata name=\"vkCmdDispatch\">vkCreateComputePipelines vkCreateShaderModule vkCreateBuffer</metadata></chunk>" +
    "</chunks></rdc>"
expect(parse_renderdoc_capture_xml(xml, "metadata.rdc", "metadata.xml", 0, "").reason).to_equal("missing-relevant-actions")
```

</details>

#### should trust only one driver inside the RenderDoc header

- should trust only one driver inside the RenderDoc header
- Place a conflicting Vulkan driver inside capture metadata
   - Expected: parsed.driver equals `d3d12`
- Reject missing and duplicate authoritative driver records


<details>
<summary>Executable SSpec</summary>

Runnable source: 31 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("should trust only one driver inside the RenderDoc header")
step("Place a conflicting Vulkan driver inside capture metadata")
val spoofed = valid_xml().replace(
    "<driver id=\"8\">Vulkan</driver>",
    "<driver id=\"1\">D3D12</driver>"
).replace(
    "</chunks>",
    "<chunk name=\"marker\"><metadata><driver>Vulkan</driver></metadata></chunk></chunks>"
)
val parsed = parse_renderdoc_capture_xml(
    spoofed, "spoofed.rdc", "spoofed.xml", 0, ""
)
expect(parsed.driver).to_equal("d3d12")
expect(validate_renderdoc_owner_agreement(
    parsed, "vulkan", "frame-1", "frame-1"
)).to_equal("capture-record-mismatch")

step("Reject missing and duplicate authoritative driver records")
val missing = valid_xml().replace(
    "<driver id=\"8\">Vulkan</driver>", ""
)
expect(parse_renderdoc_capture_xml(
    missing, "missing.rdc", "missing.xml", 0, ""
).reason).to_equal("unsupported-capture-driver")
val duplicate = valid_xml().replace(
    "</header>", "<driver id=\"1\">D3D12</driver></header>"
)
expect(parse_renderdoc_capture_xml(
    duplicate, "duplicate.rdc", "duplicate.xml", 0, ""
).reason).to_equal("unsupported-capture-driver")
```

</details>

<details>
<summary>Advanced: should reject captures without pipeline evidence</summary>

#### should reject captures without pipeline evidence

- should reject captures without pipeline evidence
- Remove pipeline creation
   - Expected: parse_renderdoc_capture_xml(xml, "no-pipeline.rdc", "no-pipeline.xml", 0, "").reason equals `missing-pipeline-evidence`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("should reject captures without pipeline evidence")
step("Remove pipeline creation")
val xml = valid_xml().replace("<chunk name=\"vkCreateComputePipelines\"></chunk>", "")
expect(parse_renderdoc_capture_xml(xml, "no-pipeline.rdc", "no-pipeline.xml", 0, "").reason).to_equal("missing-pipeline-evidence")
```

</details>


</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
- `REQ-009`
- `REQ-SSPEC-APP`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `cdfcec80ba4414cd99351961e56c8b2dc0da40eae705e150fd9e17df1231e15b`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `cdfcec80ba4414cd99351961e56c8b2dc0da40eae705e150fd9e17df1231e15b`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `cdfcec80ba4414cd99351961e56c8b2dc0da40eae705e150fd9e17df1231e15b`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **80/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/app/renderdoc_replay_inspect_spec.spl
mirror: doc/06_spec/01_unit/app/renderdoc_replay_inspect_spec.md (current)
findings: 10 blockers: 1
  narrative=100 structure=70 oracle=70
  traceability=60 evidence=100 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=80; blocker cap makes effective=49
doc/06_spec/01_unit/app/renderdoc_replay_inspect_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/renderdoc_replay_inspect_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/renderdoc_replay_inspect_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 4 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/app/renderdoc_replay_inspect_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 2 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/app/renderdoc_replay_inspect_spec.spl:32:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should accept Vulkan actions pipeline shaders and resources' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/app/renderdoc_replay_inspect_spec.spl:44:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should retain replay and owner agreement evidence' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/app/renderdoc_replay_inspect_spec.spl:61:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should reject magic or text without RenderDoc XML structure' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/app/renderdoc_replay_inspect_spec.spl:68:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should reject conversion failure' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/app/renderdoc_replay_inspect_spec.spl:75:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should reject captures without relevant rendering actions' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/app/renderdoc_replay_inspect_spec.spl:82:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should reject command names outside RenderDoc chunk records' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->

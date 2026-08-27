# RenderDoc Capture Replay Inspection

> Opens real captures through the canonical Simple helper and rejects magic-only,

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# RenderDoc Capture Replay Inspection

Opens real captures through the canonical Simple helper and rejects magic-only,

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/check/renderdoc_capture_replay_inspection_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Opens real captures through the canonical Simple helper and rejects magic-only,
synthetic, corrupt, or content-inconsistent artifacts. Replay identity comes
only from one driver record inside the authoritative capture header.

## Scenarios

### RenderDoc capture replay inspection

#### should open a real capture or retain the exact host blocker

- should open a real capture or retain the exact host blocker
   - Log capture: after_step
- Resolve the retained Simple Vulkan capture artifact
   - Log capture: after_step
- Open and replay the capture through the Simple inspector
   - Log capture: after_step
- Validate API device relevant actions and frame identity
   - Log capture: after_step
   - Evidence: log output verified by 2 expected checks
   - Expected: inspection.driver equals `vulkan`
   - Expected: validate_renderdoc_owner_agreement(inspection, "vulkan", "frame-1", "frame-1") equals `pass`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should open a real capture or retain the exact host blocker")
step("Resolve the retained Simple Vulkan capture artifact")
val capture_path = "build/renderdoc-vulkan-capture/simple_gui.rdc"
step("Open and replay the capture through the Simple inspector")
val inspection = inspect_renderdoc_capture(
    renderdoc_command_path(), capture_path,
    "build/test-renderdoc-replay-inspection/live", 120000)
step("Validate API device relevant actions and frame identity")
if inspection.status == "pass":
    expect(inspection.driver).to_equal("vulkan")
    expect(inspection.relevant_action_count).to_be_greater_than(0)
    expect(validate_renderdoc_owner_agreement(inspection, "vulkan", "frame-1", "frame-1")).to_equal("pass")
else:
    expect(["renderdoccmd-missing", "capture-missing", "capture-open-failed"]).to_contain(inspection.reason)
```

</details>

<details>
<summary>Advanced: should reject a four-byte magic-only file</summary>

#### should reject a four-byte magic-only file

- should reject a four-byte magic-only file
- Inspect a file containing RDOC without capture contents
   - Expected: inspection.reason equals `capture-too-small`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should reject a four-byte magic-only file")
step("Inspect a file containing RDOC without capture contents")
val root = "build/test-renderdoc-replay-inspection/magic-only"
dir_create_all(root)
val capture_path = root + "/magic.rdc"
expect(file_write(capture_path, "RDOC")).to_be(true)
val inspection = inspect_renderdoc_capture("/bin/false", capture_path, root + "/out", 1000)
expect(inspection.reason).to_equal("capture-too-small")
```

</details>


</details>

<details>
<summary>Advanced: should reject synthetic and corrupt capture artifacts</summary>

#### should reject synthetic and corrupt capture artifacts

- should reject synthetic and corrupt capture artifacts
- Inspect synthetic and truncated artifacts
   - Expected: opened.reason equals `capture-open-failed`
   - Expected: parsed.reason equals `invalid-renderdoc-xml`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should reject synthetic and corrupt capture artifacts")
step("Inspect synthetic and truncated artifacts")
val root = "build/test-renderdoc-replay-inspection/corrupt"
dir_create_all(root)
val capture_path = root + "/synthetic.rdc"
expect(file_write(capture_path, "RDOCsynthetic")).to_be(true)
val opened = inspect_renderdoc_capture("/bin/false", capture_path, root + "/out", 1000)
expect(opened.reason).to_equal("capture-open-failed")
val parsed = parse_renderdoc_capture_xml("RDOCsynthetic", capture_path, root + "/bad.xml", 0, "")
expect(parsed.reason).to_equal("invalid-renderdoc-xml")
```

</details>


</details>

#### should reject action names that appear only in capture metadata

- should reject action names that appear only in capture metadata
- Parse structured XML with no action chunk
   - Expected: parsed.reason equals `missing-relevant-actions`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should reject action names that appear only in capture metadata")
step("Parse structured XML with no action chunk")
val xml = "<?xml version=\"1.0\"?><rdc><header><driver id=\"8\">Vulkan</driver></header><chunks version=\"32\">" +
    "<chunk name=\"marker\"><metadata name=\"vkCmdDispatch\">vkCreateComputePipelines vkCreateShaderModule vkCreateBuffer</metadata></chunk>" +
    "</chunks></rdc>"
val parsed = parse_renderdoc_capture_xml(xml, "metadata.rdc", "metadata.xml", 0, "")
expect(parsed.reason).to_equal("missing-relevant-actions")
```

</details>

#### should reject a metadata driver that disagrees with the capture header

- should reject a metadata driver that disagrees with the capture header
- Parse a D3D12 header with a Vulkan driver nested in metadata
   - Expected: parsed.driver equals `d3d12`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should reject a metadata driver that disagrees with the capture header")
step("Parse a D3D12 header with a Vulkan driver nested in metadata")
val xml = valid_vulkan_xml().replace(
    "<driver id=\"8\">Vulkan</driver>",
    "<driver id=\"1\">D3D12</driver>"
).replace(
    "</chunks>",
    "<chunk name=\"marker\"><metadata><driver>Vulkan</driver></metadata></chunk></chunks>"
)
val parsed = parse_renderdoc_capture_xml(
    xml, "spoofed.rdc", "spoofed.xml", 0, ""
)
expect(parsed.driver).to_equal("d3d12")
expect(validate_renderdoc_owner_agreement(
    parsed, "vulkan", "frame-1", "frame-1"
)).to_equal("capture-record-mismatch")
```

</details>

<details>
<summary>Advanced: should reject capture and owner-record disagreement</summary>

#### should reject capture and owner-record disagreement

- should reject capture and owner-record disagreement
- Pair the capture with a different API or frame record
   - Expected: inspection.status equals `pass`
   - Expected: validate_renderdoc_owner_agreement(inspection, "d3d12", "frame-1", "frame-1") equals `capture-record-mismatch`
   - Expected: validate_renderdoc_owner_agreement(inspection, "vulkan", "frame-1", "frame-2") equals `capture-record-mismatch`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should reject capture and owner-record disagreement")
step("Pair the capture with a different API or frame record")
val inspection = parse_renderdoc_capture_xml(valid_vulkan_xml(), "capture.rdc", "capture.xml", 0, "")
expect(inspection.status).to_equal("pass")
expect(validate_renderdoc_owner_agreement(inspection, "d3d12", "frame-1", "frame-1")).to_equal("capture-record-mismatch")
expect(validate_renderdoc_owner_agreement(inspection, "vulkan", "frame-1", "frame-2")).to_equal("capture-record-mismatch")
```

</details>


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

- `REQ-SSPEC-SYSTEM`
- `REQ-009`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `6127fbc2bbf672bd5ef615e2c982e21293cbc183e099be2b0c4cb2d3be5990dd`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `6127fbc2bbf672bd5ef615e2c982e21293cbc183e099be2b0c4cb2d3be5990dd`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `6127fbc2bbf672bd5ef615e2c982e21293cbc183e099be2b0c4cb2d3be5990dd`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/03_system/check/renderdoc_capture_replay_inspection_spec.spl
mirror: doc/06_spec/03_system/check/renderdoc_capture_replay_inspection_spec.md (current)
findings: 9 blockers: 1
  narrative=100 structure=70 oracle=100
  traceability=60 evidence=100 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=86; blocker cap makes effective=49
doc/06_spec/03_system/check/renderdoc_capture_replay_inspection_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/check/renderdoc_capture_replay_inspection_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/check/renderdoc_capture_replay_inspection_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 1 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/03_system/check/renderdoc_capture_replay_inspection_spec.spl:44:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should open a real capture or retain the exact host blocker' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/check/renderdoc_capture_replay_inspection_spec.spl:62:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should reject a four-byte magic-only file' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/check/renderdoc_capture_replay_inspection_spec.spl:74:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should reject synthetic and corrupt capture artifacts' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/check/renderdoc_capture_replay_inspection_spec.spl:87:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should reject action names that appear only in capture metadata' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/check/renderdoc_capture_replay_inspection_spec.spl:97:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should reject a metadata driver that disagrees with the capture header' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/check/renderdoc_capture_replay_inspection_spec.spl:117:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should reject capture and owner-record disagreement' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->

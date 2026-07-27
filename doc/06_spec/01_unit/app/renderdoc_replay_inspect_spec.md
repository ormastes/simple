# Renderdoc Replay Inspect Specification

> <details>

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Renderdoc Replay Inspect Specification

## Scenarios

### RenderDoc replay XML inspection

#### should accept Vulkan actions pipeline shaders and resources

- Parse a converted Vulkan capture
   - Expected: result.status equals `pass`
   - Expected: result.driver equals `vulkan`
   - Expected: result.relevant_action_count equals `1`
   - Expected: result.pipeline_count equals `1`
   - Expected: result.shader_count equals `1`
   - Expected: result.resource_count equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

- valid xml


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

- Parse a magic-only synthetic capture conversion
   - Expected: parse_renderdoc_capture_xml("RDOCsynthetic", "fake.rdc", "fake.xml", 0, "").reason equals `invalid-renderdoc-xml`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Parse a magic-only synthetic capture conversion")
expect(parse_renderdoc_capture_xml("RDOCsynthetic", "fake.rdc", "fake.xml", 0, "").reason).to_equal("invalid-renderdoc-xml")
```

</details>


</details>

<details>
<summary>Advanced: should reject conversion failure</summary>

#### should reject conversion failure

- Report a nonzero RenderDoc conversion result
   - Expected: parse_renderdoc_capture_xml("", "bad.rdc", "bad.xml", 2, "open failed").reason equals `capture-open-failed`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Report a nonzero RenderDoc conversion result")
expect(parse_renderdoc_capture_xml("", "bad.rdc", "bad.xml", 2, "open failed").reason).to_equal("capture-open-failed")
```

</details>


</details>

<details>
<summary>Advanced: should reject captures without relevant rendering actions</summary>

#### should reject captures without relevant rendering actions

- Remove draw and dispatch actions
   - Expected: parse_renderdoc_capture_xml(xml, "empty.rdc", "empty.xml", 0, "").reason equals `missing-relevant-actions`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Remove draw and dispatch actions")
val xml = valid_xml().replace("<chunk name=\"vkCmdDispatch\"></chunk>", "")
expect(parse_renderdoc_capture_xml(xml, "empty.rdc", "empty.xml", 0, "").reason).to_equal("missing-relevant-actions")
```

</details>


</details>

#### should reject command names outside RenderDoc chunk records

- Place action and resource names only in metadata
   - Expected: parse_renderdoc_capture_xml(xml, "metadata.rdc", "metadata.xml", 0, "").reason equals `missing-relevant-actions`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Place action and resource names only in metadata")
val xml = "<?xml version=\"1.0\"?><rdc><header><driver id=\"8\">Vulkan</driver></header><chunks version=\"32\">" +
    "<chunk name=\"marker\"><metadata name=\"vkCmdDispatch\">vkCreateComputePipelines vkCreateShaderModule vkCreateBuffer</metadata></chunk>" +
    "</chunks></rdc>"
expect(parse_renderdoc_capture_xml(xml, "metadata.rdc", "metadata.xml", 0, "").reason).to_equal("missing-relevant-actions")
```

</details>

<details>
<summary>Advanced: should reject captures without pipeline evidence</summary>

#### should trust only one driver inside the RenderDoc header

- Place a conflicting Vulkan driver inside capture metadata.
- Keep the authoritative D3D12 header identity and reject Vulkan owner
  agreement.
- Reject missing and duplicate authoritative driver records.

#### should reject captures without pipeline evidence

- Remove pipeline creation
   - Expected: parse_renderdoc_capture_xml(xml, "no-pipeline.rdc", "no-pipeline.xml", 0, "").reason equals `missing-pipeline-evidence`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Remove pipeline creation")
val xml = valid_xml().replace("<chunk name=\"vkCreateComputePipelines\"></chunk>", "")
expect(parse_renderdoc_capture_xml(xml, "no-pipeline.rdc", "no-pipeline.xml", 0, "").reason).to_equal("missing-pipeline-evidence")
```

</details>


</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/renderdoc_replay_inspect_spec.spl` |
| Updated | 2026-07-27 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- RenderDoc replay XML inspection

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

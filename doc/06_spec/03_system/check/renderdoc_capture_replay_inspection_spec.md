# Renderdoc Capture Replay Inspection Specification

> <details>

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Renderdoc Capture Replay Inspection Specification

## Scenarios

### RenderDoc capture replay inspection

#### should open a real capture or retain the exact host blocker

- Resolve the retained Simple Vulkan capture artifact
   - Log capture: after_step
- Open and replay the capture through the Simple inspector
   - Log capture: after_step
- renderdoc command path
   - Log capture: after_step
- Validate API device relevant actions and frame identity
   - Log capture: after_step
   - Evidence: log output verified by 2 expected checks
   - Expected: inspection.driver equals `vulkan`
   - Expected: validate_renderdoc_owner_agreement(inspection, "vulkan", "frame-1", "frame-1") equals `pass`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

- Inspect a file containing RDOC without capture contents
- dir create all
   - Expected: inspection.reason equals `capture-too-small`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

- Inspect synthetic and truncated artifacts
- dir create all
   - Expected: opened.reason equals `capture-open-failed`
   - Expected: parsed.reason equals `invalid-renderdoc-xml`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

- Parse structured XML with no action chunk
   - Expected: parsed.reason equals `missing-relevant-actions`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Parse structured XML with no action chunk")
val xml = "<?xml version=\"1.0\"?><rdc><header><driver id=\"8\">Vulkan</driver></header><chunks version=\"32\">" +
    "<chunk name=\"marker\"><metadata name=\"vkCmdDispatch\">vkCreateComputePipelines vkCreateShaderModule vkCreateBuffer</metadata></chunk>" +
    "</chunks></rdc>"
val parsed = parse_renderdoc_capture_xml(xml, "metadata.rdc", "metadata.xml", 0, "")
expect(parsed.reason).to_equal("missing-relevant-actions")
```

</details>

<details>
<summary>Advanced: should reject capture and owner-record disagreement</summary>

#### should reject a metadata driver that disagrees with the capture header

- Parse a D3D12 header with a Vulkan driver nested in metadata.
- Preserve D3D12 replay identity and reject Vulkan owner agreement.

#### should reject capture and owner-record disagreement

- Pair the capture with a different API or frame record
   - Expected: inspection.status equals `pass`
   - Expected: validate_renderdoc_owner_agreement(inspection, "d3d12", "frame-1", "frame-1") equals `capture-record-mismatch`
   - Expected: validate_renderdoc_owner_agreement(inspection, "vulkan", "frame-1", "frame-2") equals `capture-record-mismatch`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Pair the capture with a different API or frame record")
val inspection = parse_renderdoc_capture_xml(valid_vulkan_xml(), "capture.rdc", "capture.xml", 0, "")
expect(inspection.status).to_equal("pass")
expect(validate_renderdoc_owner_agreement(inspection, "d3d12", "frame-1", "frame-1")).to_equal("capture-record-mismatch")
expect(validate_renderdoc_owner_agreement(inspection, "vulkan", "frame-1", "frame-2")).to_equal("capture-record-mismatch")
```

</details>


</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/check/renderdoc_capture_replay_inspection_spec.spl` |
| Updated | 2026-07-27 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- RenderDoc capture replay inspection

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

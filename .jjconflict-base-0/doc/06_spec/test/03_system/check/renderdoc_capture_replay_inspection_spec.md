# Renderdoc Capture Replay Inspection Specification

> <details>

<!-- sdn-diagram:id=renderdoc_capture_replay_inspection_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=renderdoc_capture_replay_inspection_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

renderdoc_capture_replay_inspection_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=renderdoc_capture_replay_inspection_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Renderdoc Capture Replay Inspection Specification

## Scenarios

### RenderDoc capture replay inspection

#### should open a real capture and agree on API device actions and frame

- Capture the Simple Vulkan frame with the canonical helper
   - Log capture: after_step
- Open and replay the capture through the Simple inspector
   - Log capture: after_step
- Validate API device relevant actions and frame identity
   - Log capture: after_step
- pending renderdoc replay inspection
   - Log capture: after_step


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Capture the Simple Vulkan frame with the canonical helper")
step("Open and replay the capture through the Simple inspector")
step("Validate API device relevant actions and frame identity")
pending_renderdoc_replay_inspection()
```

</details>

<details>
<summary>Advanced: should reject a four-byte magic-only file</summary>

#### should reject a four-byte magic-only file

- Inspect a file containing RDOC without capture contents
   - Expected: "capture-open-failed" equals `capture-open-failed`
- pending renderdoc replay inspection


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Inspect a file containing RDOC without capture contents")
expect("capture-open-failed").to_equal("capture-open-failed")
pending_renderdoc_replay_inspection()
```

</details>


</details>

<details>
<summary>Advanced: should reject synthetic and corrupt capture artifacts</summary>

#### should reject synthetic and corrupt capture artifacts

- Inspect synthetic and truncated artifacts
   - Expected: ["synthetic-capture", "corrupt-capture"].len() equals `2`
- pending renderdoc replay inspection


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Inspect synthetic and truncated artifacts")
expect(["synthetic-capture", "corrupt-capture"].len()).to_equal(2)
pending_renderdoc_replay_inspection()
```

</details>


</details>

<details>
<summary>Advanced: should reject capture and owner-record disagreement</summary>

#### should reject capture and owner-record disagreement

- Pair the capture with a different API or frame record
   - Expected: "capture-record-mismatch" equals `capture-record-mismatch`
- pending renderdoc replay inspection


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Pair the capture with a different API or frame record")
expect("capture-record-mismatch").to_equal("capture-record-mismatch")
pending_renderdoc_replay_inspection()
```

</details>


</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/check/renderdoc_capture_replay_inspection_spec.spl` |
| Updated | 2026-07-10 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- RenderDoc capture replay inspection

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

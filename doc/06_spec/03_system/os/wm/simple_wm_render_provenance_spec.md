# Simple Wm Render Provenance Specification

> <details>

<!-- sdn-diagram:id=simple_wm_render_provenance_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=simple_wm_render_provenance_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

simple_wm_render_provenance_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=simple_wm_render_provenance_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Simple Wm Render Provenance Specification

## Scenarios

### Simple WM shared render provenance

#### should render revision-matched shared windows and chrome through production backends

- Launch the production WM in a host window
   - Artifact capture: after_step
- Create multiple internal windows with distinct runtime content
   - Artifact capture: after_step
- Focus drag minimize restore maximize and restore internal windows
   - Artifact capture: after_step
- Verify the shared taskbar and top title lane follow the scene objects
   - Artifact capture: after_step
- Capture the host frame with Simple GUI Web and 2D producer metadata
   - Artifact capture: after_step
- Boot SimpleOS into its framebuffer desktop
   - Artifact capture: after_step
- Repeat the same internal window and taskbar interactions in SimpleOS
   - Artifact capture: after_step
- Capture the SimpleOS framebuffer with matching producer metadata
   - Artifact capture: after_step
- Compare semantic pixels scene content frame and capture revisions
   - Artifact capture: after_step
- Verify both production entrypoints render the shared scene and chrome
   - Artifact capture: after_step
- Verify every captured frame matches its scene content and producer revisions
   - Artifact capture: after_step


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Launch the production WM in a host window")
step("Create multiple internal windows with distinct runtime content")
step("Focus drag minimize restore maximize and restore internal windows")
step("Verify the shared taskbar and top title lane follow the scene objects")
step("Capture the host frame with Simple GUI Web and 2D producer metadata")
step("Boot SimpleOS into its framebuffer desktop")
step("Repeat the same internal window and taskbar interactions in SimpleOS")
step("Capture the SimpleOS framebuffer with matching producer metadata")
step("Compare semantic pixels scene content frame and capture revisions")
require_production_shared_scene_render()
require_matching_scene_content_and_capture_revisions()
```

</details>

<details>
<summary>Advanced: should reject stale missing duplicate or wrong-window content frames</summary>

#### should reject stale missing duplicate or wrong-window content frames

- Submit content frames that do not match the common scene revision
   - Protocol capture: after_step
- Validate captured pixels and backend provenance
   - Protocol capture: after_step
- require matching scene content and capture revisions
   - Protocol capture: after_step


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Submit content frames that do not match the common scene revision")
step("Validate captured pixels and backend provenance")
require_matching_scene_content_and_capture_revisions()
```

</details>


</details>

<details>
<summary>Advanced: should render arbitrary long and Unicode titles without canned text branches</summary>

#### should render arbitrary long and Unicode titles without canned text branches

- Create a runtime window titled 문서 편집기 — Résumé Δ dashboard with a deliberately long suffix
   - GUI capture: after_step (HTML preferred when available)
- Replace its Simple Web content with arbitrary runtime-created text
   - GUI capture: after_step (HTML preferred when available)
- Validate captured pixels and backend provenance
   - GUI capture: after_step (HTML preferred when available)
- require runtime created arbitrary text render
   - GUI capture: after_step (HTML preferred when available)
- require matching scene content and capture revisions
   - GUI capture: after_step (HTML preferred when available)


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Create a runtime window titled 문서 편집기 — Résumé Δ dashboard with a deliberately long suffix")
step("Replace its Simple Web content with arbitrary runtime-created text")
step("Validate captured pixels and backend provenance")
require_runtime_created_arbitrary_text_render()
require_matching_scene_content_and_capture_revisions()
```

</details>


</details>

<details>
<summary>Advanced: should follow physical viewport and scale events across the NFR-8 matrix</summary>

#### should follow physical viewport and scale events across the NFR-8 matrix

- Resize the physical surface through 1280x720 1920x1080 3840x2160 and 7680x4320
   - GUI capture: after_step (HTML preferred when available)
- Apply physical scales 1.0 1.5 2.0 and 3.0
   - GUI capture: after_step (HTML preferred when available)
- Validate captured pixels and backend provenance
   - GUI capture: after_step (HTML preferred when available)
- require physical resize scale layout matrix
   - GUI capture: after_step (HTML preferred when available)


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Resize the physical surface through 1280x720 1920x1080 3840x2160 and 7680x4320")
step("Apply physical scales 1.0 1.5 2.0 and 3.0")
step("Validate captured pixels and backend provenance")
require_physical_resize_scale_layout_matrix()
```

</details>


</details>

<details>
<summary>Advanced: should fail closed when provenance or semantic render evidence is unverifiable</summary>

#### should fail closed when provenance or semantic render evidence is unverifiable

- Remove producer identity backend revision or verified capture metadata
- Validate captured pixels and backend provenance
- require matching scene content and capture revisions


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Remove producer identity backend revision or verified capture metadata")
step("Validate captured pixels and backend provenance")
require_matching_scene_content_and_capture_revisions()
```

</details>


</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/03_system/os/wm/simple_wm_render_provenance_spec.spl` |
| Updated | 2026-07-11 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Simple WM shared render provenance

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

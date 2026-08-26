# Simple WM Render Provenance

> Proves that host and SimpleOS render the same revision-correlated production

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Simple WM Render Provenance

Proves that host and SimpleOS render the same revision-correlated production

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/03_system/os/wm/simple_wm_render_provenance_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Proves that host and SimpleOS render the same revision-correlated production
scene through Simple GUI, Simple Web, and the backend-neutral Simple 2D path.
The operator flow rejects canned text, stale content, fabricated captures, and
layout results that do not follow physical viewport and scale events.

## Scenarios

### Simple WM shared render provenance

#### render revision-matched shared windows and chrome through production backends

- render revision-matched shared windows and chrome through production backends
   - Artifact capture: after_step
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

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("render revision-matched shared windows and chrome through production backends")
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
<summary>Advanced: reject stale missing duplicate or wrong-window content frames</summary>

#### reject stale missing duplicate or wrong-window content frames

- reject stale missing duplicate or wrong-window content frames
   - Protocol capture: after_step
- Submit content frames that do not match the common scene revision
   - Protocol capture: after_step
- Validate captured pixels and backend provenance
   - Protocol capture: after_step


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("reject stale missing duplicate or wrong-window content frames")
step("Submit content frames that do not match the common scene revision")
step("Validate captured pixels and backend provenance")
require_matching_scene_content_and_capture_revisions()
```

</details>


</details>

<details>
<summary>Advanced: render arbitrary long and Unicode titles without canned text branches</summary>

#### render arbitrary long and Unicode titles without canned text branches

- render arbitrary long and Unicode titles without canned text branches
   - GUI capture: after_step (HTML preferred when available)
- Create a runtime window titled 문서 편집기 — Résumé Δ dashboard with a deliberately long suffix
   - GUI capture: after_step (HTML preferred when available)
- Replace its Simple Web content with arbitrary runtime-created text
   - GUI capture: after_step (HTML preferred when available)
- Validate captured pixels and backend provenance
   - GUI capture: after_step (HTML preferred when available)


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("render arbitrary long and Unicode titles without canned text branches")
step("Create a runtime window titled 문서 편집기 — Résumé Δ dashboard with a deliberately long suffix")
step("Replace its Simple Web content with arbitrary runtime-created text")
step("Validate captured pixels and backend provenance")
require_runtime_created_arbitrary_text_render()
require_matching_scene_content_and_capture_revisions()
```

</details>


</details>

<details>
<summary>Advanced: follow physical viewport and scale events across the NFR-8 matrix</summary>

#### follow physical viewport and scale events across the NFR-8 matrix

- follow physical viewport and scale events across the NFR-8 matrix
   - GUI capture: after_step (HTML preferred when available)
- Resize the physical surface through 1280x720 1920x1080 3840x2160 and 7680x4320
   - GUI capture: after_step (HTML preferred when available)
- Apply physical scales 1.0 1.5 2.0 and 3.0
   - GUI capture: after_step (HTML preferred when available)
- Validate captured pixels and backend provenance
   - GUI capture: after_step (HTML preferred when available)


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("follow physical viewport and scale events across the NFR-8 matrix")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
step("Resize the physical surface through 1280x720 1920x1080 3840x2160 and 7680x4320")
step("Apply physical scales 1.0 1.5 2.0 and 3.0")
step("Validate captured pixels and backend provenance")
require_physical_resize_scale_layout_matrix()
```

</details>


</details>

<details>
<summary>Advanced: fail closed when provenance or semantic render evidence is unverifiable</summary>

#### fail closed when provenance or semantic render evidence is unverifiable

- fail closed when provenance or semantic render evidence is unverifiable
- Remove producer identity backend revision or verified capture metadata
- Validate captured pixels and backend provenance


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("fail closed when provenance or semantic render evidence is unverifiable")
step("Remove producer identity backend revision or verified capture metadata")
step("Validate captured pixels and backend provenance")
require_matching_scene_content_and_capture_revisions()
```

</details>


</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
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

- Canonical SPipe generation for source `65182862860e566d6674a3844445390f6fb0f96893fc0aa5be066115e8023958`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `65182862860e566d6674a3844445390f6fb0f96893fc0aa5be066115e8023958`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `65182862860e566d6674a3844445390f6fb0f96893fc0aa5be066115e8023958`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **87/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/03_system/os/wm/simple_wm_render_provenance_spec.spl
mirror: doc/06_spec/03_system/os/wm/simple_wm_render_provenance_spec.md (current)
findings: 3 blockers: 1
  narrative=100 structure=100 oracle=50
  traceability=100 evidence=100 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=87; blocker cap makes effective=49
doc/06_spec/03_system/os/wm/simple_wm_render_provenance_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/os/wm/simple_wm_render_provenance_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/os/wm/simple_wm_render_provenance_spec.spl:1:1: blocker SSDOC-ORA-001 [oracle] (-50): no real executed assertion or compiler oracle
  why: A passing-looking document without an oracle is not conformance evidence.
  improve: Replace placeholders with an observable production assertion.
<!-- sspec-maintain:scorecard:end -->

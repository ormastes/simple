# Shell Baremetal Backend Specification

> Tests covering baremetal shared WM backend contract.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Shell Baremetal Backend Specification

## Scenarios

### baremetal shared WM backend contract

#### renders a live rich scene through CompositorBackend

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- renders a live rich scene through CompositorBackend
   - Expected: backend.clear_count equals `1`
   - Expected: backend.present_count equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("renders a live rich scene through CompositorBackend")
var backend = _capture_backend()
val window = simple_gui_internal_window(
    "surface-41", "41", 7001u64, "editor", "Live Editor",
    80, 70, 420, 300, "document=notes.spl", false, true, 0
)
val scene = simple_gui_internal_window_scene(800, 600, "simpleos-compositor", [window])
val pixels = _solid_pixels(412 * 264, 0xFF102030u32)
val frame = WmContentFrame(window_id: "41", scene_revision: 7, content_revision: 3, origin_kind: WM_CONTENT_ORIGIN_SIMPLE_WEB, width: 412, height: 264, pixels: pixels, checksum: wm_content_frame_checksum(pixels), parent_window_id: "", offset_x: 0, offset_y: 0)
render_baremetal_shared_wm_scene(backend, scene, empty_taskbar_model(), [frame], 7, 9, "12:34")

expect(backend.clear_count).to_equal(1)
expect(backend.fill_count > 0).to_be(true)
expect(backend.text_count > 0).to_be(true)
expect(backend.present_count).to_equal(0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/unit/os/desktop/shell_baremetal_backend_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering baremetal shared WM backend contract.
- baremetal shared WM backend contract

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `b03e6351825a1b9999710f862ae0474ce1998f1e47c94eaa18d8b1073fed384e`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `b03e6351825a1b9999710f862ae0474ce1998f1e47c94eaa18d8b1073fed384e`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `b03e6351825a1b9999710f862ae0474ce1998f1e47c94eaa18d8b1073fed384e`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **93/100**; effective score: **93/100**; blockers: **0**.

SSpec documentization score: 93/100
source: test/unit/os/desktop/shell_baremetal_backend_spec.spl
mirror: doc/06_spec/unit/os/desktop/shell_baremetal_backend_spec.md (current)
findings: 3 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=100 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/os/desktop/shell_baremetal_backend_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/os/desktop/shell_baremetal_backend_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/os/desktop/shell_baremetal_backend_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
<!-- sspec-maintain:scorecard:end -->

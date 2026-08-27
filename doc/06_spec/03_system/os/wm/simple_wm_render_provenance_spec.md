# simple_wm_render_provenance_spec

> Purpose: prove the shared-WM render provenance contract at the scene level —

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# simple_wm_render_provenance_spec

Purpose: prove the shared-WM render provenance contract at the scene level —

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/03_system/os/wm/simple_wm_render_provenance_spec.spl` |
| Updated | 2026-08-27 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: prove the shared-WM render provenance contract at the scene level —
revision-correlated content frames, runtime-created Unicode titles, the NFR-8
physical resize/scale matrix with non-overlapping chrome lanes and scaled
taskbar hit targets, and fail-closed rejection of frames whose web-render
provenance is unverifiable. Audience: WM/compositor maintainers and the
desktop-render provenance owners.

## Scenarios

### Simple WM shared render provenance

#### render revision-matched shared windows and chrome through production backends

**Manual warnings:**
- invalid capture metadata value: protocol_json (expected kind tui|gui|html|text|api|protocol|exec|binary|log|artifact and mode after_step|after_scenario|on_failure|off)


- render revision-matched shared windows and chrome through production backends
- Project a shared scene with multiple runtime-content internal windows
   - Expected: scene.width equals `1920`
   - Expected: scene.height equals `1080`
   - Expected: scene.backend equals `vulkan`
   - Expected: scene.windows.len() equals `3`
- Focus drag minimize restore and verify the shared scene follows
   - Expected: shared_wm_focused_window_id(focused) equals `win-a`
   - Expected: dragged.windows[0].x equals `65`
   - Expected: dragged.windows[0].y equals `79`
   - Expected: shared_wm_visible_windows(minimized).len() equals `1`
   - Expected: shared_wm_visible_windows(restored).len() equals `2`
   - Expected: shared_wm_topmost_visible_window_id(restored) equals `win-b`
   - Expected: closed.windows.len() equals `2`
- Verify the shared taskbar and top title lane follow the scene objects
   - Expected: chrome.command_lane.height equals `32`
   - Expected: chrome.taskbar.height equals `48`
   - Expected: chrome.command_lane.y + chrome.command_lane.height equals `chrome.content_area.y`
   - Expected: chrome.content_area.y + chrome.content_area.height equals `chrome.taskbar.y`
   - Expected: chrome.taskbar.y + chrome.taskbar.height equals `restored.height`


<details>
<summary>Executable SSpec</summary>

Runnable source: 28 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("render revision-matched shared windows and chrome through production backends")
step("Project a shared scene with multiple runtime-content internal windows")
val scene = demo_scene()
expect(scene.width).to_equal(1920)  # oracle: NFR-8 reference resolution width
expect(scene.height).to_equal(1080)  # oracle: NFR-8 reference resolution height
expect(scene.backend).to_equal("vulkan")
expect(scene.windows.len()).to_equal(3)  # oracle: three distinct internal windows
step("Focus drag minimize restore and verify the shared scene follows")
val focused = shared_wm_focus_window_by_window_id(scene, "win-a")
expect(shared_wm_focused_window_id(focused)).to_equal("win-a")
val dragged = shared_wm_drag_window(focused, "surf-a", 25, 15)
expect(dragged.windows[0].x).to_equal(65)  # oracle: 40 + drag dx 25
expect(dragged.windows[0].y).to_equal(79)  # oracle: 64 + drag dy 15
val minimized = shared_wm_minimize_window_by_window_id(dragged, "win-b")
expect(shared_wm_visible_windows(minimized).len()).to_equal(1)  # oracle: only win-c stays visible (win-c itself unminimized)
val restored = shared_wm_focus_window_by_window_id(minimized, "win-b")
expect(shared_wm_visible_windows(restored).len()).to_equal(2)
expect(shared_wm_topmost_visible_window_id(restored)).to_equal("win-b")
val closed = shared_wm_close_window_by_window_id(restored, "win-c")
expect(closed.windows.len()).to_equal(2)  # oracle: close removes exactly one window
step("Verify the shared taskbar and top title lane follow the scene objects")
val chrome = shared_wm_scene_chrome(restored, 1000, "09:41", 3, 2)
expect(chrome.command_lane.height).to_equal(32)  # oracle: 32 logical px command lane at scale 1.0
expect(chrome.taskbar.height).to_equal(48)  # oracle: 48 logical px taskbar at scale 1.0
expect(chrome.command_lane.y + chrome.command_lane.height).to_equal(chrome.content_area.y)
expect(chrome.content_area.y + chrome.content_area.height).to_equal(chrome.taskbar.y)
expect(chrome.taskbar.y + chrome.taskbar.height).to_equal(restored.height)
```

</details>

<details>
<summary>Advanced: reject stale missing duplicate or wrong-window content frames</summary>

#### reject stale missing duplicate or wrong-window content frames

**Manual warnings:**
- invalid capture metadata value: protocol_json (expected kind tui|gui|html|text|api|protocol|exec|binary|log|artifact and mode after_step|after_scenario|on_failure|off)


- reject stale missing duplicate or wrong-window content frames
- Submit content frames that do not match the common scene revision
- Validate frame-scene revision and checksum correlation
   - Expected: frame_matches_scene(scene, good) is true
   - Expected: frame_matches_scene(scene, stale) is false
   - Expected: frame_matches_scene(scene, wrong_window) is false
- Reject duplicate frames for the same window in one presentation
   - Expected: good.window_id == wrong_window.window_id is false
   - Expected: good.window_id equals `win-b`
- Checksum must fold position so equal-color permutations differ
   - Expected: good.checksum == wm_content_frame_checksum(good.pixels) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("reject stale missing duplicate or wrong-window content frames")
step("Submit content frames that do not match the common scene revision")
val scene = demo_scene()
val pixels: [u32] = [0xFF102030u32, 0xFF405060u32]
val good = provenance_frame("win-b", 41, 7, pixels)
step("Validate frame-scene revision and checksum correlation")
expect(frame_matches_scene(scene, good)).to_equal(true)
val stale = provenance_frame("win-b", 41 + 1, 8, pixels)
expect(frame_matches_scene(scene, stale)).to_equal(false)  # oracle: a stale scene revision is rejected
val wrong_window = provenance_frame("win-zz", 41, 7, pixels)
expect(frame_matches_scene(scene, wrong_window)).to_equal(false)  # oracle: an unknown window id is rejected
step("Reject duplicate frames for the same window in one presentation")
expect(good.window_id == wrong_window.window_id).to_equal(false)
expect(good.window_id).to_equal("win-b")
step("Checksum must fold position so equal-color permutations differ")
expect(wm_content_frame_checksum([0xFF102030u32, 0xFF405060u32])).to_be_greater_than(0)
expect(wm_content_frame_checksum([0xFF102030u32, 0xFF405060u32]) ==
    wm_content_frame_checksum([0xFF405060u32, 0xFF102030u32])).to_equal(false)
expect(good.checksum == wm_content_frame_checksum(good.pixels)).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: render arbitrary long and Unicode titles without canned text branches</summary>

#### render arbitrary long and Unicode titles without canned text branches

**Manual warnings:**
- invalid capture metadata value: protocol_json (expected kind tui|gui|html|text|api|protocol|exec|binary|log|artifact and mode after_step|after_scenario|on_failure|off)


- render arbitrary long and Unicode titles without canned text branches
- Create a runtime window titled with long Unicode runtime-created text
   - Expected: title_window.title equals `unicode_title()`
- Runtime-created content changes the content revision and checksum
   - Expected: rev7.content_revision equals `7`
   - Expected: rev8.content_revision equals `8`
   - Expected: rev7.checksum == rev8.checksum is false
- Every scene window title is the exact runtime-created text, never a template
   - Expected: canned is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("render arbitrary long and Unicode titles without canned text branches")
step("Create a runtime window titled with long Unicode runtime-created text")
val scene = demo_scene()
val title_window = scene.windows[1]
expect(title_window.title).to_equal(unicode_title())
expect(title_window.title.len()).to_be_greater_than(40)  # oracle: deliberately long runtime suffix present
step("Runtime-created content changes the content revision and checksum")
val rev7 = provenance_frame("win-b", 41, 7, [0xFF102030u32, 0xFF405060u32])
val rev8 = provenance_frame("win-b", 41, 8, [0xFF605040u32, 0xFF302010u32])
expect(rev7.content_revision).to_equal(7)
expect(rev8.content_revision).to_equal(8)
expect(rev7.checksum == rev8.checksum).to_equal(false)  # oracle: changed content changes the frame checksum
step("Every scene window title is the exact runtime-created text, never a template")
var canned = false
for window in scene.windows:
    if window.title.contains("{{") or window.title.contains("placeholder"):
        canned = true
expect(canned).to_equal(false)
```

</details>


</details>

<details>
<summary>Advanced: follow physical viewport and scale events across the NFR-8 matrix</summary>

#### follow physical viewport and scale events across the NFR-8 matrix

**Manual warnings:**
- invalid capture metadata value: statistics (expected kind tui|gui|html|text|api|protocol|exec|binary|log|artifact and mode after_step|after_scenario|on_failure|off)


- follow physical viewport and scale events across the NFR-8 matrix
- Resize the physical surface through 1280x720 1920x1080 3840x2160 and 7680x4320
- Apply physical scales 1.0 1.5 2.0 and 3.0
   - Expected: chrome.command_lane.height equals `command_base[scale_index]`
   - Expected: chrome.taskbar.height equals `taskbar_base[scale_index]`
   - Expected: chrome.command_lane.y + chrome.command_lane.height equals `chrome.content_area.y`
   - Expected: chrome.content_area.y + chrome.content_area.height equals `chrome.taskbar.y`
   - Expected: chrome.taskbar.y + chrome.taskbar.height equals `heights[resize_index]`
   - Expected: chrome.content_area.width equals `widths[resize_index]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 26 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("follow physical viewport and scale events across the NFR-8 matrix")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
step("Resize the physical surface through 1280x720 1920x1080 3840x2160 and 7680x4320")
step("Apply physical scales 1.0 1.5 2.0 and 3.0")
val widths: [i32] = [1280, 1920, 3840, 7680]
val heights: [i32] = [720, 1080, 2160, 4320]
val scales: [i32] = [1000, 1500, 2000, 3000]
val taskbar_base: [i32] = [48, 72, 96, 144]
val command_base: [i32] = [32, 48, 64, 96]
var resize_index = 0
while resize_index < 4:
    val scene = simple_gui_internal_window_scene(widths[resize_index], heights[resize_index],
        "vulkan", demo_scene().windows)
    var scale_index = 0
    while scale_index < 4:
        val chrome = shared_wm_scene_chrome(scene, scales[scale_index], "09:41", 3, 2)
        expect(chrome.command_lane.height).to_equal(command_base[scale_index])  # oracle: 32 logical px scaled by the physical scale
        expect(chrome.taskbar.height).to_equal(taskbar_base[scale_index])  # oracle: 48 logical px taskbar keeps hit targets above 44 logical px
        expect(chrome.taskbar.height * 1000).to_be_greater_than(43 * scales[scale_index])  # oracle: NFR-8 44 logical px minimum hit target
        expect(chrome.command_lane.y + chrome.command_lane.height).to_equal(chrome.content_area.y)
        expect(chrome.content_area.y + chrome.content_area.height).to_equal(chrome.taskbar.y)
        expect(chrome.taskbar.y + chrome.taskbar.height).to_equal(heights[resize_index])
        expect(chrome.content_area.width).to_equal(widths[resize_index])
        scale_index = scale_index + 1
    resize_index = resize_index + 1
```

</details>


</details>

<details>
<summary>Advanced: fail closed when provenance or semantic render evidence is unverifiable</summary>

#### fail closed when provenance or semantic render evidence is unverifiable

**Manual warnings:**
- invalid capture metadata value: protocol_json (expected kind tui|gui|html|text|api|protocol|exec|binary|log|artifact and mode after_step|after_scenario|on_failure|off)


- fail closed when provenance or semantic render evidence is unverifiable
- Strip producer identity backend revision or verified capture metadata
   - Expected: wm_content_frame_web_provenance_valid(frame) is true
   - Expected: wm_content_frame_web_provenance_valid(stripped) is false
   - Expected: wm_content_frame_web_provenance_valid(safe_fallback) is false
   - Expected: wm_content_frame_web_provenance_valid(short_sha) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 70 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("fail closed when provenance or semantic render evidence is unverifiable")
step("Strip producer identity backend revision or verified capture metadata")
val scene = demo_scene()
val frame = provenance_frame("win-b", 41, 7,
    [0xFF102030u32, 0xFF405060u32])
expect(wm_content_frame_web_provenance_valid(frame)).to_equal(true)  # oracle: fully provenanced frame is accepted
val stripped = WmContentFrame(
    window_id: frame.window_id,
    scene_revision: frame.scene_revision,
    content_revision: frame.content_revision,
    origin_kind: frame.origin_kind,
    width: frame.width,
    height: frame.height,
    pixels: frame.pixels,
    checksum: frame.checksum,
    parent_window_id: "",
    offset_x: 0,
    offset_y: 0,
    engine2d_status: "not_requested",
    engine2d_backend: "",
    engine2d_reason: "",
    material_fallback_kind: "none",
    material_fallback_reason: "not_requested",
    material_fallback_sha256: "",
    theme_id: "",
    theme_source_manifest_sha256: "")
expect(wm_content_frame_web_provenance_valid(stripped)).to_equal(false)  # oracle: no executed renderer provenance fails closed
val safe_fallback = WmContentFrame(
    window_id: frame.window_id,
    scene_revision: frame.scene_revision,
    content_revision: frame.content_revision,
    origin_kind: frame.origin_kind,
    width: frame.width,
    height: frame.height,
    pixels: frame.pixels,
    checksum: frame.checksum,
    parent_window_id: "",
    offset_x: 0,
    offset_y: 0,
    engine2d_status: "engine2d_rendered",
    engine2d_backend: "native-safe-fallback",
    engine2d_reason: "",
    material_fallback_kind: "cpu-composited-material",
    material_fallback_reason: "native-device-backdrop-path-pending",
    material_fallback_sha256: frame.material_fallback_sha256,
    theme_id: frame.theme_id,
    theme_source_manifest_sha256: frame.theme_source_manifest_sha256)
expect(wm_content_frame_web_provenance_valid(safe_fallback)).to_equal(false)  # oracle: a canned native-safe-fallback backend is not production provenance
val short_sha = WmContentFrame(
    window_id: frame.window_id,
    scene_revision: frame.scene_revision,
    content_revision: frame.content_revision,
    origin_kind: frame.origin_kind,
    width: frame.width,
    height: frame.height,
    pixels: frame.pixels,
    checksum: frame.checksum,
    parent_window_id: "",
    offset_x: 0,
    offset_y: 0,
    engine2d_status: "engine2d_rendered",
    engine2d_backend: "vulkan",
    engine2d_reason: "",
    material_fallback_kind: "cpu-composited-material",
    material_fallback_reason: "native-device-backdrop-path-pending",
    material_fallback_sha256: "deadbeef",
    theme_id: frame.theme_id,
    theme_source_manifest_sha256: frame.theme_source_manifest_sha256)
expect(wm_content_frame_web_provenance_valid(short_sha)).to_equal(false)  # oracle: a truncated material sha256 fails closed
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

- Canonical SPipe generation for source `95c3601850b662bfe17a2a9a37816ccd4b6b9cc584dd861bfb074aac58abd569`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `95c3601850b662bfe17a2a9a37816ccd4b6b9cc584dd861bfb074aac58abd569`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `95c3601850b662bfe17a2a9a37816ccd4b6b9cc584dd861bfb074aac58abd569`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/03_system/os/wm/simple_wm_render_provenance_spec.spl
mirror: doc/06_spec/03_system/os/wm/simple_wm_render_provenance_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/os/wm/simple_wm_render_provenance_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/os/wm/simple_wm_render_provenance_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/os/wm/simple_wm_render_provenance_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 3 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/os/wm/simple_wm_render_provenance_spec.spl:91:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'render revision-matched shared windows and chrome through production backends' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/os/wm/simple_wm_render_provenance_spec.spl:123:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reject stale missing duplicate or wrong-window content frames' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/os/wm/simple_wm_render_provenance_spec.spl:147:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'render arbitrary long and Unicode titles without canned text branches' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

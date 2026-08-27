# SimpleOS WM behavior and visual evidence

> This specification separates two evidence classes that must never substitute

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# SimpleOS WM behavior and visual evidence

This specification separates two evidence classes that must never substitute

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/03_system/os/wm/simpleos_wm_behavior_evidence_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

This specification separates two evidence classes that must never substitute
for one another:

- `host-fixture` exercises the production WM owner, compositor, input router,
  Draw IR/Engine2D scene projection, and framebuffer-shaped pixel buffer;
- `live-guest` invokes the canonical QEMU wrapper and accepts only correlated
  guest input, scene, presentation, readback, and QMP artifacts.

A passing host fixture cannot promote a missing live guest.  Missing QEMU,
firmware, admitted pure-Simple artifacts, readback, or input correlation ends
with the exact `BLOCKED[REQ-017-LIVE-GUEST]` result.

## Evidence

Display policy: `links`

| Category | Count |
|----------|------:|
| Screenshots | 4 |

### Screenshots

| Item | Kind | Path |
|------|------|------|
| `{baseline` | Screenshot | ``build/test-simpleos-wm-hardening-behavior/{baseline` |
| `fullscreen` | Screenshot | `fullscreen` |
| `restored` | Screenshot | `restored` |
| `browser-event}.ppm`` | Screenshot | `browser-event}.ppm`` |

## Scenarios

### REQ-017 host-fixture WM behavior

#### should keep focus order and choose the next stack-top window after close

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


**Scenario capture:** protocol after_step


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-017
# @req REQ-017-LIVE-GUEST
```

</details>

#### should bound damage geometry count generation and scene revision

- should bound damage geometry count generation and scene revision
   - Protocol capture: after_step
- Admit one current bounded damage rectangle
   - Protocol capture: after_step
   - Evidence: protocol response verified by 2 expected checks
   - Expected: accepted.rects.len() equals `1`
   - Expected: accepted.rects[0].width equals `80`
- Reject stale and invalid damage before it reaches presentation
   - Protocol capture: after_step
- Clip and coalesce overlapping exposure before presentation
   - Protocol capture: after_step
   - Evidence: protocol response verified by 3 expected checks
   - Expected: clipped.len() equals `1`
   - Expected: clipped[0].x equals `0`
   - Expected: clipped[0].width equals `40`


<details>
<summary>Executable SSpec</summary>

Runnable source: 38 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should bound damage geometry count generation and scene revision")
step("Admit one current bounded damage rectangle")
val current = WmDamageRegionV1(
    generation: 7u64,
    scene_revision: 9u64,
    full_redraw: false,
    reason: "input",
    rects: [WmDamageRectV1(x: 12, y: 14, width: 80, height: 60)]
)
val accepted = wm_damage_admit_v1(current, 7u64, 9u64)
expect(accepted.accepted).to_be(true)
expect(accepted.rects.len()).to_equal(1)
expect(accepted.rects[0].width).to_equal(80)

step("Reject stale and invalid damage before it reaches presentation")
expect(wm_damage_admit_v1(current, 8u64, 9u64).reason).to_equal(
    "stale-damage-generation")
val invalid = WmDamageRegionV1(
    generation: 7u64,
    scene_revision: 9u64,
    full_redraw: false,
    reason: "input",
    rects: [WmDamageRectV1(x: 0, y: 0, width: 0, height: 60)]
)
expect(wm_damage_admit_v1(invalid, 7u64, 9u64).reason).to_equal(
    "invalid-damage-geometry")

step("Clip and coalesce overlapping exposure before presentation")
val clipped = wm_damage_merge_rects_v1(
    [WmDamageRectV1(x: -10, y: 5, width: 30, height: 20)],
    [WmDamageRectV1(x: 20, y: 5, width: 30, height: 20)],
    40,
    30
)
expect(clipped.len()).to_equal(1)
expect(clipped[0].x).to_equal(0)
expect(clipped[0].width).to_equal(40)
```

</details>

#### should route committed input only through the focused production window

- should route committed input only through the focused production window
   - Protocol capture: after_step
- Create two compositor windows and one canonical client UI session
   - Protocol capture: after_step
- Send committed text through both routes while B is focused
   - Protocol capture: after_step
- Focus A through the compositor and prove routing changes owner
   - Protocol capture: after_step
- Reject adapter-bypass input at the canonical WM owner
   - Protocol capture: after_step
   - Evidence: protocol response verified by 3 expected checks
   - Expected: wm.last_rejection_reason equals `unfocused-input-window`
   - Expected: wm.last_input_sequence equals `0u64`
   - Expected: wm.last_input_sequence equals `1u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 35 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should route committed input only through the focused production window")
step("Create two compositor windows and one canonical client UI session")
var compositor = HostCompositor.new_headless(Size.wh(640, 600))
val window_a = add_colored_window(compositor, 1, "Window A", 20, 20, COLOR_A)
val window_b = add_colored_window(compositor, 2, "Window B", 160, 160, COLOR_B)
var router_a = HostGuiEventRouter.new(window_a)
var router_b = HostGuiEventRouter.new(window_b)
var session = ui_session()

step("Send committed text through both routes while B is focused")
var event = window_event_none()
event.kind = WINDOW_EVENT_TEXT
expect(router_b.route(event, compositor, session, "focused")).to_be(true)
expect(router_a.route(event, compositor, session, "wrong-target")).to_be(false)

step("Focus A through the compositor and prove routing changes owner")
compositor.handle_mouse_move(30, 60)
compositor.handle_left_button(true)
compositor.handle_left_button(false)
expect(router_a.route(event, compositor, session, "refocused")).to_be(true)
expect(router_b.route(event, compositor, session, "stale-target")).to_be(false)

step("Reject adapter-bypass input at the canonical WM owner")
val wm = WmService.new()
wm.register_window_owner(WindowId(value: 41u64), 410u64)
wm.register_window_owner(WindowId(value: 42u64), 420u64)
val bypass = WmInputEvent.mouse_move(WindowId(value: 42u64), Point.xy(3, 4))
expect(wm.accept_next_input_ingress(42u64, bypass)).to_be(false)
expect(wm.last_rejection_reason).to_equal("unfocused-input-window")
expect(wm.last_input_sequence).to_equal(0u64)
val focused = WmInputEvent.mouse_move(WindowId(value: 41u64), Point.xy(3, 4))
expect(wm.accept_next_input_ingress(41u64, focused)).to_be(true)
expect(wm.last_input_sequence).to_equal(1u64)
expect(wm.complete_input_ingress()).to_be(true)
```

</details>

#### should compose z-order into pixels and preserve it across damage-only redraw

- should compose z-order into pixels and preserve it across damage-only redraw
   - Protocol capture: after_step
- Create two overlapping windows with distinct runtime pixels
   - Protocol capture: after_step
- Damage only the lower window without changing z-order
   - Protocol capture: after_step
- Focus A and prove the composited overlap pixel follows it
   - Protocol capture: after_step


<details>
<summary>Executable SSpec</summary>

Runnable source: 32 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should compose z-order into pixels and preserve it across damage-only redraw")
step("Create two overlapping windows with distinct runtime pixels")
var compositor = HostCompositor.new_headless(Size.wh(640, 600))
val window_a = add_colored_window(compositor, 1, "Window A", 20, 20, COLOR_A)
add_colored_window(compositor, 2, "Window B", 160, 160, COLOR_B)
compositor.render_frame()
val overlap_x = 220
val overlap_y = 230
expect(pixel_at(
    compositor.pure_simple_pixel_buffer(), compositor.width, overlap_x, overlap_y
)).to_equal(COLOR_B)

step("Damage only the lower window without changing z-order")
val replacement = pixel_surface_content_frame(
    "{window_a}", "", 0, 0, 292, 264,
    solid_pixels(292, 264, COLOR_A), 3, 3
)
expect(compositor.set_external_web_frame(window_a, replacement)).to_be(true)
compositor.render_frame()
expect(pixel_at(
    compositor.pure_simple_pixel_buffer(), compositor.width, overlap_x, overlap_y
)).to_equal(COLOR_B)

step("Focus A and prove the composited overlap pixel follows it")
compositor.handle_mouse_move(30, 60)
compositor.handle_left_button(true)
compositor.handle_left_button(false)
compositor.render_frame()
expect(pixel_at(
    compositor.pure_simple_pixel_buffer(), compositor.width, overlap_x, overlap_y
)).to_equal(COLOR_A)
```

</details>

#### should fence stale input and presentation receipts after recovery

- should fence stale input and presentation receipts after recovery
   - Protocol capture: after_step
- Commit one generation-correlated input and framebuffer presentation
   - Protocol capture: after_step
- Restart the owner and reject all old-generation work
   - Protocol capture: after_step
   - Evidence: protocol response verified by 3 expected checks
   - Expected: wm.restart() equals `1u64`
   - Expected: wm.last_rejection_reason equals `stale-lifecycle-generation`
   - Expected: wm.last_presented_frame_id equals `0u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should fence stale input and presentation receipts after recovery")
step("Commit one generation-correlated input and framebuffer presentation")
val wm = WmService.new()
wm.register_window_owner(WindowId(value: 8u64), 8u64)
val generation = wm.generation_value()
val revision = wm.scene_revision_value()
val input = WmInputEvent.mouse_move(WindowId(value: 8u64), Point.xy(4, 5))
expect(wm.accept_input_ingress(generation, 1u64, input)).to_be(true)
expect(wm.commit_presentation(
    generation, revision, 1u64, 44u64, "framebuffer"
)).to_be(true)
expect(wm.presentation_matches(
    generation, revision, 1u64, 44u64, "framebuffer"
)).to_be(true)

step("Restart the owner and reject all old-generation work")
expect(wm.restart()).to_equal(1u64)
expect(wm.accept_input_ingress(generation, 2u64, input)).to_be(false)
expect(wm.last_rejection_reason).to_equal("stale-lifecycle-generation")
expect(wm.presentation_matches(
    generation, revision, 1u64, 44u64, "framebuffer"
)).to_be(false)
expect(wm.last_presented_frame_id).to_equal(0u64)
```

</details>

### REQ-017 live-guest visual capture binding

#### should bind guest input scene presentation and QMP pixels in one fresh bundle

- should bind guest input scene presentation and QMP pixels in one fresh bundle
   - Artifact capture: after_step
- Run the canonical SimpleOS WM QEMU evidence owner
   - Artifact capture: after_step
- Load the wrapper-admitted evidence and reject missing capture identities
   - Artifact capture: after_step
- Bind the same input sequence to scene mutation and presentation generation
   - Artifact capture: after_step
- Verify retained QMP frames by byte count and content hash
   - Artifact capture: after_step
   - Evidence: artifact verified by 1 expected check
   - Expected: file_hash_sha256(path).len() equals `64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 48 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should bind guest input scene presentation and QMP pixels in one fresh bundle")
step("Run the canonical SimpleOS WM QEMU evidence owner")
val (stdout, stderr, code) = process_run(
    "/usr/bin/env",
    [
        "BUILD_DIR=" + LIVE_DIR,
        "REPORT_PATH=" + LIVE_REPORT,
        "/bin/sh",
        LIVE_WRAPPER
    ]
)
if code != 0:
    block_live_guest(
        "wrapper exit=" + code.to_string() +
        " stderr_bytes=" + stderr.bytes().len().to_string())
else if not live_artifacts_present():
    block_live_guest("wrapper returned zero without the complete evidence bundle")
else:
    step("Load the wrapper-admitted evidence and reject missing capture identities")
    val evidence = file_read(LIVE_EVIDENCE)
    expect(stdout).to_contain("simpleos_wm_fullscreen_status=pass")
    expect(evidence).to_contain("simpleos_wm_fullscreen_status=pass")
    expect(file_read(LIVE_REPORT)).to_contain("- status: pass")

    step("Bind the same input sequence to scene mutation and presentation generation")
    val pointer_sequence = live_i64(evidence, "simpleos_wm_fullscreen_pointer_input_seq")
    val presented_generation = live_i64(
        evidence, "simpleos_wm_fullscreen_browser_content_presented_generation")
    expect(pointer_sequence).to_be_greater_than(0)
    expect(presented_generation).to_be_greater_than(0)
    expect(live_i64(
        evidence, "simpleos_wm_fullscreen_browser_content_delta_generation"
    )).to_equal(presented_generation)
    expect(live_value(
        evidence, "simpleos_wm_fullscreen_browser_content_applied_marker"
    )).to_contain("input_seq=" + pointer_sequence.to_string())

    step("Verify retained QMP frames by byte count and content hash")
    for name in ["baseline", "fullscreen", "restored", "browser-event"]:
        val path = LIVE_DIR + "/" + name + ".ppm"
        expect(file_read_bytes(path).len()).to_be_greater_than(0)
        expect(file_hash_sha256(path).len()).to_equal(64)
    expect(file_hash_sha256(LIVE_DIR + "/fullscreen.ppm").index_of(
        file_hash_sha256(LIVE_DIR + "/baseline.ppm")
    )).to_equal(-1)
    expect(file_hash_sha256(LIVE_DIR + "/restored.ppm")).to_equal(
        file_hash_sha256(LIVE_DIR + "/baseline.ppm"))
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

- `REQ-SSPEC-SYSTEM`
- `REQ-017`
- `REQ-017-LIVE-GUEST`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `62672f740904f614bd8391e45a4e6b96b18246ad9164e793602e584afcf656f0`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `62672f740904f614bd8391e45a4e6b96b18246ad9164e793602e584afcf656f0`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `62672f740904f614bd8391e45a4e6b96b18246ad9164e793602e584afcf656f0`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **80/100**; effective score: **80/100**; blockers: **0**.

SSpec documentization score: 80/100
source: test/03_system/os/wm/simpleos_wm_behavior_evidence_spec.spl
mirror: doc/06_spec/03_system/os/wm/simpleos_wm_behavior_evidence_spec.md (current)
findings: 13 blockers: 0
  narrative=100 structure=60 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/os/wm/simpleos_wm_behavior_evidence_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/os/wm/simpleos_wm_behavior_evidence_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/os/wm/simpleos_wm_behavior_evidence_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 6 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/os/wm/simpleos_wm_behavior_evidence_spec.spl:123:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'should keep focus order and choose the next stack-top window after close' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/03_system/os/wm/simpleos_wm_behavior_evidence_spec.spl:123:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should keep focus order and choose the next stack-top window after close' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/os/wm/simpleos_wm_behavior_evidence_spec.spl:148:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should bound damage geometry count generation and scene revision' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/os/wm/simpleos_wm_behavior_evidence_spec.spl:148:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should bound damage geometry count generation and scene revision' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/os/wm/simpleos_wm_behavior_evidence_spec.spl:189:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should route committed input only through the focused production window' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/os/wm/simpleos_wm_behavior_evidence_spec.spl:189:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should route committed input only through the focused production window' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/os/wm/simpleos_wm_behavior_evidence_spec.spl:228:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should compose z-order into pixels and preserve it across damage-only redraw' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/os/wm/simpleos_wm_behavior_evidence_spec.spl:228:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should compose z-order into pixels and preserve it across damage-only redraw' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/os/wm/simpleos_wm_behavior_evidence_spec.spl:263:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should fence stale input and presentation receipts after recovery' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/os/wm/simpleos_wm_behavior_evidence_spec.spl:294:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should bind guest input scene presentation and QMP pixels in one fresh bundle' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->

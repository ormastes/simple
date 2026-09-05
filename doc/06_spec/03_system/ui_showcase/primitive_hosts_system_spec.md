# Cross-host primitive contract — headless evidence only

> Purpose: should reduce one canonical left-button click into an observable click state

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 12 | 12 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Cross-host primitive contract — headless evidence only

Purpose: should reduce one canonical left-button click into an observable click state

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/ui_showcase/primitive_hosts_system_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: should reduce one canonical left-button click into an observable click state
Audience: compiler and tooling engineers who maintain this spec

# Cross-host primitive contract — headless evidence only

This scenario uses the canonical `HostInputEvent` ingress and
`showcase_apply` reducer for the four host surfaces. It covers the first
primitive slice needed by every surface: button activation, pointer drag,
scroll linking, modifier-bearing keys, layout geometry, and font-bearing
DrawIR.

The assertions below are host/container contract evidence. They do not claim
that a GUI window, browser, or WM is live. A live SimpleOS/QEMU run must use
the dedicated QEMU runner and retain its framebuffer/input/audio receipt;
absence of that receipt is not converted into a pass here.

## Scenarios

### headless primitive reducer — button, drag, scroll, modifiers

#### should reduce one canonical left-button click into an observable click state

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- should reduce one canonical left-button click into an observable click state
- Verify: should reduce one canonical left-button click into an observable click state
- Build a shared tree and apply a down/up click sequence
   - Expected: showcase_click_count(prefix) equals `1`
   - Expected: st.tree.root_node().get_prop("title") equals `Simple Showcase`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should reduce one canonical left-button click into an observable click state")
step("Verify: should reduce one canonical left-button click into an observable click state")
# @req: REQ-UI_SHOWCASE-PrimHostSyst-001
step("Build a shared tree and apply a down/up click sequence")
val prefix = "primitive_click_contract"
var st = showcase_build(prefix)
val (x, y) = _action_point(st, prefix)
st = showcase_apply(st, host_pointer_down(x, y, HOST_BTN_LEFT), PRIM_W, PRIM_H)
st = showcase_apply(st, host_pointer_up(x, y, HOST_BTN_LEFT), PRIM_W, PRIM_H)

expect(showcase_click_count(prefix)).to_equal(1)  # oracle: value fixed by the spec contract
expect(st.tree.root_node().id).to_contain(prefix)
expect(st.tree.root_node().get_prop("title")).to_equal("Simple Showcase")
```

</details>

#### should retain an active drag and record its move before release

- should retain an active drag and record its move before release
- Verify: should retain an active drag and record its move before release
- Apply pointer down, move, and release through the shared reducer
   - Expected: showcase_drag_count(prefix) > 0 is true
   - Expected: st.tree.root_node().get_prop("visible") equals `true`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should retain an active drag and record its move before release")
step("Verify: should retain an active drag and record its move before release")
# @req: REQ-UI_SHOWCASE-PrimHostSyst-001
step("Apply pointer down, move, and release through the shared reducer")
val prefix = "primitive_drag_contract"
var st = showcase_build(prefix)
st = showcase_apply(st, host_pointer_down(14, 14, HOST_BTN_LEFT), PRIM_W, PRIM_H)
st = showcase_apply(st, host_pointer_move(38, 29), PRIM_W, PRIM_H)
st = showcase_apply(st, host_pointer_up(38, 29, HOST_BTN_LEFT), PRIM_W, PRIM_H)

expect(showcase_drag_count(prefix) > 0).to_equal(true)
expect(st.tree.root_node().id).to_contain(prefix)
expect(st.tree.root_node().get_prop("visible")).to_equal("true")
```

</details>

#### should link scroll offsets while leaving the independent panel unchanged

- should link scroll offsets while leaving the independent panel unchanged
- Verify: should link scroll offsets while leaving the independent panel unchanged
- Scroll the linked panel at its computed layout point
   - Expected: showcase_scroll_offset(prefix, SC_LINK_SRC) > 0 is true
   - Expected: showcase_scroll_offset(prefix, SC_FREE) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should link scroll offsets while leaving the independent panel unchanged")
step("Verify: should link scroll offsets while leaving the independent panel unchanged")
# @req: REQ-UI_SHOWCASE-PrimHostSyst-001
step("Scroll the linked panel at its computed layout point")
val prefix = "primitive_scroll_contract"
var st = showcase_build(prefix)
val (x, y) = _scroll_point(st, prefix, SC_LINK_SRC)
st = showcase_apply(st, host_pointer_wheel(x, y, 1), PRIM_W, PRIM_H)

expect(showcase_scroll_offset(prefix, SC_LINK_SRC) > 0).to_equal(true)
expect(showcase_scroll_offset(prefix, SC_LINK_DST)).to_equal(
    showcase_scroll_offset(prefix, SC_LINK_SRC)
)
expect(showcase_scroll_offset(prefix, SC_FREE)).to_equal(0)  # oracle: value fixed by the spec contract
```

</details>

#### should preserve Ctrl+Alt on a key event in the visible probe state

- should preserve Ctrl+Alt on a key event in the visible probe state
- Verify: should preserve Ctrl+Alt on a key event in the visible probe state
- Apply a printable key carrying both modifier bits
   - Expected: showcase_typed_text(prefix) equals `A`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should preserve Ctrl+Alt on a key event in the visible probe state")
step("Verify: should preserve Ctrl+Alt on a key event in the visible probe state")
# @req: REQ-UI_SHOWCASE-PrimHostSyst-001
step("Apply a printable key carrying both modifier bits")
val prefix = "primitive_modifier_contract"
var st = showcase_build(prefix)
st = showcase_apply(
    st, host_key_down(65, "A", HOST_MOD_CTRL | HOST_MOD_ALT), PRIM_W, PRIM_H
)

expect(showcase_typed_text(prefix)).to_equal("A")
val probe = st.tree.root_node().get_prop("id")
expect(probe).to_contain(prefix)
expect(common.ui.widget_store_ops.get_internal_prop(
    "{prefix}{SC_PROBE}", "typed_text"
)).to_equal("A")
```

</details>

### host/container primitive ingress — no display claim

#### should translate GUI button and drag primitives into canonical ingress

- should translate GUI button and drag primitives into canonical ingress
- Verify: should translate GUI button and drag primitives into canonical ingress
- Translate GUI press, move, release, and known button codes
   - Expected: gui_button_to_host(0) equals `HOST_BTN_LEFT`
   - Expected: gui_button_to_host(99) equals `HOST_BTN_NONE`
   - Expected: [x, y, button, wheel] equals `[12, 7, HOST_BTN_LEFT, 0]`
   - Expected: pressed is true
   - Expected: [x, y, button, wheel] equals `[30, 18, HOST_BTN_NONE, 0]`
   - Expected: pressed is true
   - Expected: [x, y, button, wheel] equals `[30, 18, HOST_BTN_LEFT, 0]`
   - Expected: pressed is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 41 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should translate GUI button and drag primitives into canonical ingress")
step("Verify: should translate GUI button and drag primitives into canonical ingress")
# @req: REQ-UI_SHOWCASE-PrimHostSyst-001
step("Translate GUI press, move, release, and known button codes")
val down = gui_event_to_host(_gui_event(
    GUI_EVT_MOUSE_BUTTON, 0, 0, true, 12.9, 7.1
))
val move = gui_event_to_host(_gui_event(
    GUI_EVT_MOUSE_MOVED, 0, 0, false, 30.8, 18.2
))
val up = gui_event_to_host(_gui_event(
    GUI_EVT_MOUSE_BUTTON, 0, 0, false, 30.8, 18.2
))

expect(gui_button_to_host(0)).to_equal(HOST_BTN_LEFT)
expect(gui_button_to_host(99)).to_equal(HOST_BTN_NONE)
match down:
    case Some(HostInputEvent.Pointer(x, y, button, pressed, wheel)):
        expect([x, y, button, wheel]).to_equal([12, 7, HOST_BTN_LEFT, 0])
        expect(pressed).to_equal(true)
    case Some(_):
        fail("GUI press returned a non-pointer event")
    case None:
        fail("GUI press was dropped")
match move:
    case Some(HostInputEvent.Pointer(x, y, button, pressed, wheel)):
        expect([x, y, button, wheel]).to_equal([30, 18, HOST_BTN_NONE, 0])
        expect(pressed).to_equal(true)
    case Some(_):
        fail("GUI move returned a non-pointer event")
    case None:
        fail("GUI move was dropped")
match up:
    case Some(HostInputEvent.Pointer(x, y, button, pressed, wheel)):
        expect([x, y, button, wheel]).to_equal([30, 18, HOST_BTN_LEFT, 0])
        expect(pressed).to_equal(false)
    case Some(_):
        fail("GUI release returned a non-pointer event")
    case None:
        fail("GUI release was dropped")
```

</details>

#### should preserve web wheel and modifier-bearing key bridge events

- should preserve web wheel and modifier-bearing key bridge events
- Verify: should preserve web wheel and modifier-bearing key bridge events
- Write encoded events and read them through the web file bridge
   - Expected: code equals `65`
   - Expected: ch equals `A`
   - Expected: down is true
   - Expected: mods equals `HOST_MOD_CTRL | HOST_MOD_ALT`
   - Expected: [x, y] equals `[24, 32]`
   - Expected: wheel_delta equals `1`
   - Expected: button equals `HOST_BTN_NONE`
   - Expected: pressed is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 42 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should preserve web wheel and modifier-bearing key bridge events")
step("Verify: should preserve web wheel and modifier-bearing key bridge events")
# @req: REQ-UI_SHOWCASE-PrimHostSyst-001
step("Write encoded events and read them through the web file bridge")
val dir = "/tmp/primitive_hosts_web_events"
mkdir_p(dir)
write_file(
    wm_fs_app_event_seq_path(dir + "/event", 1),
    wm_fs_app_event_encode(wm_fs_app_event(
        1, "key", 0, 0, 65, true, 65, "A", HOST_MOD_CTRL | HOST_MOD_ALT, 0
    ))
)
write_file(
    wm_fs_app_event_seq_path(dir + "/event", 2),
    wm_fs_app_event_encode(wm_fs_app_event(
        2, "wheel", 24, 32, HOST_BTN_NONE, false, 0, "", 0, 1
    ))
)
val key = web_read_event_at(dir + "/event", 1)
val wheel = web_read_event_at(dir + "/event", 2)

match key:
    case Some(HostInputEvent.Key(code, ch, down, mods)):
        expect(code).to_equal(65)  # oracle: value fixed by the spec contract
        expect(ch).to_equal("A")
        expect(down).to_equal(true)
        expect(mods).to_equal(HOST_MOD_CTRL | HOST_MOD_ALT)
    case Some(_):
        fail("web key bridge returned a non-key event")
    case None:
        fail("web key bridge returned nil")
match wheel:
    case Some(HostInputEvent.Pointer(x, y, button, pressed, wheel_delta)):
        expect([x, y]).to_equal([24, 32])
        expect(wheel_delta).to_equal(1)  # oracle: value fixed by the spec contract
        expect(button).to_equal(HOST_BTN_NONE)
        expect(pressed).to_equal(false)
    case Some(_):
        fail("web wheel bridge returned a non-pointer event")
    case None:
        fail("web wheel bridge returned nil")
```

</details>

#### should decode the same pointer and modifier wire contract for the WM bridge

- should decode the same pointer and modifier wire contract for the WM bridge
- Verify: should decode the same pointer and modifier wire contract for the WM bridge
- Read an encoded drag and key sequence through the WM bridge
   - Expected: [x, y, button, wheel] equals `[9, 10, HOST_BTN_LEFT, 0]`
   - Expected: pressed is true
   - Expected: code equals `17`
   - Expected: ch equals ``
   - Expected: pressed is true
   - Expected: mods equals `HOST_MOD_CTRL`


<details>
<summary>Executable SSpec</summary>

Runnable source: 40 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should decode the same pointer and modifier wire contract for the WM bridge")
step("Verify: should decode the same pointer and modifier wire contract for the WM bridge")
# @req: REQ-UI_SHOWCASE-PrimHostSyst-001
step("Read an encoded drag and key sequence through the WM bridge")
val dir = "/tmp/primitive_hosts_wm_events"
mkdir_p(dir)
write_file(
    wm_fs_app_event_seq_path(dir + "/event", 1),
    wm_fs_app_event_encode(wm_fs_app_event(
        1, "mouse_down", 9, 10, HOST_BTN_LEFT, true, 0, "", 0, 0
    ))
)
write_file(
    wm_fs_app_event_seq_path(dir + "/event", 2),
    wm_fs_app_event_encode(wm_fs_app_event(
        2, "key", 0, 0, 17, true, 17, "", HOST_MOD_CTRL, 0
    ))
)
val down = wm_read_event_at(dir + "/event", 1)
val key = wm_read_event_at(dir + "/event", 2)

match down:
    case Some(HostInputEvent.Pointer(x, y, button, pressed, wheel)):
        expect([x, y, button, wheel]).to_equal([9, 10, HOST_BTN_LEFT, 0])
        expect(pressed).to_equal(true)
    case Some(_):
        fail("WM pointer bridge returned a non-pointer event")
    case None:
        fail("WM pointer bridge returned nil")
match key:
    case Some(HostInputEvent.Key(code, ch, pressed, mods)):
        expect(code).to_equal(17)  # oracle: value fixed by the spec contract
        expect(ch).to_equal("")
        expect(pressed).to_equal(true)
        expect(mods).to_equal(HOST_MOD_CTRL)
    case Some(_):
        fail("WM key bridge returned a non-key event")
    case None:
        fail("WM key bridge returned nil")
```

</details>

#### should keep the 2d host queue finite and report the headless host identity

- should keep the 2d host queue finite and report the headless host identity
- Verify: should keep the 2d host queue finite and report the headless host identity
- Drain a scripted 2d host without requiring a display
   - Expected: host.host_name() equals `2d`
   - Expected: count equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should keep the 2d host queue finite and report the headless host identity")
step("Verify: should keep the 2d host queue finite and report the headless host identity")
# @req: REQ-UI_SHOWCASE-PrimHostSyst-001
step("Drain a scripted 2d host without requiring a display")
val host = Screen2dHost.open(64, 48, "click 5,5;wheel 2,2,1")
var count = 0
var ev = host.poll_input()
while count < 4:
    match ev:
        case None:
            break
        case Some(value):
            count = count + 1
            ev = host.poll_input()

expect(host.host_name()).to_equal("2d")
expect(count).to_equal(3)  # oracle: value fixed by the spec contract
expect(host.poll_input()).to_be_nil()
```

</details>

### semantic layout and font DrawIR — host evidence

#### should expose positive layout boxes for the linked panel and probe

- should expose positive layout boxes for the linked panel and probe
- Verify: should expose positive layout boxes for the linked panel and probe
- Compute the shared widget layout at a fixed host extent
   - Expected: panel_box.w > 0 is true
   - Expected: panel_box.h > 0 is true
   - Expected: probe_box.y >= panel_box.y is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should expose positive layout boxes for the linked panel and probe")
step("Verify: should expose positive layout boxes for the linked panel and probe")
# @req: REQ-UI_SHOWCASE-PrimHostSyst-001
step("Compute the shared widget layout at a fixed host extent")
val prefix = "primitive_layout_contract"
val st = showcase_build(prefix)
val rects = compute_layout(st.tree.root_node(), 0, 0, PRIM_W, PRIM_H)
val panel = find_rect(rects, "{prefix}{SC_LINK_SRC}")
val probe = find_rect(rects, "{prefix}{SC_PROBE}")

match panel:
    case None:
        fail("linked panel has no layout box")
    case Some(panel_box):
        expect(panel_box.w > 0).to_equal(true)
        expect(panel_box.h > 0).to_equal(true)
        match probe:
            case None:
                fail("probe has no layout box")
            case Some(probe_box):
                expect(probe_box.y >= panel_box.y).to_equal(true)
```

</details>

#### should emit rect and text commands from the same semantic tree

- should emit rect and text commands from the same semantic tree
- Verify: should emit rect and text commands from the same semantic tree
- Lower the shared tree to CPU-targeted DrawIR for observation
   - Expected: _command_count(composition, DRAW_IR_COMMAND_RECT) > 0 is true
   - Expected: _command_count(composition, DRAW_IR_COMMAND_TEXT) > 0 is true
   - Expected: composition.backend_target equals `cpu`
   - Expected: composition.batches.len() > 0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should emit rect and text commands from the same semantic tree")
step("Verify: should emit rect and text commands from the same semantic tree")
# @req: REQ-UI_SHOWCASE-PrimHostSyst-001
step("Lower the shared tree to CPU-targeted DrawIR for observation")
val prefix = "primitive_drawir_contract"
val st = showcase_build(prefix)
val composition = widget_tree_to_draw_ir_cpu(st.tree.root_node(), PRIM_W, PRIM_H)

expect(_command_count(composition, DRAW_IR_COMMAND_RECT) > 0).to_equal(true)
expect(_command_count(composition, DRAW_IR_COMMAND_TEXT) > 0).to_equal(true)
expect(composition.backend_target).to_equal("cpu")
expect(composition.batches.len() > 0).to_equal(true)
```

</details>

#### should retain an observable font identity and glyph payload for text

- should retain an observable font identity and glyph payload for text
- Verify: should retain an observable font identity and glyph payload for text
- Inspect the first semantic text command before any backend runs
   - Expected: command.text_value.len() > 0 is true
   - Expected: command.computed_style.len() > 0 is true
   - Expected: _style_value(command, "font-identity").len() > 0 is true
   - Expected: command.advance_widths.len() > 0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should retain an observable font identity and glyph payload for text")
step("Verify: should retain an observable font identity and glyph payload for text")
# @req: REQ-UI_SHOWCASE-PrimHostSyst-001
step("Inspect the first semantic text command before any backend runs")
val prefix = "primitive_font_contract"
val st = showcase_build(prefix)
val composition = widget_tree_to_draw_ir_cpu(st.tree.root_node(), PRIM_W, PRIM_H)
val text_command = _first_text(composition)

match text_command:
    case None:
        fail("semantic tree emitted no text command")
    case Some(command):
        expect(command.text_value.len() > 0).to_equal(true)
        # Resolved-font commands carry the identity/style; the glyph
        # payload is the fallback-proof representation consumed by
        # every renderer.
        expect(command.computed_style.len() > 0).to_equal(true)
        expect(_style_value(command, "font-identity").len() > 0).to_equal(true)
        expect(command.advance_widths.len() > 0).to_equal(true)
```

</details>

### live evidence boundary

#### should leave live GUI, web, WM, and QEMU claims to their real runners

- should leave live GUI, web, WM, and QEMU claims to their real runners
- Verify: should leave live GUI, web, WM, and QEMU claims to their real runners
- Record the boundary between this headless contract and live evidence
   - Expected: host.host_name() equals `web`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should leave live GUI, web, WM, and QEMU claims to their real runners")
step("Verify: should leave live GUI, web, WM, and QEMU claims to their real runners")
# @req: REQ-UI_SHOWCASE-PrimHostSyst-001
step("Record the boundary between this headless contract and live evidence")
val web = ScreenWebHost.open(40, 30, "/tmp/primitive_hosts_boundary.html", "")
# An absent browser/server is not inferred from this spec. The web host
# only proves its projection contract; QEMU must provide its own receipt.
match web:
    case None:
        fail("web host projection did not open")
    case Some(host):
        expect(host.host_name()).to_equal("web")
        expect(web_scene_to_html(
            common.ui.draw_ir_v3.draw_ir_v3_empty_scene(1u32, 1u32), 40, 30
        ).contains("showcase-root")).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 12 |
| Active scenarios | 12 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
- `REQ-UI_SHOWCASE-PrimHostSyst-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `209f1f63b5e78f969b7c20f8af474737334da8ec7654d87d3d1fca1516bbee78`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `209f1f63b5e78f969b7c20f8af474737334da8ec7654d87d3d1fca1516bbee78`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `209f1f63b5e78f969b7c20f8af474737334da8ec7654d87d3d1fca1516bbee78`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/03_system/ui_showcase/primitive_hosts_system_spec.spl
mirror: doc/06_spec/03_system/ui_showcase/primitive_hosts_system_spec.md (current)
findings: 11 blockers: 0
  narrative=100 structure=70 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/ui_showcase/primitive_hosts_system_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/ui_showcase/primitive_hosts_system_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/ui_showcase/primitive_hosts_system_spec.spl:113:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should reduce one canonical left-button click into an observable click state' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/ui_showcase/primitive_hosts_system_spec.spl:113:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should reduce one canonical left-button click into an observable click state' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/ui_showcase/primitive_hosts_system_spec.spl:129:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should retain an active drag and record its move before release' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/ui_showcase/primitive_hosts_system_spec.spl:129:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should retain an active drag and record its move before release' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/ui_showcase/primitive_hosts_system_spec.spl:145:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should link scroll offsets while leaving the independent panel unchanged' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/ui_showcase/primitive_hosts_system_spec.spl:145:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should link scroll offsets while leaving the independent panel unchanged' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/ui_showcase/primitive_hosts_system_spec.spl:162:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should preserve Ctrl+Alt on a key event in the visible probe state' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/ui_showcase/primitive_hosts_system_spec.spl:183:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should translate GUI button and drag primitives into canonical ingress' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/ui_showcase/primitive_hosts_system_spec.spl:226:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should preserve web wheel and modifier-bearing key bridge events' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->

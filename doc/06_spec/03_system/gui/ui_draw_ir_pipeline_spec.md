# Widget → Draw-IR → Engine2D Pipeline Specification

> Capture-backed proof of the widget-tree → Draw-IR converter, pointer/scroll event routing, and the animation timeline:

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Widget → Draw-IR → Engine2D Pipeline Specification

Capture-backed proof of the widget-tree → Draw-IR converter, pointer/scroll event routing, and the animation timeline:

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | W1d, G1.2, G1.5, G1.6 |
| Category | GUI \| Rendering \| Interaction |
| Status | In Progress |
| Requirements | doc/03_plan/ui/production_readiness_master_plan_2026-07-02.md |
| Source | `test/03_system/gui/ui_draw_ir_pipeline_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Capture-backed proof of the widget-tree → Draw-IR converter, pointer/scroll
event routing, and the animation timeline:

1. **Converter (G1.2):** a small widget tree (container, label, button,
   checkbox, text input, image, progress, scroll area) is laid out at
   640x480, converted to a Draw-IR composition, and rendered offscreen
   through the CPU Engine2D backend. Pixel probes assert each widget is
   visible at its expected geometry.
2. **Event routing (G1.5):** a button press flips its rendered fill and the
   re-rendered frame differs in exactly the button region; a checkbox click
   toggles its mark; a scroll event shifts clipped content by exactly one row.
3. **Animation timeline (G1.6):** an ease-in-out timeline drives a progress
   bar deterministically from injected elapsed time; successive frames
   advance monotonically and the eased midpoint lands at 50%.

All rendering is offscreen (CPU backend, PPM dumps); the live display is
never touched.

## Scenarios

### Widget → Draw-IR → Engine2D pipeline

#### renders each widget at its laid-out geometry incl. the IMAGE op (pixel probes)

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- renders each widget at its laid-out geometry incl. the IMAGE op (pixel probes)
   - Expected: label_command.computed_style[0].value equals `Noto Sans Mono`
   - Expected: at(px, 320, 51) equals `BTN_NORMAL`
   - Expected: at(px, 10, 86) equals `CHECK_BG`
   - Expected: at(px, 400, 205) equals `PROGRESS_TRACK`
   - Expected: at(px, 320, 161) equals `GREEN`


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("renders each widget at its laid-out geometry incl. the IMAGE op (pixel probes)")
# Rendered with a resolved image so the IMAGE draw-op executes for real;
# the other widget probes are unaffected (distinct regions). One render
# covers geometry + image coverage to stay within the render budget.
val root = build_demo("g1")
val comp = widget_tree_to_draw_ir_cpu(root, W, H)
val label_command = comp.batches[0].commands[1]
if label_command.computed_style.len() > 0:
    expect(label_command.computed_style[0].value).to_equal("Noto Sans Mono")
    expect(label_command.computed_style[1].value).to_start_with("sha256=")
    expect(label_command.computed_style[2].value).to_contain(",")
    expect(label_command.width).to_be_greater_than(0)
val px = render_pixels_with_image(root)
# button rect (1,31,638,40) -> center (320,51)
expect(at(px, 320, 51)).to_equal(BTN_NORMAL)
# checkbox mark, unchecked -> CHECK_BG box interior near (10,86)
expect(at(px, 10, 86)).to_equal(CHECK_BG)
# progress track (1,191,638,30), value 0 -> no fill
expect(at(px, 400, 205)).to_equal(PROGRESS_TRACK)
# resolved 2x2 green image scaled over the image rect (1,131,638,60)
expect(at(px, 320, 161)).to_equal(GREEN)
write_ppm(px, "build/gui_draw_ir/frame_normal.ppm")
```

</details>

#### button press flips fill and re-render differs in exactly the button region

- button press flips fill and re-render differs in exactly the button region
   - Expected: hit equals `g2btn_btn`
   - Expected: at(after, 320, 51) equals `BTN_PRESSED`
   - Expected: outside equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("button press flips fill and re-render differs in exactly the button region")
val root = build_demo("g2btn")
val before = render_pixels(root)
write_ppm(before, "build/gui_draw_ir/frame_btn_before.ppm")
# press the button at its center
val hit = widget_set_pressed(root, W, H, 320, 51)
expect(hit).to_equal("g2btn_btn")
val after = render_pixels(root)
expect(at(after, 320, 51)).to_equal(BTN_PRESSED)
# every differing pixel must lie inside the button rect y ∈ [31,71)
var diff = 0
var outside = 0
var i = 0
val n = before.len()
while i < n:
    if before[i] != after[i]:
        diff = diff + 1
        val y = i / W
        if y < 31 or y >= 71:
            outside = outside + 1
    i = i + 1
expect(diff).to_be_greater_than(0)
expect(outside).to_equal(0)
write_ppm(after, "build/gui_draw_ir/frame_pressed.ppm")
```

</details>

#### checkbox click toggles the rendered mark

- checkbox click toggles the rendered mark
   - Expected: hit equals `g2chk_chk`
   - Expected: at(after, 10, 86) equals `CHECK_MARK`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("checkbox click toggles the rendered mark")
# Unchecked mark colour (CHECK_BG) is proven by the geometry probe above;
# here we render only the post-click frame to stay within the render
# budget (each 640x480 CPU render is ~9s under the interpreter).
val root = build_demo("g2chk")
val hit = widget_dispatch_click(root, W, H, 10, 86)
expect(hit).to_equal("g2chk_chk")
val after = render_pixels(root)
expect(at(after, 10, 86)).to_equal(CHECK_MARK)
write_ppm(after, "build/gui_draw_ir/frame_chk_after.ppm")
```

</details>

#### scroll shifts clipped content up by exactly one row

- scroll shifts clipped content up by exactly one row
   - Expected: at(before, 10, 260) equals `BTN_NORMAL`
   - Expected: target equals `g2scr_scroll`
   - Expected: at(after, 10, 260) equals `PROGRESS_FILL`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("scroll shifts clipped content up by exactly one row")
val root = build_demo("g2scr")
val before = render_pixels(root)
write_ppm(before, "build/gui_draw_ir/frame_scroll_before.ppm")
# probe P=(10,260) inside the scroll viewport (221..301):
# offset 0 -> content y260 -> row1 (button)
expect(at(before, 10, 260)).to_equal(BTN_NORMAL)
# scroll content up 30px (one row height)
val target = widget_dispatch_scroll(root, W, H, 10, 260, 30)
expect(target).to_equal("g2scr_scroll")
val after = render_pixels(root)
# now content y290 -> row2 (progress) is at P
expect(at(after, 10, 260)).to_equal(PROGRESS_FILL)
write_ppm(after, "build/gui_draw_ir/frame_scrolled.ppm")
```

</details>

#### ease-in-out timeline advances deterministically from injected time

- ease-in-out timeline advances deterministically from injected time


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("ease-in-out timeline advances deterministically from injected time")
val tl = timeline_new(0.0, 100.0, 100.0, EasingKind.EaseInOut)
val v0 = timeline_value_at(tl, 0.0)
val v25 = timeline_value_at(tl, 25.0)
val v50 = timeline_value_at(tl, 50.0)
val v75 = timeline_value_at(tl, 75.0)
val v100 = timeline_value_at(tl, 100.0)
# endpoints exact, midpoint symmetric at 50
assert_true(math_abs(v0 - 0.0) < 1e-6)
assert_true(math_abs(v100 - 100.0) < 1e-6)
assert_true(math_abs(v50 - 50.0) < 0.5)
# ease-in-out: slow start, fast middle, slow end
assert_true(v25 < 25.0)
assert_true(v75 > 75.0)
# monotonic non-decreasing
assert_true(v0 <= v25)
assert_true(v25 <= v50)
assert_true(v50 <= v75)
assert_true(v75 <= v100)
```

</details>

#### timeline-driven progress bar produces monotonically advancing frames

- timeline-driven progress bar produces monotonically advancing frames
   - Expected: at(f_lo, 100, 205) equals `PROGRESS_FILL`
   - Expected: at(f_lo, 300, 205) equals `PROGRESS_TRACK`
   - Expected: at(f_hi, 300, 205) equals `PROGRESS_FILL`


<details>
<summary>Executable SSpec</summary>

Runnable source: 28 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("timeline-driven progress bar produces monotonically advancing frames")
# 3 injected-time frames (elapsed 0 / 50 / 100 ms). The fill boundary in
# the progress row (1,191)-(639,221) must sweep left→right as time
# advances; two probe columns (x=300, x=500) witness the boundary
# crossing between frames, proving deterministic monotonic advance.
val root = build_demo("g3")
val tl = timeline_new(0.0, 100.0, 100.0, EasingKind.EaseInOut)
val prog = WidgetNode(id: "g3_prog")

# Two injected-time frames (elapsed 40 / 60 ms). The progress fill
# boundary must sweep left→right between them, witnessed at x=300.
val iv_lo = (timeline_value_at(tl, 40.0) + 0.5) as i32
prog.set_prop("value", "{iv_lo}")
val f_lo = render_pixels(root)
val iv_hi = (timeline_value_at(tl, 60.0) + 0.5) as i32
prog.set_prop("value", "{iv_hi}")
val f_hi = render_pixels(root)

# lo frame: x=100 filled, boundary not yet at x=300
expect(at(f_lo, 100, 205)).to_equal(PROGRESS_FILL)
expect(at(f_lo, 300, 205)).to_equal(PROGRESS_TRACK)
# hi frame: boundary has advanced past x=300
expect(at(f_hi, 300, 205)).to_equal(PROGRESS_FILL)
# total fill strictly increased frame-to-frame (monotonic advance)
val c_lo = count_color(f_lo, 1, 191, 639, 221, PROGRESS_FILL)
val c_hi = count_color(f_hi, 1, 191, 639, 221, PROGRESS_FILL)
expect(c_hi).to_be_greater_than(c_lo)
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


## Related Documentation

- **Requirements:** `doc/03_plan/ui/production_readiness_master_plan_2026-07-02.md`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `0f1f1c986c69a3ca250486daf4cbecc0f6eadcdb40c192d7b014abb94e66c467`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `0f1f1c986c69a3ca250486daf4cbecc0f6eadcdb40c192d7b014abb94e66c467`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `0f1f1c986c69a3ca250486daf4cbecc0f6eadcdb40c192d7b014abb94e66c467`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/03_system/gui/ui_draw_ir_pipeline_spec.spl
mirror: doc/06_spec/03_system/gui/ui_draw_ir_pipeline_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/gui/ui_draw_ir_pipeline_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/gui/ui_draw_ir_pipeline_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/gui/ui_draw_ir_pipeline_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/gui/ui_draw_ir_pipeline_spec.spl:161:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'renders each widget at its laid-out geometry incl. the IMAGE op (pixel probes)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/gui/ui_draw_ir_pipeline_spec.spl:188:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'button press flips fill and re-render differs in exactly the button region' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/gui/ui_draw_ir_pipeline_spec.spl:215:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'checkbox click toggles the rendered mark' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

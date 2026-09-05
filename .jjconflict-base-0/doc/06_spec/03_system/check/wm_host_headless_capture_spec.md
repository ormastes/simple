# Host-WM Headless Capture Lane Contract

> Pins the headless capture lane added to the three host-WM showcase wrappers

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Host-WM Headless Capture Lane Contract

Pins the headless capture lane added to the three host-WM showcase wrappers

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/check/wm_host_headless_capture_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Pins the headless capture lane added to the three host-WM showcase wrappers
(widget, graphics-2D, web-standards) so the matrix's `widget x host-WM`,
`2D x host-WM`, and `web x host-WM` cells can collect evidence without owning
the single physical-window capture lane (see
`doc/08_tracking/bug/wm_showcase_no_headless_lane_2026-07-25.md`).

Static-contract style, matching
`test/03_system/check/wm_production_fullscreen_evidence_spec.spl`: it greps
each wrapper source for the exact env gate, the reused (not reinvented)
compose/blit/PPM-encode calls, and the honest-fail status keys, so a future
edit that silently drops the gate or swaps in fabricated pixels fails this
spec instead of only showing up as a missing matrix cell.

## Scenarios

### Host-WM headless capture lane contract

#### widget showcase host-WM wrapper implements the headless capture lane

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- widget showcase host-WM wrapper implements the headless capture lane
- Inspect the widget showcase host-WM wrapper source


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("widget showcase host-WM wrapper implements the headless capture lane")
step("Inspect the widget showcase host-WM wrapper source")
val script = file_read("examples/06_io/ui/wm_widget_showcase_gui.spl")
expect_headless_lane_contract(script, "wm_widget_showcase_host_headless", "compose_pixels(comp, trace_path)", "blit_child_frame_pixels(base_pixels, comp, child.pixels, child.w, child.h)")
expect(script).to_contain("val prefix = \"wm_widget_showcase_host_headless\"")
```

</details>

#### graphics 2D showcase host-WM wrapper implements the headless capture lane via the shared Engine2D pipeline

- graphics 2D showcase host-WM wrapper implements the headless capture lane via the shared Engine2D pipeline
- Inspect the graphics 2D showcase host-WM wrapper source


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("graphics 2D showcase host-WM wrapper implements the headless capture lane via the shared Engine2D pipeline")
step("Inspect the graphics 2D showcase host-WM wrapper source")
val script = file_read("examples/06_io/ui/wm_graphics_2d_showcase_gui.spl")
expect_headless_lane_contract(script, "wm_graphics_2d_showcase_host_headless", "compose_scene(b, comp, trace_path)", "blit_child_frame(b, comp, child.pixels, child.w, child.h)")
expect(script).to_contain("val prefix = \"wm_graphics_2d_showcase_host_headless\"")
# Migrated off the hand-rolled [u32] framebuffer onto the shared
# Engine2D/DrawIR HAL: chrome via draw_rect_filled, the child app's
# already-rendered frame via draw_image, single readback via
# read_pixels() feeding both gui.present_rgba and the PPM encoder.
expect(script).to_contain('use std.gpu.engine2d.engine.{Engine2D}')
expect(script).to_contain("b.draw_rect_filled(")
expect(script).to_contain("b.draw_image(win.x + 4, win.y + 28, child_w, child_h, child_pixels)")
expect(script).to_contain("b.read_pixels()")
```

</details>

#### web standards showcase host-WM wrapper implements the headless capture lane

- web standards showcase host-WM wrapper implements the headless capture lane
- Inspect the web standards showcase host-WM wrapper source


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("web standards showcase host-WM wrapper implements the headless capture lane")
step("Inspect the web standards showcase host-WM wrapper source")
val script = file_read("examples/06_io/ui/wm_web_standards_showcase_gui.spl")
expect_headless_lane_contract(script, "wm_web_standards_showcase_host_headless", "compose_pixels(comp, trace_path)", "blit_child_frame_pixels(base_pixels, comp, child.pixels, child.w, child.h)")
expect(script).to_contain("val prefix = \"wm_web_standards_showcase_host_headless\"")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
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

- Canonical SPipe generation for source `a5d31c36d4f4c6b1ed33bffbf1de77f440a87f710816acb374b9623fe6f98602`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `a5d31c36d4f4c6b1ed33bffbf1de77f440a87f710816acb374b9623fe6f98602`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `a5d31c36d4f4c6b1ed33bffbf1de77f440a87f710816acb374b9623fe6f98602`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/check/wm_host_headless_capture_spec.spl
mirror: doc/06_spec/03_system/check/wm_host_headless_capture_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/check/wm_host_headless_capture_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/check/wm_host_headless_capture_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/check/wm_host_headless_capture_spec.spl:94:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'widget showcase host-WM wrapper implements the headless capture lane' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/check/wm_host_headless_capture_spec.spl:102:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'graphics 2D showcase host-WM wrapper implements the headless capture lane via the shared Engine2D pipeline' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/check/wm_host_headless_capture_spec.spl:118:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'web standards showcase host-WM wrapper implements the headless capture lane' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

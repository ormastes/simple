# BrowserSession Script and CSS Animation Rendering

> BrowserSession owns the deterministic CSS/JavaScript animation clock and the selected animation instances. The trace scenario proves that its initial, intermediate, paused, resumed, and completed states lower through the canonical DrawIrComposition and that Engine2D paints the exact command color area.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 24 | 24 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# BrowserSession Script and CSS Animation Rendering

BrowserSession owns the deterministic CSS/JavaScript animation clock and the selected animation instances. The trace scenario proves that its initial, intermediate, paused, resumed, and completed states lower through the canonical DrawIrComposition and that Engine2D paints the exact command color area.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Requirements | doc/02_requirements/feature/simple_web_browser_engine_production_hardening.md |
| Plan | doc/03_plan/sys_test/html_css_spec_traceability.md |
| Design | doc/05_design/simple_web_browser_engine_production_hardening.md |
| Research | doc/01_research/local/simple_web_browser_engine_production_hardening.md |
| Source | `test/02_integration/rendering/browser_session_script_css_animation_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

BrowserSession owns the deterministic CSS/JavaScript animation clock and the
selected animation instances. The trace scenario proves that its initial,
intermediate, paused, resumed, and completed states lower through the canonical
DrawIrComposition and that Engine2D paints the exact command color area.

Requirement trace: REQ-WEB-BROWSER-003, REQ-WEB-BROWSER-004,
REQ-WEB-BROWSER-005, REQ-WEB-BROWSER-006, REQ-WEB-BROWSER-007,
REQ-WEB-BROWSER-017, and REQ-WEB-BROWSER-021.

## Examples

The displayed trace advances the browser clock, pauses and resumes through the
JavaScript DOM bridge, then checks the resulting Draw IR command and the pixels
rendered from that exact composition.

## Scenarios

### BrowserSession script CSS animation rendering

#### should cascade duplicate keyframe offsets into Draw IR pixels

- should cascade duplicate keyframe offsets into Draw IR pixels
   - Artifact capture: after_step
- Open CSS animation with duplicate keyframe offsets
   - Artifact capture: after_step
   - Evidence: artifact verified by 1 expected check
   - Expected: initial.command.color equals `0xFFEF4444u32`
- Advance to the duplicate keyframe offset
   - Artifact capture: after_step
   - Evidence: artifact verified by 2 expected checks
   - Expected: session.advance_time(500) equals `0`
   - Expected: midpoint.next_ms equals `516`
- Select the later same-offset declaration in Draw IR
   - Artifact capture: after_step
   - Evidence: artifact verified by 1 expected check
   - Expected: midpoint.command.color equals `0xFF22C55Eu32`
- Rasterize the cascaded frame through canonical Engine2D
   - Artifact capture: after_step
   - Expected: midpoint frame satisfies `_expect_browser_animation_draw_ir_frame`
   - Evidence: exact 32×24 command-color pixels, zero matching pixels outside the command, and zero skipped commands

Helper ownership is frozen to `_duplicate_offset_animation_html` for the
fixture, `_browser_animation_draw_ir_trace` for canonical Draw IR lowering and
Engine2D execution, and `_expect_browser_animation_draw_ir_frame` for exact
geometry/pixel/source assertions.

| Helper | Source |
|--------|--------|
| `_duplicate_offset_animation_html` | `test/02_integration/rendering/browser_session_script_css_animation_spec.spl` |
| `_browser_animation_draw_ir_trace` | `test/02_integration/rendering/browser_session_script_css_animation_spec.spl` |
| `_expect_browser_animation_draw_ir_frame` | `test/02_integration/rendering/browser_session_script_css_animation_spec.spl` |

<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("should cascade duplicate keyframe offsets into Draw IR pixels")
step("Open CSS animation with duplicate keyframe offsets")
var session = BrowserSession.new()
expect(session.open_html(
    "https://example.test/duplicate-keyframe-offset",
    _duplicate_offset_animation_html()
).is_ok()).to_be(true)
val initial = _browser_animation_draw_ir_trace(session, 64, 48)
_expect_browser_animation_draw_ir_frame(initial)
expect(initial.command.color).to_equal(0xFFEF4444u32)

step("Advance to the duplicate keyframe offset")
expect(session.advance_time(500)).to_equal(0)
val midpoint = _browser_animation_draw_ir_trace(session, 64, 48)
expect(midpoint.next_ms).to_equal(516)

step("Select the later same-offset declaration in Draw IR")
expect(midpoint.command.color).to_equal(0xFF22C55Eu32)

step("Rasterize the cascaded frame through canonical Engine2D")
_expect_browser_animation_draw_ir_frame(midpoint)
```

</details>

#### should trace JavaScript pause and resume through deterministic Draw IR frames

- should trace JavaScript pause and resume through deterministic Draw IR frames
   - Artifact capture: after_step
- Trace CSS animation through deterministic Draw IR frames
   - Artifact capture: after_step
- var session = BrowserSession new
   - Artifact capture: after_step
-  expect browser animation draw ir frame
   - Artifact capture: after_step
   - Evidence: artifact verified by 3 expected checks
   - Expected: initial.command.color equals `0xFFEF4444u32`
   - Expected: initial.next_ms equals `16`
   - Expected: session.advance_time(500) equals `0`
   - Expected: intermediate.command.color == initial.command.color is false
   - Expected: intermediate.command.color == 0xFF2563EBu32 is false
- "document getElementById
   - Artifact capture: after_step
-  expect browser animation draw ir frame
   - Artifact capture: after_step
   - Evidence: artifact verified by 3 expected checks
   - Expected: paused.command.color equals `intermediate.command.color`
   - Expected: paused.next_ms equals `-1`
   - Expected: session.advance_time(1000) equals `0`
   - Expected: still_paused.command.color equals `paused.command.color`
- "document getElementById
   - Artifact capture: after_step
-  expect browser animation draw ir frame
   - Artifact capture: after_step
   - Evidence: artifact verified by 3 expected checks
   - Expected: resumed.command.color equals `paused.command.color`
   - Expected: resumed.next_ms equals `1016`
   - Expected: session.advance_time(2500) equals `0`
   - Expected: completed.command.color equals `0xFF2563EBu32`
   - Expected: completed.next_ms equals `-1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 46 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("should trace JavaScript pause and resume through deterministic Draw IR frames")
step("Trace CSS animation through deterministic Draw IR frames")
val html = "<!DOCTYPE html><html><head><style>@keyframes Pulse { from { background-color: #ef4444; } to { background-color: #2563eb; } } #stage { width: 32px; height: 24px; background-color: #ef4444; } .running { animation: Pulse 2000ms linear forwards; } .paused { animation-play-state: paused; }</style></head><body><div id='stage' class='running'></div></body></html>"
var session = BrowserSession.new()
expect(session.open_html(
    "https://example.test/animation-draw-ir-trace", html
).is_ok()).to_equal(true)

val initial = _browser_animation_draw_ir_trace(session, 64, 48)
_expect_browser_animation_draw_ir_frame(initial)
expect(initial.command.color).to_equal(0xFFEF4444u32)
expect(initial.next_ms).to_equal(16)

expect(session.advance_time(500)).to_equal(0)
val intermediate = _browser_animation_draw_ir_trace(session, 64, 48)
_expect_browser_animation_draw_ir_frame(intermediate)
expect(intermediate.command.color == initial.command.color).to_equal(false)
expect(intermediate.command.color == 0xFF2563EBu32).to_equal(false)

expect(session.eval_script(
    "document.getElementById('stage').className = 'running paused'"
).is_ok()).to_equal(true)
val paused = _browser_animation_draw_ir_trace(session, 64, 48)
_expect_browser_animation_draw_ir_frame(paused)
expect(paused.command.color).to_equal(intermediate.command.color)
expect(paused.next_ms).to_equal(-1)

expect(session.advance_time(1000)).to_equal(0)
val still_paused = _browser_animation_draw_ir_trace(session, 64, 48)
_expect_browser_animation_draw_ir_frame(still_paused)
expect(still_paused.command.color).to_equal(paused.command.color)

expect(session.eval_script(
    "document.getElementById('stage').className = 'running'"
).is_ok()).to_equal(true)
val resumed = _browser_animation_draw_ir_trace(session, 64, 48)
_expect_browser_animation_draw_ir_frame(resumed)
expect(resumed.command.color).to_equal(paused.command.color)
expect(resumed.next_ms).to_equal(1016)

expect(session.advance_time(2500)).to_equal(0)
val completed = _browser_animation_draw_ir_trace(session, 64, 48)
_expect_browser_animation_draw_ir_frame(completed)
expect(completed.command.color).to_equal(0xFF2563EBu32)
expect(completed.next_ms).to_equal(-1)
```

</details>

#### tracks only DOM-observable animation frame mutations

- tracks only DOM-observable animation frame mutations
   - Expected: session.advance_time(16) equals `1`
   - Expected: session.current_title equals `title-only`
   - Expected: session.advance_time(32) equals `1`
   - Expected: session.advance_time(48) equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 43 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("tracks only DOM-observable animation frame mutations")
var session = BrowserSession.new()
expect(session.open_html(
    "https://example.test/dom-mutation-generation",
    "<html><body><div id='stage'></div><script>var stage = document.getElementById('stage'); requestAnimationFrame(function(){ document.title = 'title-only'; requestAnimationFrame(function(){ Object.assign(stage.style, { backgroundColor: '#ef4444' }, { backgroundColor: '#2563eb' }); requestAnimationFrame(function(){ delete stage.style.backgroundColor; }); }); });</script></body></html>"
).is_ok()).to_equal(true)

var initial_generation: i64 = -1
if val Some(state) = session.runtime_state:
    initial_generation = (
        state.runtime.interpreter.host_dom_mutation_generation
    )
expect(initial_generation).to_be_greater_than(-1)

expect(session.advance_time(16)).to_equal(1)
expect(session.current_title).to_equal("title-only")
if val Some(state) = session.runtime_state:
    expect(
        state.runtime.interpreter.host_dom_mutation_generation
    ).to_equal(initial_generation)

expect(session.advance_time(32)).to_equal(1)
var assigned_generation = initial_generation
if val Some(state) = session.runtime_state:
    assigned_generation = (
        state.runtime.interpreter.host_dom_mutation_generation
    )
    expect(
        state.runtime.interpreter.host_dom_mutation_generation
    ).to_be_greater_than(initial_generation)
expect(session.render_html_document()).to_contain(
    "background-color:#2563eb;"
)

expect(session.advance_time(48)).to_equal(1)
if val Some(state) = session.runtime_state:
    expect(
        state.runtime.interpreter.host_dom_mutation_generation
    ).to_be_greater_than(assigned_generation)
expect(session.render_html_document().contains(
    "background-color:#2563eb;"
)).to_equal(false)
```

</details>

#### observes DOM mutation generation wraparound

- observes DOM mutation generation wraparound
   - Expected: session.advance_time(16) equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("observes DOM mutation generation wraparound")
var session = BrowserSession.new()
expect(session.open_html(
    "https://example.test/dom-mutation-wrap",
    "<html><body><div id='stage'></div><script>var stage = document.getElementById('stage'); requestAnimationFrame(function(){ stage.style.cssText = 'color:#2563eb'; });</script></body></html>"
).is_ok()).to_equal(true)
if val Some(state) = session.runtime_state:
    var wrapped_state = state
    wrapped_state.runtime.interpreter.host_dom_mutation_generation = (
        9223372036854775807
    )
    wrapped_state.dom_mutation_generation = 9223372036854775807
    session.runtime_state = Some(wrapped_state)

expect(session.advance_time(16)).to_equal(1)
if val Some(state) = session.runtime_state:
    expect(
        state.runtime.interpreter.host_dom_mutation_generation
    ).to_equal(0)
expect(session.render_html_document()).to_contain(
    "style=\"color:#2563eb;\""
)
```

</details>

#### treats cssText as the latest declaration reset boundary

- treats cssText as the latest declaration reset boundary
   - Expected: session.advance_time(16) equals `1`
   - Expected: replaced does not contain `background-color:#ef4444`
   - Expected: session.advance_time(32) equals `1`
   - Expected: cleared does not contain `color:#2563eb`
   - Expected: cleared does not contain `background-color:#ef4444`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("treats cssText as the latest declaration reset boundary")
var session = BrowserSession.new()
expect(session.open_html(
    "https://example.test/css-text-reset",
    "<html><body><div id='stage' style='background-color:#ef4444'></div><script>var stage = document.getElementById('stage'); requestAnimationFrame(function(){ stage.style.cssText = 'color:#2563eb'; requestAnimationFrame(function(){ stage.style.cssText = ''; }); });</script></body></html>"
).is_ok()).to_equal(true)

expect(session.advance_time(16)).to_equal(1)  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario
val replaced = session.render_html_document()
expect(replaced).to_contain("style=\"color:#2563eb;\"")
expect(replaced.contains("background-color:#ef4444")).to_equal(false)

expect(session.advance_time(32)).to_equal(1)  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario
val cleared = session.render_html_document()
expect(cleared.contains("color:#2563eb")).to_equal(false)
expect(cleared.contains("background-color:#ef4444")).to_equal(false)
```

</details>

#### removes a declaration inherited from cssText

- var session = BrowserSession new
- "<html><body><div id='stage'></div><script>var stage = document getElementById
   - Expected: session.advance_time(16) equals `1`
   - Expected: session.advance_time(32) equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("removes a declaration inherited from cssText")
var session = BrowserSession.new()
expect(session.open_html(
    "https://example.test/css-text-remove-property",
    "<html><body><div id='stage'></div><script>var stage = document.getElementById('stage'); requestAnimationFrame(function(){ stage.style.cssText = 'color:#2563eb'; requestAnimationFrame(function(){ stage.style.removeProperty('color'); }); });</script></body></html>"
).is_ok()).to_equal(true)

expect(session.advance_time(16)).to_equal(1)
expect(session.render_html_document()).to_contain(
    "style=\"color:#2563eb;\""
)
expect(session.advance_time(32)).to_equal(1)
expect(session.render_html_document().contains(
    "color:#2563eb"
)).to_equal(false)
```

</details>

#### observes DOM bridge generation wraparound

- observes DOM bridge generation wraparound
   - Expected: session.eval_script("document.title = 'runtime-ready'").is_ok() is true
- session runtime state = Some


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("observes DOM bridge generation wraparound")
var session = BrowserSession.new()
expect(session.open_html(
    "https://example.test/dom-bridge-wrap",
    "<html><body><div id='before'></div></body></html>"
).is_ok()).to_equal(true)
expect(session.eval_script("document.title = 'runtime-ready'").is_ok()).to_equal(true)
if val Some(state) = session.runtime_state:
    var wrapped_state = state
    wrapped_state.runtime.interpreter.host_dom_bridge_generation = (
        9223372036854775807
    )
    wrapped_state.dom_bridge_generation = 9223372036854775807
    session.runtime_state = Some(wrapped_state)

expect(session.eval_script(
    "document.body.innerHTML = '<div id=\"after\"></div>'"
).is_ok()).to_equal(true)
if val Some(state) = session.runtime_state:
    expect(
        state.runtime.interpreter.host_dom_bridge_generation
    ).to_equal(0)
expect(session.render_html_document()).to_contain("id=\"after\"")
```

</details>

#### passes the actual delayed frame time to requestAnimationFrame

- passes the actual delayed frame time to requestAnimationFrame
   - Expected: session.advance_time(33) equals `1`
   - Expected: session.current_title equals `33`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("passes the actual delayed frame time to requestAnimationFrame")
var session = BrowserSession.new()
expect(session.open_html(
    "https://example.test/frame-time",
    "<html><head><title>Waiting</title></head><body><script>requestAnimationFrame(function(frameTime){ document.title = '' + frameTime; });</script></body></html>"
).is_ok()).to_be(true)

expect(session.advance_time(33)).to_equal(1)  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario
expect(session.current_title).to_equal("33")
```

</details>

#### should paint a requestAnimationFrame Promise microtask before advance returns

- should paint a requestAnimationFrame Promise microtask before advance returns
   - Artifact capture: after_step
- Open the red animation frame
   - Artifact capture: after_step
   - Evidence: artifact verified by 8 expected checks
   - Expected: initial.source_kind equals `html_ast`
   - Expected: initial.command.component_id equals `stage`
   - Expected: initial.command.width equals `32)  # oracle: pinned constant asserted by this scenario  # oracle: pinned co... (full value in folded executable source)`
   - Expected: initial.command.height equals `24)  # oracle: pinned constant asserted by this scenario  # oracle: pinned co... (full value in folded executable source)`
   - Expected: initial.command.color equals `0xFFEF4444u32`
   - Expected: initial.rect_pixel_count equals `32 * 24`
   - Expected: initial.outside_color_count equals `0)  # oracle: pinned constant asserted by this scenario  # oracle: pinned con... (full value in folded executable source)`
   - Expected: initial.skipped_command_count equals `0)  # oracle: pinned constant asserted by this scenario  # oracle: pinned con... (full value in folded executable source)`
- Advance requestAnimationFrame and its Promise microtask
   - Artifact capture: after_step
   - Evidence: artifact verified by 2 expected checks
   - Expected: callback_count equals `1)  # oracle: pinned constant asserted by this scenario  # oracle: pinned con... (full value in folded executable source)`
   - Expected: session.current_title equals `microtask`
- Observe the microtask DOM style before returning
   - Artifact capture: after_step
- Render the changed Draw IR through canonical Engine2D
   - Artifact capture: after_step
   - Evidence: artifact verified by 8 expected checks
   - Expected: changed.source_kind equals `html_ast`
   - Expected: changed.command.component_id equals `stage`
   - Expected: changed.command.width equals `32)  # oracle: pinned constant asserted by this scenario  # oracle: pinned co... (full value in folded executable source)`
   - Expected: changed.command.height equals `24)  # oracle: pinned constant asserted by this scenario  # oracle: pinned co... (full value in folded executable source)`
   - Expected: changed.command.color equals `0xFF2563EBu32`
   - Expected: changed.rect_pixel_count equals `32 * 24`
   - Expected: changed.outside_color_count equals `0)  # oracle: pinned constant asserted by this scenario  # oracle: pinned con... (full value in folded executable source)`
   - Expected: changed.skipped_command_count equals `0)  # oracle: pinned constant asserted by this scenario  # oracle: pinned con... (full value in folded executable source)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 29 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("should paint a requestAnimationFrame Promise microtask before advance returns")
val session = _open_raf_promise_microtask_frame()
val initial = _browser_animation_draw_ir_trace(session, 64, 48)
expect(initial.source_kind).to_equal("html_ast")
expect(initial.command.component_id).to_equal("stage")
expect(initial.command.width).to_equal(32)  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario
expect(initial.command.height).to_equal(24)  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario
expect(initial.command.color).to_equal(0xFFEF4444u32)
expect(initial.rect_pixel_count).to_equal(32 * 24)
expect(initial.outside_color_count).to_equal(0)  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario
expect(initial.skipped_command_count).to_equal(0)  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario

val callback_count = session.advance_time(16)
expect(callback_count).to_equal(1)  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario
expect(session.current_title).to_equal("microtask")

val rendered_html = session.render_html_document()
expect(rendered_html).to_contain("background-color:#2563eb;")

val changed = _browser_animation_draw_ir_trace(session, 64, 48)
expect(changed.source_kind).to_equal("html_ast")
expect(changed.command.component_id).to_equal("stage")
expect(changed.command.width).to_equal(32)  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario
expect(changed.command.height).to_equal(24)  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario
expect(changed.command.color).to_equal(0xFF2563EBu32)
expect(changed.rect_pixel_count).to_equal(32 * 24)
expect(changed.outside_color_count).to_equal(0)  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario
expect(changed.skipped_command_count).to_equal(0)  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario
```

</details>

#### seeds a new JavaScript runtime from the browser clock

- seeds a new JavaScript runtime from the browser clock
   - Expected: session.advance_time(1000) equals `0`
   - Expected: session.current_title equals `Waiting`
   - Expected: session.advance_time(1001) equals `0)  # oracle: pinned constant asserted by this scenario  # oracle: pinned con... (full value in folded executable source)`
   - Expected: session.advance_time(1499) equals `0)  # oracle: pinned constant asserted by this scenario  # oracle: pinned con... (full value in folded executable source)`
   - Expected: session.current_title equals `Waiting`
   - Expected: session.advance_time(1500) equals `1)  # oracle: pinned constant asserted by this scenario  # oracle: pinned con... (full value in folded executable source)`
   - Expected: session.current_title equals `Due`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("seeds a new JavaScript runtime from the browser clock")
var session = BrowserSession.new()
expect(session.advance_time(1000)).to_equal(0)  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario
expect(session.open_html(
    "https://example.test/later-runtime",
    "<html><head><title>Waiting</title></head><body><script>setTimeout(function(){ document.title = 'Due'; }, 500);</script></body></html>"
).is_ok()).to_equal(true)

expect(session.current_title).to_equal("Waiting")
expect(session.advance_time(1001)).to_equal(0)  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario
expect(session.advance_time(1499)).to_equal(0)  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario
expect(session.current_title).to_equal("Waiting")
expect(session.advance_time(1500)).to_equal(1)  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario
expect(session.current_title).to_equal("Due")
```

</details>

#### schedules a late-created timer from the current browser clock

- schedules a late-created timer from the current browser clock
   - Expected: session.advance_time(500) equals `0`
- "setTimeout
   - Expected: session.advance_time(599) equals `0`
   - Expected: session.current_title equals `Waiting`
   - Expected: session.advance_time(600) equals `1)  # oracle: pinned constant asserted by this scenario  # oracle: pinned con... (full value in folded executable source)`
   - Expected: session.current_title equals `Due`
   - Expected: session.advance_time(601) equals `0)  # oracle: pinned constant asserted by this scenario  # oracle: pinned con... (full value in folded executable source)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
expect(session.open_html(
    "https://example.test/late-timer",
    "<html><head><title>Waiting</title></head><body><script>var ready = true;</script></body></html>"
).is_ok()).to_equal(true)

expect(session.advance_time(500)).to_equal(0)  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario
expect(session.eval_script(
    "setTimeout(function(){ document.title = 'Due'; }, 100);"
).is_ok()).to_equal(true)
expect(session.advance_time(599)).to_equal(0)  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario
expect(session.current_title).to_equal("Waiting")
expect(session.advance_time(600)).to_equal(1)  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario
expect(session.current_title).to_equal("Due")
expect(session.advance_time(601)).to_equal(0)  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario
```

</details>

#### reports animation frame time from the current document origin

- var session = BrowserSession new
   - Expected: session.advance_time(1000) equals `0`
- "<html><head><title>Waiting</title></head><body><script>requestAnimationFrame
   - Expected: session.advance_time(1016) equals `1`
   - Expected: session.current_title equals `16`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
expect(session.advance_time(1000)).to_equal(0)  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario
expect(session.open_html(
    "https://example.test/later-frame",
    "<html><head><title>Waiting</title></head><body><script>requestAnimationFrame(function(frameTime){ document.title = '' + frameTime; });</script></body></html>"
).is_ok()).to_be(true)

expect(session.advance_time(1016)).to_equal(1)
expect(session.current_title).to_equal("16")
```

</details>

#### applies CSS then renders a later JavaScript frame through Engine2D

- applies CSS then renders a later JavaScript frame through Engine2D
   - Expected: session.current_title equals `SimpleReady`
   - Expected: first.ok is true
   - Expected: first.pixel_data.len() equals `64 * 48`
   - Expected: _count_color(first.pixel_data, 0xFF2563EBu32) equals `0`
   - Expected: session.advance_time(15) equals `0`
   - Expected: session.current_title equals `SimpleReady`
   - Expected: session.advance_time(16) equals `1`
   - Expected: session.current_title equals `Animated`
   - Expected: second.ok is true
   - Expected: _pixels_equal(second.pixel_data, first.pixel_data) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 29 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("applies CSS then renders a later JavaScript frame through Engine2D")
var session = BrowserSession.new()
val opened = session.open_html(
    "https://example.test/animation",
    "<!DOCTYPE html><html><head><style>#stage { width: 32px; height: 24px; background-color: #ef4444; }</style></head><body><script type='text/simple'>title \"SimpleReady\"\nbody_html '<div id=\"stage\"></div>'</script><script>requestAnimationFrame(function(frameTime){ var stage = document.getElementById('stage'); stage.style.backgroundColor = '#2563eb'; document.title = 'Animated'; });</script></body></html>"
)
match opened:
    Err(e):
        fail("Expected scripted page to open: {e}")
    Ok(_):
        expect(session.current_title).to_equal("SimpleReady")
        expect(session.current_body_html).to_contain("id=\"stage\"")

val first = session.render_to_pixels(64, 48)
expect(first.ok).to_equal(true)
expect(first.pixel_data.len()).to_equal(64 * 48)
expect(_count_color(first.pixel_data, 0xFFEF4444u32)).to_be_greater_than(0)
expect(_count_color(first.pixel_data, 0xFF2563EBu32)).to_equal(0)

expect(session.advance_time(15)).to_equal(0)
expect(session.current_title).to_equal("SimpleReady")
expect(session.advance_time(16)).to_equal(1)
expect(session.current_title).to_equal("Animated")

val second = session.render_to_pixels(64, 48)
expect(second.ok).to_equal(true)
expect(_count_color(second.pixel_data, 0xFF2563EBu32)).to_be_greater_than(0)
expect(_pixels_equal(second.pixel_data, first.pixel_data)).to_equal(false)
```

</details>

#### applies CSS from a SimpleScript animation frame through Draw IR

- applies CSS from a SimpleScript animation frame through Draw IR
- Render the HTML and CSS frame before the SimpleScript callback
   - Expected: initial.command.color equals `0xFFEF4444u32`
- Advance the production SimpleScript animation clock
   - Expected: session.advance_time(16) equals `1`
   - Expected: session.simple_script_callback_count() equals `1`
   - Expected: animated.command.color equals `0xFF2563EBu32`
   - Expected: animated.command.color == initial.command.color is false

<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("applies CSS from a SimpleScript animation frame through Draw IR")
step("Render the HTML and CSS frame before the SimpleScript callback")
var session = BrowserSession.new()
expect(session.open_html(
    "https://example.test/simple-script-draw-ir-animation",
    "<!DOCTYPE html><html><head><style>#stage { width: 32px; height: 24px; background-color: #ef4444; }</style></head><body><div id='stage'></div><script type='text/simple'>callback 41|style_html '<style>#stage { width: 32px; height: 24px; background-color: #2563eb; }</style>'\nanimation_frame 41</script></body></html>"
).is_ok()).to_equal(true)
val initial = _browser_animation_draw_ir_trace(session, 64, 48)
_expect_browser_animation_draw_ir_frame(initial)
expect(initial.command.color).to_equal(0xFFEF4444u32)

step("Advance the production SimpleScript animation clock")
expect(session.advance_time(16)).to_equal(1)
expect(session.simple_script_callback_count()).to_equal(1)
val animated = _browser_animation_draw_ir_trace(session, 64, 48)
_expect_browser_animation_draw_ir_frame(animated)
expect(animated.command.color).to_equal(0xFF2563EBu32)
expect(animated.command.color == initial.command.color).to_equal(false)
```

</details>

#### cancels copied SimpleScript callbacks after body replacement

- cancels copied SimpleScript callbacks after body replacement
   - Artifact capture: after_step
- Render the pre-replacement CSS frame through Draw IR and Engine2D
   - Artifact capture: after_step
   - Evidence: artifact verified by 1 expected check
   - Expected: before.command.color equals `0xFFEF4444u32`
- Replace the document and discard later copied callbacks
   - Artifact capture: after_step
   - Evidence: artifact verified by 3 expected checks
   - Expected: session.advance_time(10) equals `2`
   - Expected: session.current_title equals `before-replacement`
   - Expected: session.style_revision equals `before_style_revision`
- Keep the replacement CSS frame red in canonical Draw IR and Engine2D
   - Artifact capture: after_step
   - Evidence: artifact verified by 2 expected checks
   - Expected: after.command.color equals `0xFFEF4444u32`
   - Expected: after.command.color == 0xFF2563EBu32 is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 28 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("cancels copied SimpleScript callbacks after body replacement")
step("Render the pre-replacement CSS frame through Draw IR and Engine2D")
var session = BrowserSession.new()
expect(session.open_html(
    "https://example.test/simple-script-stale-callback",
    "<!DOCTYPE html><html><head><style>#stage{width:32px;height:24px;background-color:#ef4444}</style></head><body><div id='stage'></div><script type='text/simple'>callback 71|title \"before-replacement\"\ncallback 72|body_html '<div id=\"stage\"></div>'\ncallback 73|style_html '<style>#stage{width:32px;height:24px;background-color:#2563eb}</style>'\ntimeout 71 10\ntimeout 72 10\ntimeout 73 10</script></body></html>"
).is_ok()).to_equal(true)
val before_generation = session.document_generation().value
val before_style_revision = session.style_revision
val before = _browser_animation_draw_ir_trace(session, 64, 48)
_expect_browser_animation_draw_ir_frame(before)
expect(before.command.color).to_equal(0xFFEF4444u32)

step("Replace the document and discard later copied callbacks")
expect(session.advance_time(10)).to_equal(2)
expect(session.document_generation().value).to_equal(
    before_generation + 1
)
expect(session.current_title).to_equal("before-replacement")
expect(session.current_body_html).to_contain("id=\"stage\"")
expect(session.style_revision).to_equal(before_style_revision)

step("Keep the replacement CSS frame red in canonical Draw IR and Engine2D")
val after = _browser_animation_draw_ir_trace(session, 64, 48)
_expect_browser_animation_draw_ir_frame(after)
expect(after.command.color).to_equal(0xFFEF4444u32)
expect(after.command.color == 0xFF2563EBu32).to_equal(false)
```

</details>

#### should preserve an active animation across an unrelated SimpleScript stylesheet update

- should preserve an active animation across an unrelated SimpleScript stylesheet update
   - Artifact capture: after_step
- Render the active animation before the SimpleScript timer
   - Expected: initial.command.color equals `0xFFEF4444u32`
- Apply an unrelated stylesheet rule from the SimpleScript timer
   - Artifact capture: after_step
   - Evidence: artifact verified by 2 expected checks
   - Expected: session.advance_time(500) equals `1`
   - Expected: session.style_revision equals `prior_style_revision + 1`
   - Expected: session.current_style_html contains `#other{color:#16a34a}`
- Keep the animation midpoint in canonical Draw IR and Engine2D pixels
   - Expected: midpoint.command.color equals `0xFF8A5397u32`
   - Expected: midpoint.rect_pixel_count equals `32 * 24`
   - Expected: midpoint.skipped_command_count equals `0)  # oracle: pinned constant asserted by this scenario  # oracle: pinned con... (full value in folded executable source)`



<details>
<summary>Executable SSpec</summary>

Runnable source: 36 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("should preserve an active animation across an unrelated SimpleScript stylesheet update")
step("Render the active animation before the SimpleScript timer")
val animation_css = (
    "@keyframes Pulse{from{background-color:#ef4444}" +
    "to{background-color:#2563eb}}" +
    "#stage{width:32px;height:24px;" +
    "animation:Pulse 1000ms linear forwards}"
)
var session = BrowserSession.new()
expect(session.open_html(
    "https://example.test/simple-script-stylesheet-animation",
    "<style>{animation_css}</style><div id='stage'></div>" +
    "<script type='text/simple'>" +
    "callback 51|style_html '<style>{animation_css}" +
    "#other{color:#16a34a}</style>'\n" +
    "timeout 51 500</script>"
).is_ok()).to_be(true)
val initial = _browser_animation_draw_ir_trace(session, 64, 48)
_expect_browser_animation_draw_ir_frame(initial)
expect(initial.command.color).to_equal(0xFFEF4444u32)
val prior_style_revision = session.style_revision

step("Apply an unrelated stylesheet rule from the SimpleScript timer")
expect(session.advance_time(500)).to_equal(1)
expect(session.style_revision).to_equal(prior_style_revision + 1)
expect(session.current_style_html).to_contain(
    "#other{color:#16a34a}"
)
val midpoint = _browser_animation_draw_ir_trace(session, 64, 48)

step("Keep the animation midpoint in canonical Draw IR and Engine2D pixels")
_expect_browser_animation_draw_ir_frame(midpoint)
expect(midpoint.command.color).to_equal(0xFF8A5397u32)
expect(midpoint.rect_pixel_count).to_equal(32 * 24)
expect(midpoint.skipped_command_count).to_equal(0)
```

</details>

#### repaints selector-driven element style mutations from animation frames

- repaints selector-driven element style mutations from animation frames
   - Expected: session.advance_time(16) equals `1`
   - Expected: session.current_title equals `1:true`
   - Expected: _pixels_equal(second.pixel_data, first.pixel_data) is false
   - Expected: session.advance_time(32) equals `1`
   - Expected: _pixels_equal(third.pixel_data, second.pixel_data) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("repaints selector-driven element style mutations from animation frames")
var session = BrowserSession.new()
expect(session.open_html(
    "https://example.test/selector-animation",
    "<!DOCTYPE html><html><head><style>#stage { width: 32px; height: 24px; background-color: #ef4444; }</style></head><body><div id='stage'></div><script>var stage = document.getElementById('stage'); requestAnimationFrame(function(){ stage.style.backgroundColor = '#2563eb'; document.title = document.querySelectorAll('#stage').length + ':' + (document.querySelector('#stage') === stage); requestAnimationFrame(function(){ stage.style.setProperty('background-color', '#16a34a'); }); });</script></body></html>"
).is_ok()).to_equal(true)

val first = session.render_to_pixels(64, 48)
expect(_count_color(first.pixel_data, 0xFFEF4444u32)).to_be_greater_than(0)
expect(session.advance_time(16)).to_equal(1)
expect(session.current_title).to_equal("1:true")

val second = session.render_to_pixels(64, 48)
expect(_count_color(second.pixel_data, 0xFF2563EBu32)).to_be_greater_than(0)
expect(_pixels_equal(second.pixel_data, first.pixel_data)).to_equal(false)

expect(session.advance_time(32)).to_equal(1)
val third = session.render_to_pixels(64, 48)
expect(_count_color(third.pixel_data, 0xFF16A34Au32)).to_be_greater_than(0)
expect(_pixels_equal(third.pixel_data, second.pixel_data)).to_equal(false)
```

</details>

#### preserves scripted body identity and inline style in canonical rendering

- preserves scripted body identity and inline style in canonical rendering
   - Expected: session.advance_time(16) equals `1`
   - Expected: session.current_title equals `body-preserved`
   - Expected: _pixels_equal(second.pixel_data, first.pixel_data) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("preserves scripted body identity and inline style in canonical rendering")
var session = BrowserSession.new()
expect(session.open_html(
    "https://example.test/body-style-animation",
    "<!DOCTYPE html><html><head><style>body { width: 32px; height: 24px; }</style></head><body id='before' class='cold' style='background-color:#ef4444'><script>requestAnimationFrame(function(){ document.body.innerHTML = '<div id=\"child\"></div>'; var preserved = document.querySelector('#before') === document.body && document.querySelector('.cold') === document.body && document.body.style.backgroundColor === '#ef4444'; document.body.id = 'after'; document.body.className = 'hot'; document.body.style.backgroundColor = '#16a34a'; document.title = preserved ? 'body-preserved' : 'body-lost'; });</script></body></html>"
).is_ok()).to_equal(true)

val first = session.render_to_pixels(64, 48)
expect(_count_color(first.pixel_data, 0xFFEF4444u32)).to_be_greater_than(0)
expect(session.advance_time(16)).to_equal(1)
expect(session.current_title).to_equal("body-preserved")
val rendered = session.render_html_document()
expect(rendered).to_contain("id=\"after\"")
expect(rendered).to_contain("class=\"hot\"")
expect(rendered).to_contain("background-color:#16a34a;")
val second = session.render_to_pixels(64, 48)
expect(_count_color(second.pixel_data, 0xFF16A34Au32)).to_be_greater_than(0)
expect(_pixels_equal(second.pixel_data, first.pixel_data)).to_equal(false)
```

</details>

#### publishes body replacements to selectors within the same animation callback

- publishes body replacements to selectors within the same animation callback
   - Expected: session.advance_time(16) equals `1`
   - Expected: session.current_title equals `same-turn`
   - Expected: session.advance_time(32) equals `1`
   - Expected: session.current_title equals `same-next:computed`


<details>
<summary>Executable SSpec</summary>

Runnable source: 32 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("publishes body replacements to selectors within the same animation callback")
var session = BrowserSession.new()
expect(session.open_html(
    "https://example.test/same-callback-dom",
    "<!DOCTYPE html><html><body><div style='width:32px;height:24px;background-color:#ef4444'></div><script>var saved = null; requestAnimationFrame(function(){ document.body.innerHTML = '<div id=\"next\" style=\"width:32px;height:24px;background-color:#ef4444\"></div>'; saved = document.getElementById('next'); saved.style.backgroundColor = '#16a34a'; document.title = document.querySelector('#next') === saved ? 'same-turn' : 'stale'; requestAnimationFrame(function(){ var same = document.getElementById('next') === saved; document.body['innerHTML'] = '<div id=\"last\" style=\"width:32px;height:24px;background-color:#ef4444\"></div>'; var last = document.querySelector('#last'); last.style.setProperty('background-color', '#2563eb'); document.title = (same && saved !== last && document.getElementById('last') === last) ? 'same-next:computed' : 'lost'; }); });</script></body></html>"
).is_ok()).to_equal(true)

val first = session.render_to_pixels(64, 48)
expect(_count_color(
    first.pixel_data, 0xFFEF4444u32
)).to_be_greater_than(0)

expect(session.advance_time(16)).to_equal(1)
expect(session.current_title).to_equal("same-turn")
val second = session.render_to_pixels(64, 48)
expect(_count_color(
    second.pixel_data, 0xFF16A34Au32
)).to_be_greater_than(0)
expect(_pixels_equal(
    second.pixel_data, first.pixel_data
)).to_equal(false)

expect(session.advance_time(32)).to_equal(1)
expect(session.current_title).to_equal("same-next:computed")
val third = session.render_to_pixels(64, 48)
expect(_count_color(
    third.pixel_data, 0xFF2563EBu32
)).to_be_greater_than(0)
expect(_pixels_equal(
    third.pixel_data, second.pixel_data
)).to_equal(false)
```

</details>

#### bounds retained DOM bridge allocations without aliasing detached nodes

- bounds retained DOM bridge allocations without aliasing detached nodes
   - Expected: session.current_title equals `distinct`
- session runtime state = Some
   - Expected: exercised is true
   - Expected: admitted_checked is true
   - Expected: object_limit_checked is true
   - Expected: byte_limit_checked is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 66 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("bounds retained DOM bridge allocations without aliasing detached nodes")
var session = BrowserSession.new()
expect(session.open_html(
    "https://example.test/dom-retention-budget",
    "<html><body><div id='kept'></div></body></html>"
).is_ok()).to_equal(true)
expect(session.eval_script(
    "document.title = 'runtime-ready'"
).is_ok()).to_equal(true)
var exercised = false
var admitted_checked = false
var object_limit_checked = false
var byte_limit_checked = false
if val Some(state) = session.runtime_state:
    exercised = true
    var bounded_state = state
    # list + fresh element/style pairs for implicit html, head, and div
    val replacement_object_count: i64 = 7
    bounded_state.runtime.interpreter.host_dom_mutation_retained_objects = (
        JS_HOST_DOM_MUTATION_MAX_RETAINED_OBJECTS -
        replacement_object_count
    )
    session.runtime_state = Some(bounded_state)
    expect(session.eval_script(
        "var old = document.getElementById('kept'); document.body.innerHTML = '<div id=\"last\"></div>'; var next = document.getElementById('last'); document.title = (old !== null && next !== null && old !== next) ? 'distinct' : 'aliased';"
    ).is_ok()).to_equal(true)
    expect(session.current_title).to_equal("distinct")
    expect(session.current_body_html).to_contain("id=\"last\"")
    if val Some(after_first) = session.runtime_state:
        admitted_checked = true
        val allocated = after_first.runtime.interpreter.object_store.next_id
        expect(session.eval_script(
            "document.body.innerHTML = '<div id=\"rejected\"></div>'"
        ).is_ok()).to_equal(true)
        if val Some(after_limit) = session.runtime_state:
            object_limit_checked = true
            expect(
                after_limit.runtime.interpreter.object_store.next_id
            ).to_equal(allocated)
        expect(session.current_body_html).to_contain("id=\"last\"")
        expect(session.current_body_html.contains(
            "id=\"rejected\""
        )).to_equal(false)
        if val Some(after_object_limit) = session.runtime_state:
            var byte_bounded_state = after_object_limit
            byte_bounded_state.runtime.interpreter.host_dom_mutation_retained_objects = 0
            byte_bounded_state.runtime.interpreter.host_dom_mutation_retained_bytes = (
                JS_HOST_DOM_MUTATION_MAX_RETAINED_BYTES
            )
            session.runtime_state = Some(byte_bounded_state)
            expect(session.eval_script(
                "document.body.innerHTML = '<div id=\"byte-rejected\"></div>'"
            ).is_ok()).to_equal(true)
            if val Some(after_byte_limit) = session.runtime_state:
                byte_limit_checked = true
                expect(
                    after_byte_limit.runtime.interpreter.object_store.next_id
                ).to_equal(allocated)
            expect(session.current_body_html.contains(
                "id=\"byte-rejected\""
            )).to_equal(false)
expect(exercised).to_equal(true)
expect(admitted_checked).to_equal(true)
expect(object_limit_checked).to_equal(true)
expect(byte_limit_checked).to_equal(true)
```

</details>

#### keeps the prior body when a synchronous mutation plan exceeds its element bound

- keeps the prior body when a synchronous mutation plan exceeds its element bound
   - Expected: session.current_title equals `bounded`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("keeps the prior body when a synchronous mutation plan exceeds its element bound")
var session = BrowserSession.new()
expect(session.open_html(
    "https://example.test/bounded-dom",
    "<html><body><div id='kept'>safe</div></body></html>"
).is_ok()).to_equal(true)
var oversized = ""
var element_count = 0
while element_count < 4096:
    oversized = oversized + "<i></i>"
    element_count = element_count + 1
expect(session.eval_script(
    "document.body.innerHTML = '" + oversized +
    "'; document.title = document.getElementById('kept') !== null ? 'bounded' : 'replaced';"
).is_ok()).to_equal(true)
expect(session.current_title).to_equal("bounded")
expect(session.current_body_html).to_contain("id='kept'")
```

</details>

#### renders start midpoint and end frames from CSS keyframes

- renders start midpoint and end frames from CSS keyframes
   - Expected: opened.is_ok() is true
   - Expected: first.ok is true
   - Expected: session.advance_time(500) equals `0`
   - Expected: middle.ok is true
   - Expected: _pixels_equal(middle.pixel_data, first.pixel_data) is false
   - Expected: session.advance_time(1000) equals `0`
   - Expected: last.ok is true
   - Expected: _pixels_equal(last.pixel_data, middle.pixel_data) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("renders start midpoint and end frames from CSS keyframes")
var session = BrowserSession.new()
val opened = session.open_html(
    "https://example.test/css-animation",
    "<!DOCTYPE html><html><head><style>@keyframes Pulse { from { background-color: #ef4444; } to { background-color: #2563eb; } } #stage { width: 32px; height: 24px; animation-name: Pulse; animation-duration: 1000ms; animation-timing-function: linear; animation-fill-mode: forwards; }</style></head><body><div id='stage'></div></body></html>"
)
expect(opened.is_ok()).to_equal(true)

val first = session.render_to_pixels(64, 48)
expect(first.ok).to_equal(true)
expect(_count_color(first.pixel_data, 0xFFEF4444u32)).to_be_greater_than(0)

expect(session.advance_time(500)).to_equal(0)
val middle = session.render_to_pixels(64, 48)
expect(middle.ok).to_equal(true)
expect(_pixels_equal(middle.pixel_data, first.pixel_data)).to_equal(false)

expect(session.advance_time(1000)).to_equal(0)
val last = session.render_to_pixels(64, 48)
expect(last.ok).to_equal(true)
expect(_count_color(last.pixel_data, 0xFF2563EBu32)).to_be_greater_than(0)
expect(_pixels_equal(last.pixel_data, middle.pixel_data)).to_equal(false)
```

</details>

#### starts and restarts script-added animations from local time zero

- starts and restarts script-added animations from local time zero
   - Expected: session.advance_time(500) equals `0`
   - Expected: session.advance_time(1000) equals `0`
   - Expected: session.advance_time(1500) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 46 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("starts and restarts script-added animations from local time zero")
var session = BrowserSession.new()
expect(session.open_html(
    "https://example.test/dynamic-css-animation",
    "<!DOCTYPE html><html><head><style>@keyframes Pulse { from { background-color: #ef4444; } to { background-color: #2563eb; } } #a, #b { width: 32px; height: 16px; background-color: #ef4444; } #a, .running { animation-name: Pulse; animation-duration: 1000ms; animation-timing-function: linear; animation-fill-mode: forwards; }</style></head><body><div id='a'></div><div id='b'></div></body></html>"
).is_ok()).to_equal(true)

expect(session.advance_time(500)).to_equal(0)
val before_start = session.render_to_pixels(64, 48)
expect(session.eval_script(
    "document.getElementById('b').className = 'running'"
).is_ok()).to_equal(true)
val local_start = session.render_to_pixels(64, 48)
expect(_pixels_equal(
    local_start.pixel_data, before_start.pixel_data
)).to_equal(true)

expect(session.advance_time(1000)).to_equal(0)
val first_midpoint = session.render_to_pixels(64, 48)
expect(_pixels_equal(
    first_midpoint.pixel_data, local_start.pixel_data
)).to_equal(false)
expect(session.eval_script(
    "document.getElementById('b').className = ''"
).is_ok()).to_equal(true)
val before_restart = session.render_to_pixels(64, 48)
expect(_count_color(
    before_restart.pixel_data, 0xFFEF4444u32
)).to_be_greater_than(0)
expect(_count_color(
    before_restart.pixel_data, 0xFF2563EBu32
)).to_be_greater_than(0)

expect(session.eval_script(
    "document.getElementById('b').className = 'running'"
).is_ok()).to_equal(true)
val local_restart = session.render_to_pixels(64, 48)
expect(_pixels_equal(
    local_restart.pixel_data, before_restart.pixel_data
)).to_equal(true)
expect(session.advance_time(1500)).to_equal(0)
val restarted_midpoint = session.render_to_pixels(64, 48)
expect(_pixels_equal(
    restarted_midpoint.pixel_data, first_midpoint.pixel_data
)).to_equal(true)
```

</details>

#### preserves animation time across unrelated classes pause and resume

- preserves animation time across unrelated classes pause and resume
   - Expected: session.advance_time(500) equals `0`
   - Expected: reference.advance_time(500) equals `0`
   - Expected: session.advance_time(1000) equals `0`
   - Expected: reference.advance_time(1000) equals `0`
   - Expected: session.advance_time(1500) equals `0`
   - Expected: session.advance_time(2000) equals `0`
   - Expected: reference.advance_time(1500) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 62 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("preserves animation time across unrelated classes pause and resume")
val html = "<!DOCTYPE html><html><head><style>@keyframes Pulse { from { background-color: #ef4444; } to { background-color: #2563eb; } } #stage { width: 32px; height: 24px; background-color: #ef4444; } .running { animation: Pulse 2000ms linear forwards; } .paused { animation-play-state: paused; }</style></head><body><div id='stage' class='running'></div></body></html>"
var session = BrowserSession.new()
var reference = BrowserSession.new()
expect(session.open_html(
    "https://example.test/animation-pause", html
).is_ok()).to_equal(true)
expect(reference.open_html(
    "https://example.test/animation-pause-reference", html
).is_ok()).to_equal(true)
expect(_pixels_equal(
    session.render_to_pixels(64, 48).pixel_data,
    reference.render_to_pixels(64, 48).pixel_data
)).to_equal(true)

expect(session.advance_time(500)).to_equal(0)
expect(reference.advance_time(500)).to_equal(0)
expect(session.eval_script(
    "document.getElementById('stage').className = 'running unrelated'"
).is_ok()).to_equal(true)
val unrelated = session.render_to_pixels(64, 48)
val reference_500 = reference.render_to_pixels(64, 48)
expect(_pixels_equal(
    unrelated.pixel_data, reference_500.pixel_data
)).to_equal(true)

expect(session.advance_time(1000)).to_equal(0)
expect(reference.advance_time(1000)).to_equal(0)
val running = session.render_to_pixels(64, 48)
val reference_1000 = reference.render_to_pixels(64, 48)
expect(_pixels_equal(
    running.pixel_data, reference_1000.pixel_data
)).to_equal(true)
expect(session.eval_script(
    "document.getElementById('stage').className = 'running unrelated paused'"
).is_ok()).to_equal(true)
val paused = session.render_to_pixels(64, 48)
expect(_pixels_equal(
    paused.pixel_data, running.pixel_data
)).to_equal(true)

expect(session.advance_time(1500)).to_equal(0)
val still_paused = session.render_to_pixels(64, 48)
expect(_pixels_equal(
    still_paused.pixel_data, paused.pixel_data
)).to_equal(true)
expect(session.eval_script(
    "document.getElementById('stage').className = 'running unrelated'"
).is_ok()).to_equal(true)
val resumed = session.render_to_pixels(64, 48)
expect(_pixels_equal(
    resumed.pixel_data, paused.pixel_data
)).to_equal(true)

expect(session.advance_time(2000)).to_equal(0)
expect(reference.advance_time(1500)).to_equal(0)
val continued = session.render_to_pixels(64, 48)
val reference_1500 = reference.render_to_pixels(64, 48)
expect(_pixels_equal(
    continued.pixel_data, reference_1500.pixel_data
)).to_equal(true)
```

</details>

#### starts external stylesheet animation when the stylesheet applies

- starts external stylesheet animation when the stylesheet applies
   - Expected: before_style_timers equals `0`
   - Expected: middle_timers equals `0`
   - Expected: _pixels_equal(middle.pixel_data, first.pixel_data) is false
   - Expected: end_timers equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 47 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("starts external stylesheet animation when the stylesheet applies")
var session = BrowserSession.new()
expect(session.begin_network_navigation(
    "https://example.test/external-animation", "GET", "", "", ""
).is_ok()).to_equal(true)
match session.take_pending_request():
    Some(document_request):
        expect(session.commit_network_response(BrowserResponse.create(
            request_id: document_request.id,
            kind: "document",
            url: document_request.url,
            status: 200,
            headers: "",
            body: "<html><head><link rel='stylesheet' href='/animation.css'></head><body><div id='stage'></div></body></html>",
            error: ""
        )).is_ok()).to_equal(true)
    nil:
        fail("Expected animation document request")

val style_request = session.take_pending_request()
val before_style_timers = session.advance_time(500)
match style_request:
    Some(request):
        expect(session.commit_network_response(BrowserResponse.create(
            request_id: request.id,
            kind: "style",
            url: request.url,
            status: 200,
            headers: "",
            body: "@keyframes Pulse { from { background-color: #ef4444; } to { background-color: #2563eb; } } #stage { width: 32px; height: 24px; animation-name: Pulse; animation-duration: 1000ms; animation-timing-function: linear; animation-fill-mode: forwards; }",
            error: ""
        )).is_ok()).to_equal(true)
    nil:
        fail("Expected external animation stylesheet request")

val first = session.render_to_pixels(64, 48)
expect(before_style_timers).to_equal(0)
expect(_count_color(first.pixel_data, 0xFFEF4444u32)).to_be_greater_than(0)
val middle_timers = session.advance_time(1000)
val middle = session.render_to_pixels(64, 48)
expect(middle_timers).to_equal(0)
expect(_pixels_equal(middle.pixel_data, first.pixel_data)).to_equal(false)
val end_timers = session.advance_time(1500)
val last = session.render_to_pixels(64, 48)
expect(end_timers).to_equal(0)
expect(_count_color(last.pixel_data, 0xFF2563EBu32)).to_be_greater_than(0)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 24 |
| Active scenarios | 24 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Requirements:** `doc/02_requirements/feature/simple_web_browser_engine_production_hardening.md`
- **Plan:** `doc/03_plan/sys_test/html_css_spec_traceability.md`
- **Design:** `doc/05_design/simple_web_browser_engine_production_hardening.md`
- **Research:** `doc/01_research/local/simple_web_browser_engine_production_hardening.md`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-INTEGRATION`
- `REQ-WEB-BROWSER-003`
- `REQ-WEB-BROWSER-004`
- `REQ-WEB-BROWSER-005`
- `REQ-WEB-BROWSER-006`
- `REQ-WEB-BROWSER-007`
- `REQ-WEB-BROWSER-017`
- `REQ-WEB-BROWSER-021`
- `REQ-WEB-BROWSER-021.`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `57bfda20bb41ee1bce4b5e1e555bc4d3955c6779124c93b2877655831870fc62`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `57bfda20bb41ee1bce4b5e1e555bc4d3955c6779124c93b2877655831870fc62`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `57bfda20bb41ee1bce4b5e1e555bc4d3955c6779124c93b2877655831870fc62`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **77/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/02_integration/rendering/browser_session_script_css_animation_spec.spl
mirror: doc/06_spec/02_integration/rendering/browser_session_script_css_animation_spec.md (current)
findings: 11 blockers: 1
  narrative=100 structure=80 oracle=70
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=77; blocker cap makes effective=49
doc/06_spec/02_integration/rendering/browser_session_script_css_animation_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/02_integration/rendering/browser_session_script_css_animation_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/02_integration/rendering/browser_session_script_css_animation_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 67 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/02_integration/rendering/browser_session_script_css_animation_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 7 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/02_integration/rendering/browser_session_script_css_animation_spec.spl:173:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should cascade duplicate keyframe offsets into Draw IR pixels' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/02_integration/rendering/browser_session_script_css_animation_spec.spl:173:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should cascade duplicate keyframe offsets into Draw IR pixels' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/02_integration/rendering/browser_session_script_css_animation_spec.spl:200:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should trace JavaScript pause and resume through deterministic Draw IR frames' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/02_integration/rendering/browser_session_script_css_animation_spec.spl:200:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should trace JavaScript pause and resume through deterministic Draw IR frames' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/02_integration/rendering/browser_session_script_css_animation_spec.spl:248:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'tracks only DOM-observable animation frame mutations' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/02_integration/rendering/browser_session_script_css_animation_spec.spl:397:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should paint a requestAnimationFrame Promise microtask before advance returns' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/02_integration/rendering/browser_session_script_css_animation_spec.spl:578:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should preserve an active animation across an unrelated SimpleScript stylesheet update' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->

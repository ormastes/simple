# Browser Animation Clock Wiring

> Proves the frame clock is connected end-to-end: advancing the session's

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Browser Animation Clock Wiring

Proves the frame clock is connected end-to-end: advancing the session's

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/01_unit/browser_engine/browser_animation_clock_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Proves the frame clock is connected end-to-end: advancing the session's
monotonic time (the same call `app.browser.render_adapter.
browser_engine_animated_frames` makes per GUI frame) must

- run requestAnimationFrame callbacks — at least twice across 2+ ticks, and
- change a CSS-@keyframes-animated property between ticks, observable in the
  actual rendered pixel output.

This is the wiring gate for
doc/08_tracking/bug/browser_css_animation_clock_not_connected_2026-07-26.md.

## Scenarios

### browser animation clock

#### fires a chained requestAnimationFrame callback on each of 2+ clock ticks

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- fires a chained requestAnimationFrame callback on each of 2+ clock ticks
- load a page whose rAF callback increments a counter and re-registers
- advance the session clock across two frame boundaries
- assert the callback ran at least twice


<details>
<summary>Executable SSpec</summary>

Runnable source: 32 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
step("fires a chained requestAnimationFrame callback on each of 2+ clock ticks")
"""A rAF callback that re-registers itself must run once per advanced
frame boundary — two ticks, two invocations, observable both in the
script's own counter and the DOM title it writes."""
step("load a page whose rAF callback increments a counter and re-registers")
var session = BrowserSession.new()
val html = "<html><body><div id='c'>0</div><script>" +
    "var ticks = 0;" +
    "function loop(t) { ticks = ticks + 1;" +
    " document.title = 'tick-' + ticks;" +
    " requestAnimationFrame(loop); }" +
    "requestAnimationFrame(loop);" +
    "</script></body></html>"
match session.open_html("https://example.test/raf-clock.html", html):
    Ok(_): pass_do_nothing
    Err(err): fail("expected rAF page to load: {err}")

step("advance the session clock across two frame boundaries")
val ran_first = session.advance_time(20)
val ran_second = session.advance_time(40)
assert_true(ran_first > 0)
assert_true(ran_second > 0)

step("assert the callback ran at least twice")
match session.eval_script("ticks"):
    Ok(value):
        match value:
            JsValue.Number(n): assert_true(n >= 2.0)
            _: fail("expected numeric tick counter")
    Err(err): fail("expected tick counter to evaluate: {err}")
assert_contains(session.render_html_document(), "tick-")
```

</details>

#### renders different pixels for a CSS keyframes animation across two ticks

- renders different pixels for a CSS keyframes animation across two ticks
- load a page animating background-color red to blue over 1000ms
- render the frame at t=0
- advance the clock to t=500ms and render again
- advance the clock to t=900ms and render a third frame
- assert successive ticks painted different animated frames
   - Expected: frame_start.len() equals `CLOCK_W * CLOCK_H`


<details>
<summary>Executable SSpec</summary>

Runnable source: 35 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
step("renders different pixels for a CSS keyframes animation across two ticks")
"""A red-to-blue @keyframes animation sampled by the session clock
must paint distinct frames at t=0 and t=500ms of a 1000ms run —
the animated property change is observable in real pixel output."""
step("load a page animating background-color red to blue over 1000ms")
var session = BrowserSession.new()
# Raw single-quoted strings: `{margin:0}` in a double-quoted literal
# is parsed as string interpolation (documented spec-source landmine).
val html = '<html><head><style>' +
    'html,body{margin:0}' +
    '@keyframes fade{from{background-color:#dc2626}' +
    'to{background-color:#2563eb}}' +
    '#box{width:8px;height:8px;background-color:#dc2626;' +
    'animation:fade 1000ms linear forwards}' +
    '</style></head><body><div id="box"></div></body></html>'
match session.open_html("https://example.test/css-clock.html", html):
    Ok(_): pass_do_nothing
    Err(err): fail("expected animation page to load: {err}")

step("render the frame at t=0")
val frame_start = session.render_to_pixels(CLOCK_W, CLOCK_H).pixel_data

step("advance the clock to t=500ms and render again")
val _ = session.advance_time(500)
val frame_mid = session.render_to_pixels(CLOCK_W, CLOCK_H).pixel_data

step("advance the clock to t=900ms and render a third frame")
val _2 = session.advance_time(900)
val frame_late = session.render_to_pixels(CLOCK_W, CLOCK_H).pixel_data

step("assert successive ticks painted different animated frames")
expect(frame_start.len()).to_equal(CLOCK_W * CLOCK_H)
assert_true(_pixels_differ(frame_start, frame_mid))
assert_true(_pixels_differ(frame_mid, frame_late))
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
- `REQ-WEB-BROWSER-004`
- `REQ-WEB-BROWSER-012`
- `REQ-SSPEC-BROWSER_ENGINE`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `19054f61d18ca62be240a31da165ae13438c1dc88260c008f5152f0945de4cb5`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `19054f61d18ca62be240a31da165ae13438c1dc88260c008f5152f0945de4cb5`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `19054f61d18ca62be240a31da165ae13438c1dc88260c008f5152f0945de4cb5`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/browser_engine/browser_animation_clock_spec.spl
mirror: doc/06_spec/01_unit/browser_engine/browser_animation_clock_spec.md (current)
findings: 5 blockers: 1
  narrative=100 structure=100 oracle=100
  traceability=60 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=88; blocker cap makes effective=49
doc/06_spec/01_unit/browser_engine/browser_animation_clock_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/browser_engine/browser_animation_clock_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/browser_engine/browser_animation_clock_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 3 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/browser_engine/browser_animation_clock_spec.spl:47:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'fires a chained requestAnimationFrame callback on each of 2+ clock ticks' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/browser_engine/browser_animation_clock_spec.spl:81:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'renders different pixels for a CSS keyframes animation across two ticks' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

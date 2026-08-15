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
| Updated | 2026-08-15 |
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

- load a page whose rAF callback increments a counter and re-registers
- advance the session clock across two frame boundaries
- assert the callback ran at least twice


<details>
<summary>Executable SSpec</summary>

Runnable source: 27 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

- load a page animating background-color red to blue over 1000ms
- render the frame at t=0
- advance the clock to t=500ms and render again
- advance the clock to t=900ms and render a third frame
- assert successive ticks painted different animated frames
   - Expected: frame_start.len() equals `CLOCK_W * CLOCK_H`


<details>
<summary>Executable SSpec</summary>

Runnable source: 30 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

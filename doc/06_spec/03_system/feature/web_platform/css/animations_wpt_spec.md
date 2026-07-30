# CSS Animation Frame Preservation

> Proves start, signed-delay seek, midpoint, and filled-end animation frames

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# CSS Animation Frame Preservation

Proves start, signed-delay seek, midpoint, and filled-end animation frames

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/feature/web_platform/css/animations_wpt_spec.spl` |
| Updated | 2026-07-30 |
| Generator | Manual mirror; qualified docgen pending |

Proves the supported keyframe subset at its start, negative-delay seek,
midpoint, and filled end through web semantics, layout, canonical Draw IR, and
exact expected-color Engine2D coverage/count. Web Animations compositing and
unsupported properties remain outside this bounded profile.

## Scenarios

### REQ-WEB-BROWSER-003/004/006: CSS animation frames

#### should preserve the animation feature at its exact start frame

- Resolve the animation start in canonical web semantic and layout state
   - Artifact capture: after_step
- Render the animation start through canonical Draw IR and Engine2D
   - Artifact capture: after_step


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Resolve the animation start in canonical web semantic and layout state")
step("Render the animation start through canonical Draw IR and Engine2D")
expect(_animation_frame_fingerprint(
    _animation_html(), 0, 0xFFDC2626u32
)).to_equal(
    "preserve,1000,forwards|4,4|html_ast|box:0,0,4,4|" +
    "preserve,1000ms,4292617766|16|0|16"
)
```

</details>

#### should preserve interpolated geometry and color at the midpoint

- Resolve the animation midpoint in canonical web semantic and layout state
   - Artifact capture: after_step
- Render the animation midpoint through canonical Draw IR and Engine2D
   - Artifact capture: after_step


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Resolve the animation midpoint in canonical web semantic and layout state")
step("Render the animation midpoint through canonical Draw IR and Engine2D")
expect(_animation_frame_fingerprint(
    _animation_html(), 500, 0xFF804488u32
)).to_equal(
    "preserve,1000,forwards|4,4|html_ast|box:0,0,8,4|" +
    "preserve,1000ms,4286596232|516|0|32"
)
```

</details>

#### should preserve the filled end frame without scheduling another frame

- Resolve the animation end in canonical web semantic and layout state
   - Artifact capture: after_step
- Render the animation end through canonical Draw IR and Engine2D
   - Artifact capture: after_step


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Resolve the animation end in canonical web semantic and layout state")
step("Render the animation end through canonical Draw IR and Engine2D")
expect(_animation_frame_fingerprint(
    _animation_html(), 1000, 0xFF2563EBu32
)).to_equal(
    "preserve,1000,forwards|4,4|html_ast|box:0,0,12,4|" +
    "preserve,1000ms,4280640491|-1|0|48"
)
```

</details>

#### should seek a fractional negative delay before consecutive frames

- Resolve the signed fractional delay in canonical web semantic state
   - HTML capture: after_step
- Render consecutive sought frames through canonical Draw IR and Engine2D
   - Artifact capture: after_step

<details>
<summary>Executable SSpec</summary>

Runnable source folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = _negative_delay_animation_html("-0.5s")
step("Resolve the signed fractional delay in canonical web semantic state")
expect(simple_web_layout_debug_style_by_id(
    html, "box", "animation_delay_ms"
)).to_equal("-500")
expect(simple_web_layout_debug_style_by_id(
    _negative_delay_animation_html("-1.5s"),
    "box", "animation_delay_ms"
)).to_equal("-1500")
expect(simple_web_layout_debug_style_by_id(
    _negative_delay_animation_html("-500ms"),
    "box", "animation_delay_ms"
)).to_equal("-500")
expect(simple_web_layout_debug_style_by_id(
    _negative_delay_animation_html("-0.5ms"),
    "box", "animation_delay_ms"
)).to_equal("-1")

step("Render consecutive sought frames through canonical Draw IR and Engine2D")
val midpoint = _animation_frame_fingerprint(
    html, 0, 0xFF804488u32
)
val next = _animation_frame_fingerprint(
    html, 16, 0xFF7D458Bu32
)
expect(midpoint).to_equal(
    "preserve,1000,forwards|4,4|html_ast|box:0,0,8,4|" +
    "preserve,1000ms,4286596232|16|0|32"
)
expect(next).to_equal(
    "preserve,1000,forwards|4,4|html_ast|box:0,0,8,4|" +
    "preserve,1000ms,4286399883|32|0|32"
)
expect(next == midpoint).to_equal(false)
```

</details>

#### should reuse the completed animation Draw IR after its final frame

- Render the finite CSS animation through its scheduled final frame
   - Protocol capture: completed frame schedules no later animation frame
- Advance past the completed frame without scheduling an identical repaint
   - Protocol capture: retained Draw IR, paint count, and checksum stay stable

<details>
<summary>Executable SSpec</summary>

Runnable source folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Render the finite CSS animation through its scheduled final frame")
var worker = HostedBrowserRendererWorkerSession.create(WIDTH, HEIGHT)
expect(worker.handle(BrowserRendererMessage(
    kind: "init", generation: 7, request_id: 2,
    payload: _animation_html()
)).ok).to_be(true)
val completed = worker.handle(BrowserRendererMessage(
    kind: "advance", generation: 7, request_id: 3, payload: "1000"
))
expect(completed.ok).to_be(true)
val completed_message = browser_renderer_decoder_feed(
    browser_renderer_decoder_new(7), completed.wire
)
expect(completed_message.status).to_equal("message")
val completed_frame = browser_renderer_frame_decode(
    completed_message.message, WIDTH, HEIGHT
)
expect(completed_frame.ok).to_be(true)
expect(completed_frame.next_animation_ms).to_equal(-1)
expect(
    completed_frame.composition.batches[0].commands.len()
).to_be_greater_than(0)
val completed_paints = worker.render_session.counters.paint_count
val completed_checksum = worker.render_session.composition_checksum()

step("Advance past the completed frame without scheduling an identical repaint")
val later = worker.handle(BrowserRendererMessage(
    kind: "advance", generation: 7, request_id: 4, payload: "1016"
))
expect(later.ok).to_be(true)
val later_message = browser_renderer_decoder_feed(
    browser_renderer_decoder_new(7), later.wire
)
expect(later_message.status).to_equal("message")
val later_frame = browser_renderer_frame_decode(
    later_message.message, WIDTH, HEIGHT
)
expect(later_frame.ok).to_be(true)
expect(later_frame.next_animation_ms).to_equal(-1)
expect(
    later_frame.composition.batches[0].commands.len()
).to_be_greater_than(0)
expect(worker.render_session.counters.paint_count).to_equal(
    completed_paints
)
expect(worker.render_session.composition_checksum()).to_equal(
    completed_checksum
)
worker.close()
```

</details>

<details>
<summary>Advanced: should retain linear length interpolation at the midpoint</summary>

#### should retain linear length interpolation at the midpoint

- Check the bounded animation interpolation primitives
- interpolate length


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Check the bounded animation interpolation primitives")
expect(approx(
    interpolate_length(0.0, 100.0, 0.5), 50.0
)).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: should retain linear timing identity</summary>

#### should retain linear timing identity

- Check the bounded animation interpolation primitives
- ease value


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Check the bounded animation interpolation primitives")
expect(approx(
    ease_value(0.5, TimingFunction.Linear), 0.5
)).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: should retain the ease-in slow start</summary>

#### should retain the ease-in slow start

- Check the bounded animation interpolation primitives


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Check the bounded animation interpolation primitives")
expect(ease_value(
    0.5, TimingFunction.EaseIn
) < 0.5).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: should interpolate number values at the midpoint</summary>

#### should interpolate number values at the midpoint

- Check the bounded animation interpolation primitives
   - Expected: _interp_number_half() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Check the bounded animation interpolation primitives")
expect(_interp_number_half()).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: should parse the bounded keyframes block</summary>

#### should parse the bounded keyframes block

- Parse supported CSS keyframes


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Parse supported CSS keyframes")
val registry = extract_keyframes(
    "@keyframes fade { from { opacity: 0; } to { opacity: 1; } }"
)
expect(registry.entries.len()).to_be_greater_than(0)
```

</details>


</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 10 |
| Active scenarios | 10 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

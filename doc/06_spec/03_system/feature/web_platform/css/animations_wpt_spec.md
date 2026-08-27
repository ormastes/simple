# CSS Animation Frame Preservation

> Proves fractional last-valid declaration selection and saturating i64 clock

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 13 | 13 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# CSS Animation Frame Preservation

Proves fractional last-valid declaration selection and saturating i64 clock

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/feature/web_platform/css/animations_wpt_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Proves fractional last-valid declaration selection and saturating i64 clock
boundaries, plus the supported keyframe subset at its start, negative-delay
seek, midpoint, and filled end through web semantics, layout, canonical Draw
IR, and exact expected-color Engine2D coverage/count. Web Animations
compositing and unsupported properties remain outside this bounded profile.

## Scenarios

### REQ-WEB-BROWSER-003/004/006: CSS animation frames

#### should apply bounded CSS timing functions to canonical Draw IR

**Scenario capture:** artifact after_step


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-WEB-BROWSER-003/004/006
```

</details>

#### should synthesize implicit underlying endpoints for one midpoint keyframe

- should synthesize implicit underlying endpoints for one midpoint keyframe
   - Artifact capture: after_step
- Open a one-midpoint keyframe animation over a red underlying style
   - Artifact capture: after_step
- Render the implicit start endpoint through canonical Draw IR and Engine2D
   - Artifact capture: after_step
- Advance to the authored midpoint without changing scheduler cadence
   - Artifact capture: after_step
- Fill and reuse the implicit end endpoint after completion
   - Artifact capture: after_step


<details>
<summary>Executable SSpec</summary>

Runnable source: 41 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should synthesize implicit underlying endpoints for one midpoint keyframe")
val html = _single_midpoint_keyframe_html()
step("Open a one-midpoint keyframe animation over a red underlying style")
expect(simple_web_layout_debug_style_by_id(
    html, "box", "background_color"
)).to_equal("4293870660")

step("Render the implicit start endpoint through canonical Draw IR and Engine2D")
expect(_single_midpoint_animation_command_color(
    html, 0
)).to_equal(0xFFEF4444u32)
expect(_animation_frame_fingerprint(
    html, 0, 0xFFEF4444u32
)).to_equal(
    "peak,1000,forwards|8,8|html_ast|box:0,0,8,8|" +
    "peak,1000ms,4293870660|16|0|64"
)

step("Advance to the authored midpoint without changing scheduler cadence")
expect(_single_midpoint_animation_command_color(
    html, 500
)).to_equal(0xFF2563EBu32)
expect(_animation_frame_fingerprint(
    html, 500, 0xFF2563EBu32
)).to_equal(
    "peak,1000,forwards|8,8|html_ast|box:0,0,32,8|" +
    "peak,1000ms,4280640491|516|0|256"
)

step("Fill and reuse the implicit end endpoint after completion")
expect(_single_midpoint_animation_command_color(
    html, 1000
)).to_equal(0xFFEF4444u32)
expect(_animation_frame_fingerprint(
    html, 1000, 0xFFEF4444u32
)).to_equal(
    "peak,1000,forwards|8,8|html_ast|box:0,0,8,8|" +
    "peak,1000ms,4293870660|-1|0|64"
)
_expect_completed_animation_reuse(html, 0xFFEF4444u32)
```

</details>

#### should preserve the fractional winner across clock bounds

- should preserve the fractional winner across clock bounds
   - Artifact capture: after_step
- Parse the last valid animation declaration
   - Artifact capture: after_step
- Advance across the integer clock boundary
   - Artifact capture: after_step
- Lower the bounded animation frame
   - Artifact capture: after_step
- Reject invalid tails without erasing the winner
   - Artifact capture: after_step


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should preserve the fractional winner across clock bounds")
val html = setup_fractional_animation_boundary_fixture()
step("Parse the last valid animation declaration")
check_last_valid_animation_winner(html)
step("Advance across the integer clock boundary")
check_saturating_animation_clock(html)
step("Lower the bounded animation frame")
check_bounded_animation_frame(html)
step("Reject invalid tails without erasing the winner")
check_last_valid_animation_winner(html)
```

</details>

#### should preserve the animation feature at its exact start frame

- should preserve the animation feature at its exact start frame
   - Artifact capture: after_step
- Resolve the animation start in canonical web semantic and layout state
   - Artifact capture: after_step
- Render the animation start through canonical Draw IR and Engine2D
   - Artifact capture: after_step


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should preserve the animation feature at its exact start frame")
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

- should preserve interpolated geometry and color at the midpoint
   - Artifact capture: after_step
- Resolve the animation midpoint in canonical web semantic and layout state
   - Artifact capture: after_step
- Render the animation midpoint through canonical Draw IR and Engine2D
   - Artifact capture: after_step


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should preserve interpolated geometry and color at the midpoint")
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

- should preserve the filled end frame without scheduling another frame
   - Artifact capture: after_step
- Resolve the animation end in canonical web semantic and layout state
   - Artifact capture: after_step
- Render the animation end through canonical Draw IR and Engine2D
   - Artifact capture: after_step


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should preserve the filled end frame without scheduling another frame")
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

- should seek a fractional negative delay before consecutive frames
   - Artifact capture: after_step
- Resolve the signed fractional delay in canonical web semantic state
   - Artifact capture: after_step
- Render consecutive sought frames through canonical Draw IR and Engine2D
   - Artifact capture: after_step
   - Evidence: artifact verified by 1 expected check
   - Expected: next == midpoint is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 36 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should seek a fractional negative delay before consecutive frames")
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

- should reuse the completed animation Draw IR after its final frame
   - Protocol capture: after_step
- Render the finite CSS animation through its scheduled final frame
   - Protocol capture: after_step
   - Evidence: protocol response verified by 2 expected checks
   - Expected: completed_message.status equals `message`
   - Expected: completed_frame.next_animation_ms equals `-1`
- Advance past the completed frame without scheduling an identical repaint
   - Protocol capture: after_step
   - Evidence: protocol response verified by 2 expected checks
   - Expected: later_message.status equals `message`
   - Expected: later_frame.next_animation_ms equals `-1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 51 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should reuse the completed animation Draw IR after its final frame")
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

- should retain linear length interpolation at the midpoint
- Check the bounded animation interpolation primitives


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should retain linear length interpolation at the midpoint")
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

- should retain linear timing identity
- Check the bounded animation interpolation primitives


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should retain linear timing identity")
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

- should retain the ease-in slow start
- Check the bounded animation interpolation primitives


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should retain the ease-in slow start")
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

- should interpolate number values at the midpoint
- Check the bounded animation interpolation primitives
   - Expected: _interp_number_half() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should interpolate number values at the midpoint")
step("Check the bounded animation interpolation primitives")
expect(_interp_number_half()).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: should parse the bounded keyframes block</summary>

#### should parse the bounded keyframes block

- should parse the bounded keyframes block
- Parse supported CSS keyframes


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should parse the bounded keyframes block")
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
| Total scenarios | 13 |
| Active scenarios | 13 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
- `REQ-WEB-BROWSER-003/004/006`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `001c879c6b1f27b7f43a0ffb1f820c28e87a025b0bd03f44f59c85d04ca8ab3a`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `001c879c6b1f27b7f43a0ffb1f820c28e87a025b0bd03f44f59c85d04ca8ab3a`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `001c879c6b1f27b7f43a0ffb1f820c28e87a025b0bd03f44f59c85d04ca8ab3a`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **82/100**; effective score: **82/100**; blockers: **0**.

SSpec documentization score: 82/100
source: test/03_system/feature/web_platform/css/animations_wpt_spec.spl
mirror: doc/06_spec/03_system/feature/web_platform/css/animations_wpt_spec.md (current)
findings: 13 blockers: 0
  narrative=100 structure=60 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/feature/web_platform/css/animations_wpt_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/feature/web_platform/css/animations_wpt_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/feature/web_platform/css/animations_wpt_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/feature/web_platform/css/animations_wpt_spec.spl:609:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'should apply bounded CSS timing functions to canonical Draw IR' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/03_system/feature/web_platform/css/animations_wpt_spec.spl:609:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should apply bounded CSS timing functions to canonical Draw IR' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/feature/web_platform/css/animations_wpt_spec.spl:675:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should synthesize implicit underlying endpoints for one midpoint keyframe' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/feature/web_platform/css/animations_wpt_spec.spl:675:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should synthesize implicit underlying endpoints for one midpoint keyframe' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/web_platform/css/animations_wpt_spec.spl:721:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should preserve the fractional winner across clock bounds' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/feature/web_platform/css/animations_wpt_spec.spl:721:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should preserve the fractional winner across clock bounds' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/web_platform/css/animations_wpt_spec.spl:737:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should preserve the animation feature at its exact start frame' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/feature/web_platform/css/animations_wpt_spec.spl:737:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should preserve the animation feature at its exact start frame' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/web_platform/css/animations_wpt_spec.spl:752:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should preserve interpolated geometry and color at the midpoint' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/feature/web_platform/css/animations_wpt_spec.spl:767:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should preserve the filled end frame without scheduling another frame' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->

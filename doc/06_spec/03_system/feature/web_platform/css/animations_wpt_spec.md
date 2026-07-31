# CSS Animation Frame Preservation

> Proves implicit endpoints, fractional winners, bounded clocks, signed-delay seek, and filled-end frames

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 13 | 13 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# CSS Animation Frame Preservation

Proves implicit underlying endpoints, fractional winners, bounded clocks,
signed-delay seek, midpoint, and filled-end animation frames

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/feature/web_platform/css/animations_wpt_spec.spl` |
| Updated | 2026-07-30 |
| Generator | Manual mirror; qualified docgen pending |

Proves fractional last-valid declaration selection and saturating i64 clock
boundaries, plus the supported keyframe subset at its start, negative-delay
seek, midpoint, and filled end through web semantics, layout, canonical Draw
IR, and exact expected-color Engine2D coverage/count. Web Animations
compositing and unsupported properties remain outside this bounded profile.

## Scenarios

### REQ-WEB-BROWSER-003/004/006: CSS animation frames

#### should apply bounded CSS timing functions to canonical Draw IR

- Resolve valid timing functions without rewriting them to ease
  - The depth-aware tokenizer keeps commas inside a single functional value
- Sample cubic Bézier identity timing into canonical Draw IR
  - At 500 ms the exact opaque interpolated color is `0xFF804488`
- Sample step timing at exact jump boundaries
  - The `before` flag is set only for before+forwards or after+backwards
  - Active `jump-start` and `jump-end` frames use exact quarter-step colors
  - Reverse `jump-end` backwards fill is exact blue progress `1.0`
  - Reverse `jump-start` forwards fill is exact red progress `0.0`
  - Alternate and alternate-reverse controls prove both boundary directions
- Ignore malformed nonfinite and out-of-range timing declarations
  - Later invalid animation and transition declarations do not erase `linear`
  - List-valued and keyframe-local timing remain intentionally unsupported

<details>
<summary>Executable SSpec</summary>

```simple
val html = _timing_function_html()
step("Resolve valid timing functions without rewriting them to ease")
expect(simple_web_layout_debug_style_by_id(
    html, "cubic", "animation_timing_function"
)).to_equal("cubic-bezier(0, 0, 1, 1)")

step("Sample cubic Bézier identity timing into canonical Draw IR")
expect(_timing_command_color(html, "cubic", 500)).to_equal(0xFF804488u32)

step("Sample step timing at exact jump boundaries")
expect(_timing_command_color(html, "jump-start", 0)).to_equal(0xFFDC2626u32)
expect(_timing_command_color(html, "jump-start", 100)).to_equal(0xFFAE3557u32)
expect(_timing_command_color(html, "jump-end", 249)).to_equal(0xFFDC2626u32)
expect(_timing_command_color(html, "jump-end", 250)).to_equal(0xFFAE3557u32)
expect(_timing_command_color(html, "reverse-before", 0)).to_equal(0xFF2563EBu32)
expect(_timing_command_color(html, "reverse-after", 1000)).to_equal(0xFFDC2626u32)
expect(_timing_command_color(html, "alternate-before", 0)).to_equal(0xFFDC2626u32)
expect(_timing_command_color(html, "alternate-after", 2000)).to_equal(0xFFDC2626u32)
expect(_timing_command_color(html, "alternate-reverse-before", 0)).to_equal(0xFF2563EBu32)
expect(_timing_command_color(html, "alternate-reverse-after", 2000)).to_equal(0xFF2563EBu32)

step("Ignore malformed nonfinite and out-of-range timing declarations")
for id in ["bad-x", "bad-finite", "bad-zero", "bad-none", "bad-list"]:
    expect(simple_web_layout_debug_style_by_id(
        html, id, "animation_timing_function"
    )).to_equal("linear")
    expect(_timing_command_color(html, id, 500)).to_equal(0xFF804488u32)
expect(simple_web_layout_debug_style_by_id(
    html, "transition", "transition_timing_function"
)).to_equal("linear")
expect(simple_web_layout_debug_style_by_id(
    html, "transition-shorthand", "transition_timing_function"
)).to_equal("steps(4,jump-end)")
```

</details>

#### should synthesize implicit underlying endpoints for one midpoint keyframe

- Open a one-midpoint keyframe animation over a red underlying style
  - Fixture: `_single_midpoint_keyframe_html`
  - Unrelated opacity declarations own 0% and 100%; the midpoint independently
    authors background color and width
  - The computed underlying background is exact opaque red `#ef4444`
- Render the implicit start endpoint through canonical Draw IR and Engine2D
  - Checker: `_single_midpoint_animation_command_color`
  - Exact Draw IR: one 8×8 red box at (0,0)
  - Exact Engine2D: 64 red pixels and zero skipped commands
- Advance to the authored midpoint without changing scheduler cadence
  - Exact Draw IR: authored `width:auto` fills the 32×8 row in `#2563eb`
  - Exact Engine2D: 256 blue pixels and zero skipped commands
  - The next scheduled frame remains 516 ms
- Fill and reuse the implicit end endpoint after completion
  - Checker: `_expect_completed_animation_reuse`
  - Exact Draw IR and Engine2D return to the underlying red endpoint
  - The terminal frame schedules no successor
  - Advancing to 1016 ms preserves paint count and composition checksum

<details>
<summary>Executable SSpec</summary>

Runnable source folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

- Parse the last valid animation declaration
  - Fixture: `setup_fractional_animation_boundary_fixture`
  - Checker: `check_last_valid_animation_winner`
  - Custom names `news`, `paused-banner`, `reverse-card`, `forwards-news`, and
    `linear-news` remain names; exact tokens alone select animation keywords
  - A later valid shorthand resets every earlier longhand to its parsed or
    initial value
  - Zero iterations retain `both` fill at the first frame; infinite iterations
    remain scheduled and reach the midpoint
- Advance across the integer clock boundary
  - Checker: `check_saturating_animation_clock`
  - Reconcile subtraction clamps at i64-min/max
  - Positive and negative schedule addition clamps at i64-max/min
- Lower the bounded animation frame
  - Checker: `check_bounded_animation_frame`
  - Exact Draw IR: one 8×8 box at (0,0), red at i64-min and fractional midpoint at i64-max
  - Exact Engine2D: 64 matching pixels per frame, zero skipped commands
  - The actual pause and resume reconciliation pair both lower to the exact
    quarter-frame color and 64 matching pixels
- Reject invalid tails without erasing the winner
  - Checker: `check_last_valid_animation_winner`
  - Invalid shorthand and longhand `-1` tails retain the earlier `.5` winner

<details>
<summary>Executable SSpec</summary>

Runnable source folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Complete fixture and checker implementations</summary>

```simple
use std.spec.*

use std.gc_async_mut.gpu.browser_engine.style.animation.{
    BrowserCssAnimationInstance
}
use std.gc_async_mut.gpu.browser_engine.simple_web_html_layout_renderer.{
    simple_web_layout_debug_style_by_id,
    simple_web_layout_render_html_draw_ir_result_at_time,
    simple_web_layout_render_html_draw_ir_result_at_time_with_animations,
    simple_web_layout_reconcile_animation_instances,
    simple_web_layout_animation_instances_next_ms
}
use os.compositor.compositor_engine2d.{Engine2dCompositorBackend}

val WIDTH: i32 = 32
val HEIGHT: i32 = 24

fn _animation_color_count(pixels: [u32], color: u32) -> i32:
    var count = 0
    for pixel in pixels:
        if pixel == color:
            count = count + 1
    count

fn setup_fractional_animation_boundary_fixture() -> text:
    (
        "<style>html,body{margin:0}@keyframes boundary{" +
        "from{background-color:#dc2626}to{background-color:#2563eb}}" +
        "#box{width:8px;height:8px;background-color:#16a34a;" +
        "animation:boundary 1000ms linear 2 both;" +
        "animation:boundary 1000ms linear -1;" +
        "animation-iteration-count:.5;" +
        "animation-iteration-count:-1}</style><div id='box'></div>"
    )

fn check_last_valid_animation_winner(html: text):
    expect(simple_web_layout_debug_style_by_id(
        html, "box", "animation_name"
    )).to_equal("boundary")
    expect(simple_web_layout_debug_style_by_id(
        html, "box", "animation_duration_ms"
    )).to_equal("1000")
    expect(simple_web_layout_debug_style_by_id(
        html, "box", "animation_iteration_count"
    )).to_equal(".5")
    expect(simple_web_layout_debug_style_by_id(
        html, "box", "animation_fill_mode"
    )).to_equal("both")
    val instances = simple_web_layout_reconcile_animation_instances(
        html, WIDTH, 0, 0, false, []
    )
    expect(instances.len()).to_equal(1)
    expect(instances[0].iteration_count).to_equal(0.5)
    val names_html = (
        "<style>#paused{animation:paused-banner 1000ms}" +
        "#reverse{animation:reverse-card 1000ms}" +
        "#forwards{animation:forwards-news 1000ms}" +
        "#linear{animation:linear-news 1000ms}" +
        "#news{animation:news 1000ms}" +
        "#reset{animation-name:old;animation-duration:2000ms;" +
        "animation-delay:200ms;animation-timing-function:ease-in;" +
        "animation-iteration-count:3;animation-direction:reverse;" +
        "animation-fill-mode:forwards;animation-play-state:paused;" +
        "animation:news 1000ms linear .5 both running}</style>" +
        "<div id='paused'></div><div id='reverse'></div>" +
        "<div id='forwards'></div><div id='linear'></div>" +
        "<div id='news'></div><div id='reset'></div>"
    )
    expect(simple_web_layout_debug_style_by_id(
        names_html, "paused", "animation_name"
    )).to_equal("paused-banner")
    expect(simple_web_layout_debug_style_by_id(
        names_html, "paused", "animation_play_state"
    )).to_equal("running")
    expect(simple_web_layout_debug_style_by_id(
        names_html, "reverse", "animation_direction"
    )).to_equal("normal")
    expect(simple_web_layout_debug_style_by_id(
        names_html, "forwards", "animation_fill_mode"
    )).to_equal("none")
    expect(simple_web_layout_debug_style_by_id(
        names_html, "linear", "animation_timing_function"
    )).to_equal("ease")
    expect(simple_web_layout_debug_style_by_id(
        names_html, "news", "animation_name"
    )).to_equal("news")
    expect(simple_web_layout_debug_style_by_id(
        names_html, "news", "animation_duration_ms"
    )).to_equal("1000")
    expect(simple_web_layout_debug_style_by_id(
        names_html, "reset", "animation_name"
    )).to_equal("news")
    expect(simple_web_layout_debug_style_by_id(
        names_html, "reset", "animation_duration_ms"
    )).to_equal("1000")
    expect(simple_web_layout_debug_style_by_id(
        names_html, "reset", "animation_delay_ms"
    )).to_equal("0")
    expect(simple_web_layout_debug_style_by_id(
        names_html, "reset", "animation_timing_function"
    )).to_equal("linear")
    expect(simple_web_layout_debug_style_by_id(
        names_html, "reset", "animation_iteration_count"
    )).to_equal(".5")
    expect(simple_web_layout_debug_style_by_id(
        names_html, "reset", "animation_direction"
    )).to_equal("normal")
    expect(simple_web_layout_debug_style_by_id(
        names_html, "reset", "animation_fill_mode"
    )).to_equal("both")
    expect(simple_web_layout_debug_style_by_id(
        names_html, "reset", "animation_play_state"
    )).to_equal("running")
    val edge_html = (
        "<style>@keyframes edge{from{background-color:#dc2626}" +
        "to{background-color:#2563eb}}" +
        "#zero{width:8px;height:8px;animation:edge 1000ms linear 0 both}" +
        "#forever{width:8px;height:8px;" +
        "animation:edge 1000ms linear infinite}</style>" +
        "<div id='zero'></div><div id='forever'></div>"
    )
    expect(simple_web_layout_debug_style_by_id(
        edge_html, "zero", "animation_iteration_count"
    )).to_equal("0")
    expect(simple_web_layout_debug_style_by_id(
        edge_html, "zero", "animation_fill_mode"
    )).to_equal("both")
    val edge_instances = simple_web_layout_reconcile_animation_instances(
        edge_html, WIDTH, 0, 0, false, []
    )
    expect(edge_instances.len()).to_equal(2)
    expect(edge_instances[0].iteration_count).to_equal(0.0)
    expect(edge_instances[1].iteration_count).to_equal(-1.0)
    expect(simple_web_layout_animation_instances_next_ms(
        [edge_instances[0]], 0
    )).to_equal(-1)
    expect(simple_web_layout_animation_instances_next_ms(
        [edge_instances[1]], 0
    )).to_equal(16)
    val edge_frame = simple_web_layout_render_html_draw_ir_result_at_time(
        edge_html, WIDTH, HEIGHT, 500
    )
    var zero_color = 0u32
    var infinite_color = 0u32
    for command in edge_frame.composition.batches[0].commands:
        if command.component_id == "zero":
            zero_color = command.color
        elif command.component_id == "forever":
            infinite_color = command.color
    expect(zero_color).to_equal(0xFFDC2626u32)
    expect(infinite_color).to_equal(0xFF804488u32)

fn check_saturating_animation_clock(html: text):
    val baseline = simple_web_layout_reconcile_animation_instances(
        html, WIDTH, 0, 0, false, []
    )
    expect(baseline.len()).to_equal(1)
    val min_time: i64 = -9223372036854775808
    val max_time: i64 = 9223372036854775807
    val running_at_min = BrowserCssAnimationInstance(
        target_key: baseline[0].target_key,
        signature: baseline[0].signature,
        start_time_ms: min_time,
        paused: false,
        paused_elapsed_ms: 0,
        duration_ms: 1000,
        delay_ms: 0,
        iteration_count: 0.5
    )
    val paused_html = html.replace(
        "animation-iteration-count:-1",
        "animation-iteration-count:-1;animation-play-state:paused"
    )
    val paused = simple_web_layout_reconcile_animation_instances(
        paused_html, WIDTH, max_time, max_time, false, [running_at_min]
    )
    expect(paused.len()).to_equal(1)
    expect(paused[0].paused_elapsed_ms).to_equal(max_time)
    val resumed = simple_web_layout_reconcile_animation_instances(
        html, WIDTH, min_time, min_time, false, [BrowserCssAnimationInstance(
            target_key: paused[0].target_key,
            signature: baseline[0].signature,
            start_time_ms: paused[0].start_time_ms,
            paused: true,
            paused_elapsed_ms: max_time,
            duration_ms: 1000,
            delay_ms: 0,
            iteration_count: 0.5
        )]
    )
    expect(resumed.len()).to_equal(1)
    expect(resumed[0].start_time_ms).to_equal(min_time)
    val positive_add = BrowserCssAnimationInstance(
        target_key: "positive-add",
        signature: "positive-add",
        start_time_ms: max_time - 8,
        paused: false,
        paused_elapsed_ms: 0,
        duration_ms: max_time,
        delay_ms: 16,
        iteration_count: 2.0
    )
    expect(simple_web_layout_animation_instances_next_ms(
        [positive_add], max_time - 10
    )).to_equal(max_time)
    expect(simple_web_layout_animation_instances_next_ms(
        [positive_add], max_time
    )).to_equal(-1)
    val negative_add = BrowserCssAnimationInstance(
        target_key: "negative-add",
        signature: "negative-add",
        start_time_ms: min_time + 8,
        paused: false,
        paused_elapsed_ms: 0,
        duration_ms: 100,
        delay_ms: -16,
        iteration_count: 1.0
    )
    expect(simple_web_layout_animation_instances_next_ms(
        [negative_add], min_time
    )).to_equal(min_time + 16)

fn check_bounded_animation_frame(html: text):
    val baseline = simple_web_layout_reconcile_animation_instances(
        html, WIDTH, 0, 0, false, []
    )
    expect(baseline.len()).to_equal(1)
    val min_time: i64 = -9223372036854775808
    val max_time: i64 = 9223372036854775807
    val future = BrowserCssAnimationInstance(
        target_key: baseline[0].target_key,
        signature: baseline[0].signature,
        start_time_ms: max_time,
        paused: false,
        paused_elapsed_ms: 0,
        duration_ms: 1000,
        delay_ms: 0,
        iteration_count: 0.5
    )
    val past = BrowserCssAnimationInstance(
        target_key: baseline[0].target_key,
        signature: baseline[0].signature,
        start_time_ms: min_time,
        paused: false,
        paused_elapsed_ms: 0,
        duration_ms: 1000,
        delay_ms: 0,
        iteration_count: 0.5
    )
    val first = (
        simple_web_layout_render_html_draw_ir_result_at_time_with_animations(
            html, WIDTH, HEIGHT, min_time, [future]
        )
    )
    val last = (
        simple_web_layout_render_html_draw_ir_result_at_time_with_animations(
            html, WIDTH, HEIGHT, max_time, [past]
        )
    )
    val paused_html = html.replace(
        "animation-iteration-count:-1",
        "animation-iteration-count:-1;animation-play-state:paused"
    )
    val paused_pair = simple_web_layout_reconcile_animation_instances(
        paused_html, WIDTH, 250, 250, false, baseline
    )
    expect(paused_pair.len()).to_equal(1)
    expect(paused_pair[0].paused).to_equal(true)
    expect(paused_pair[0].paused_elapsed_ms).to_equal(250)
    val resumed_pair = simple_web_layout_reconcile_animation_instances(
        html, WIDTH, 750, 750, false, paused_pair
    )
    expect(resumed_pair.len()).to_equal(1)
    expect(resumed_pair[0].paused).to_equal(false)
    expect(resumed_pair[0].start_time_ms).to_equal(500)
    val paused_frame = (
        simple_web_layout_render_html_draw_ir_result_at_time_with_animations(
            html, WIDTH, HEIGHT, 750, paused_pair
        )
    )
    val resumed_frame = (
        simple_web_layout_render_html_draw_ir_result_at_time_with_animations(
            html, WIDTH, HEIGHT, 750, resumed_pair
        )
    )
    var first_commands = 0
    var last_commands = 0
    var paused_commands = 0
    var resumed_commands = 0
    for command in first.composition.batches[0].commands:
        if command.component_id == "box":
            expect(command.x).to_equal(0)
            expect(command.y).to_equal(0)
            expect(command.width).to_equal(8)
            expect(command.height).to_equal(8)
            expect(command.color).to_equal(0xFFDC2626u32)
            first_commands = first_commands + 1
    for command in last.composition.batches[0].commands:
        if command.component_id == "box":
            expect(command.x).to_equal(0)
            expect(command.y).to_equal(0)
            expect(command.width).to_equal(8)
            expect(command.height).to_equal(8)
            expect(command.color).to_equal(0xFF804488u32)
            last_commands = last_commands + 1
    for command in paused_frame.composition.batches[0].commands:
        if command.component_id == "box":
            expect(command.color).to_equal(0xFFAE3557u32)
            paused_commands = paused_commands + 1
    for command in resumed_frame.composition.batches[0].commands:
        if command.component_id == "box":
            expect(command.color).to_equal(0xFFAE3557u32)
            resumed_commands = resumed_commands + 1
    expect(first_commands).to_equal(1)
    expect(last_commands).to_equal(1)
    expect(paused_commands).to_equal(1)
    expect(resumed_commands).to_equal(1)
    val raster = Engine2dCompositorBackend.create_named(
        WIDTH, HEIGHT, "software"
    )
    val first_pixels = raster.render_draw_ir_composition(
        first.composition, []
    )
    val last_pixels = raster.render_draw_ir_composition(
        last.composition, []
    )
    val paused_pixels = raster.render_draw_ir_composition(
        paused_frame.composition, []
    )
    val resumed_pixels = raster.render_draw_ir_composition(
        resumed_frame.composition, []
    )
    raster.shutdown()
    expect(first_pixels.skipped_command_count).to_equal(0)
    expect(last_pixels.skipped_command_count).to_equal(0)
    expect(paused_pixels.skipped_command_count).to_equal(0)
    expect(resumed_pixels.skipped_command_count).to_equal(0)
    expect(_animation_color_count(
        first_pixels.pixels, 0xFFDC2626u32
    )).to_equal(64)
    expect(_animation_color_count(
        last_pixels.pixels, 0xFF804488u32
    )).to_equal(64)
    expect(_animation_color_count(
        paused_pixels.pixels, 0xFFAE3557u32
    )).to_equal(64)
    expect(_animation_color_count(
        resumed_pixels.pixels, 0xFFAE3557u32
    )).to_equal(64)

```

</details>

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
| Total scenarios | 13 |
| Active scenarios | 13 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

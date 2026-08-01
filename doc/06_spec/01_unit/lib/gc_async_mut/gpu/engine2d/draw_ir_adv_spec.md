# Engine2D Draw IR Advanced Executor Specification

> This unit spec covers the Simple2D-facing Draw IR executor. It proves Draw IR batches and compositions choose the CPU fallback when GPU execution is unavailable, render supported rectangle commands into the Engine2D pixel buffer, skip unsupported future commands, and expose the same Draw IR batch through SGTTI before raster so semantic assertions and pixel readback are paired.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 33 | 33 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Engine2D Draw IR Advanced Executor Specification

This unit spec covers the Simple2D-facing Draw IR executor. It proves Draw IR batches and compositions choose the CPU fallback when GPU execution is unavailable, render supported rectangle commands into the Engine2D pixel buffer, skip unsupported future commands, and expose the same Draw IR batch through SGTTI before raster so semantic assertions and pixel readback are paired.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Requirements | N/A |
| Plan | doc/03_plan/ui/ui_test/ui_test_sgtti_plan.md |
| Design | doc/04_architecture/ui/ui_test_architecture.md |
| Research | doc/01_research/ui/draw_ir/draw_io_sdn_draw_ir.md |
| Source | `test/01_unit/lib/gc_async_mut/gpu/engine2d/draw_ir_adv_spec.spl` |
| Updated | 2026-07-31 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

This unit spec covers the Simple2D-facing Draw IR executor. It proves Draw IR
batches and compositions choose the CPU fallback when GPU execution is
unavailable, render supported rectangle commands into the Engine2D pixel buffer,
skip unsupported future commands, and expose the same Draw IR batch through
SGTTI before raster so semantic assertions and pixel readback are paired.

## Evidence Model

The first scenario is the SGTTI Phase 5 gate: it builds a Draw IR batch, asserts
the pre-raster semantic node with `SgttiTestDriver`, then renders the same batch
through Engine2D and checks pixel output.

**Requirements:** N/A

This is implementation evidence for the active SGTTI and Draw IR plans rather
than a numbered product requirement.

**Plan:** doc/03_plan/ui/ui_test/ui_test_sgtti_plan.md

**Design:** doc/04_architecture/ui/ui_test_architecture.md

**Research:** doc/01_research/ui/draw_ir/draw_io_sdn_draw_ir.md

## Syntax

The spec uses normal `std.spec` scenarios. Assertions stay on the canonical
SPipe matcher set; SGTTI is used as a helper inside an `it` block, not as a
replacement test framework.

## Scenarios

### Engine2D advanced Draw IR executor

#### preserves repeated opaque and translucent image blending with cached opacity

- Construct one opaque, one translucent, and two malformed resolved images.
  - Expected: only the exact-size all-alpha-255 image is cached as opaque.
- Render duplicate opaque image commands through the shared path.
  - Expected: both commands render with the same pixels as direct scaled draws.
- Render duplicate translucent image commands through blending.
  - Expected: both commands render with the same pixels as direct src-over draws.
- Keep translucent first-frame images outside fresh-device admission.
  - Expected: preflight rejects the translucent full-target initializer.

<details>
<summary>Executable SSpec</summary>

Runnable source: 93 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Construct one opaque and one translucent resolved image")
val opaque = engine2d_resolved_draw_ir_image(
    "image://opaque-cache", 2, 1, [RED, GREEN])
val translucent = engine2d_resolved_draw_ir_image(
    "image://translucent-cache", 2, 1, [HALF_RED, GREEN])
val empty = engine2d_resolved_draw_ir_image(
    "image://empty-cache", 0, 0, [])
val truncated = engine2d_resolved_draw_ir_image(
    "image://truncated-cache", 2, 1, [RED])
expect(opaque.opaque).to_equal(true)
expect(translucent.opaque).to_equal(false)
expect(empty.opaque).to_equal(false)
expect(truncated.opaque).to_equal(false)

step("Render duplicate opaque image commands through the shared path")
val opaque_commands = [
    draw_ir_image_command(
        "opaque-first", 0, 0, 2, 1, opaque.image_uri, []),
    draw_ir_image_command(
        "opaque-second", 0, 0, 2, 1, opaque.image_uri, [])
]
val opaque_batch = draw_ir_batch(
    "opaque-cache", DRAW_IR_BACKEND_CPU,
    draw_ir_embedding_config(
        "surface", "window", 0, 0, 2, 1, 0, 1000, false),
    opaque_commands)
var opaque_expected_engine = Engine2D.create_with_backend(2, 1, "cpu")
opaque_expected_engine.clear(BG)
opaque_expected_engine.draw_image_scaled(
    0, 0, 2, 1, opaque.width, opaque.height, opaque.pixels)
opaque_expected_engine.draw_image_scaled(
    0, 0, 2, 1, opaque.width, opaque.height, opaque.pixels)
val opaque_expected = opaque_expected_engine.read_pixels()
opaque_expected_engine.shutdown()
var opaque_engine = Engine2D.create_with_backend(2, 1, "cpu")
opaque_engine.clear(BG)
val opaque_result = engine2d_draw_ir_adv_batch_with_images(
    opaque_engine, opaque_batch, false, [opaque])
expect(opaque_result.rendered_command_count).to_equal(2)
expect(opaque_result.pixels).to_equal(opaque_expected)
opaque_engine.shutdown()

step("Render duplicate translucent image commands through blending")
val translucent_commands = [
    draw_ir_image_command(
        "translucent-first", 0, 0, 2, 1,
        translucent.image_uri, []),
    draw_ir_image_command(
        "translucent-second", 0, 0, 2, 1,
        translucent.image_uri, [])
]
val translucent_batch = draw_ir_batch(
    "translucent-cache", DRAW_IR_BACKEND_CPU,
    draw_ir_embedding_config(
        "surface", "window", 0, 0, 2, 1, 0, 1000, false),
    translucent_commands)
var translucent_expected_engine = Engine2D.create_with_backend(
    2, 1, "cpu")
translucent_expected_engine.clear(BG)
translucent_expected_engine.draw_image_blend(
    0, 0, 2, 1, translucent.pixels)
translucent_expected_engine.draw_image_blend(
    0, 0, 2, 1, translucent.pixels)
val translucent_expected = translucent_expected_engine.read_pixels()
translucent_expected_engine.shutdown()
var translucent_engine = Engine2D.create_with_backend(2, 1, "cpu")
translucent_engine.clear(BG)
val translucent_result = engine2d_draw_ir_adv_batch_with_images(
    translucent_engine, translucent_batch, false, [translucent])
expect(translucent_result.rendered_command_count).to_equal(2)
expect(translucent_result.pixels).to_equal(translucent_expected)
translucent_engine.shutdown()

step("Keep translucent first-frame images outside fresh-device admission")
val fresh_batch = draw_ir_batch(
    "translucent-fresh", DRAW_IR_BACKEND_GPU,
    draw_ir_embedding_config(
        "surface", "window", 0, 0, 2, 1, 0, 1000, true),
    [draw_ir_image_command(
        "translucent-fresh", 0, 0, 2, 1,
        translucent.image_uri, [])])
val fresh_composition = draw_ir_composition(
    "translucent-fresh", "scene", DRAW_IR_BACKEND_GPU, [fresh_batch])
var fresh_engine = Engine2D.create_with_backend(2, 1, "cpu")
val fresh_result = (
    engine2d_draw_ir_adv_fresh_device_composition_with_images(
        fresh_engine, fresh_composition, [translucent])
)
expect(fresh_result.readback_source).to_equal("preflight_rejected")
expect(fresh_result.fallback_reason).to_contain(
    "fresh-device-opaque-full-target-first-command-required")
fresh_engine.shutdown()

```

</details>

#### samples canonical CSS background image repeat modes with exact alpha pixels

-  css background style
   - Expected: no_repeat.pixels equals `[`
-  css background style
   - Expected: repeat_x.pixels equals `[`
-  css background style
   - Expected: repeat_y.pixels equals `[`
-  css background style
   - Expected: repeat.pixels equals `[`


<details>
<summary>Executable SSpec</summary>

Runnable source: 35 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val no_repeat = _css_background_result(
    _css_background_style("no-repeat", "1", "1", "2", "2"),
    0, 0, 4, 3, 4, 3)
expect(no_repeat.pixels).to_equal([
    BG, BG, BG, BG,
    BG, RED, GREEN, BG,
    BG, BLUE, HALF_RED_OVER_BG, BG
])

val repeat_x = _css_background_result(
    _css_background_style("repeat-x", "1", "1", "2", "2"),
    0, 0, 4, 3, 4, 3)
expect(repeat_x.pixels).to_equal([
    BG, BG, BG, BG,
    GREEN, RED, GREEN, RED,
    HALF_RED_OVER_BG, BLUE, HALF_RED_OVER_BG, BLUE
])

val repeat_y = _css_background_result(
    _css_background_style("repeat-y", "1", "1", "2", "2"),
    0, 0, 4, 3, 4, 3)
expect(repeat_y.pixels).to_equal([
    BG, BLUE, HALF_RED_OVER_BG, BG,
    BG, RED, GREEN, BG,
    BG, BLUE, HALF_RED_OVER_BG, BG
])

val repeat = _css_background_result(
    _css_background_style("repeat", "1", "1", "2", "2"),
    0, 0, 4, 3, 4, 3)
expect(repeat.pixels).to_equal([
    HALF_RED_OVER_BG, BLUE, HALF_RED_OVER_BG, BLUE,
    GREEN, RED, GREEN, RED,
    HALF_RED_OVER_BG, BLUE, HALF_RED_OVER_BG, BLUE
])
```

</details>

#### uses positive modulo for a negative CSS background tile offset

-  css background style
   - Expected: result.rendered_command_count equals `1`
   - Expected: result.skipped_command_count equals `0`
   - Expected: result.pixels equals `[GREEN, RED, GREEN]`
- var embedded engine = Engine2D create with backend
- embedded engine clear
-  css background style
   - Expected: embedded_result.pixels equals `[`
- embedded engine shutdown


<details>
<summary>Executable SSpec</summary>

Runnable source: 27 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = _css_background_result(
    _css_background_style("repeat", "-1", "0", "2", "1"),
    0, 0, 3, 1, 3, 1)
expect(result.rendered_command_count).to_equal(1)
expect(result.skipped_command_count).to_equal(0)
expect(result.pixels).to_equal([GREEN, RED, GREEN])

var embedded_engine = Engine2D.create_with_backend(5, 1, "cpu")
embedded_engine.clear(BG)
val embedded_command = draw_ir_image_command(
    "embedded-css-background", 0, 0, 3, 1,
    "image://css-background",
    _css_background_style("repeat", "-1", "0", "2", "1"))
val embedded_batch = draw_ir_batch(
    "embedded-css-background", DRAW_IR_BACKEND_CPU,
    draw_ir_embedding_config(
        "surface", "window", 2, 0, 3, 1, 0, 1000, true),
    [embedded_command])
val embedded_image = engine2d_resolved_draw_ir_image(
    "image://css-background", 2, 2,
    [RED, GREEN, BLUE, HALF_RED])
val embedded_result = engine2d_draw_ir_adv_batch_with_images(
    embedded_engine, embedded_batch, false, [embedded_image])
expect(embedded_result.pixels).to_equal([
    BG, BG, GREEN, RED, GREEN
])
embedded_engine.shutdown()
```

</details>

#### masks a clipped CSS background against its unclipped rounded shape

- var engine = Engine2D create with backend
- engine clear
- draw ir style prop
- draw ir style prop
- draw ir style prop
- draw ir style prop
- draw ir style prop
- draw ir style prop
- draw ir style prop
- draw ir style prop
- draw ir style prop
- draw ir style prop
- draw ir style prop
- draw ir style prop
- draw ir style prop
- draw ir style prop
- draw ir style prop
- draw ir style prop
- draw ir style prop
- draw ir style prop
   - Expected: result.rendered_command_count equals `1`
   - Expected: result.skipped_command_count equals `0`
   - Expected: result.pixels[0] equals `BG`
   - Expected: result.pixels[1] equals `BG`
   - Expected: result.pixels[2] equals `RED`
   - Expected: result.pixels[2 + 7 * 10] equals `RED`
- engine shutdown


<details>
<summary>Executable SSpec</summary>

Runnable source: 40 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var engine = Engine2D.create_with_backend(10, 8, "cpu")
engine.clear(BG)
val command = draw_ir_image_command(
    "rounded-css-background", 2, 0, 8, 8,
    "image://rounded-css-background", [
        draw_ir_style_prop("image-role", "css-background"),
        draw_ir_style_prop("background-repeat", "repeat"),
        draw_ir_style_prop("background-tile-x", "0"),
        draw_ir_style_prop("background-tile-y", "0"),
        draw_ir_style_prop("background-tile-width", "1"),
        draw_ir_style_prop("background-tile-height", "1"),
        draw_ir_style_prop("background-shape-x", "0"),
        draw_ir_style_prop("background-shape-y", "0"),
        draw_ir_style_prop("background-shape-width", "12"),
        draw_ir_style_prop("background-shape-height", "8"),
        draw_ir_style_prop("background-radius-tl-x", "4"),
        draw_ir_style_prop("background-radius-tl-y", "4"),
        draw_ir_style_prop("background-radius-tr-x", "0"),
        draw_ir_style_prop("background-radius-tr-y", "0"),
        draw_ir_style_prop("background-radius-br-x", "0"),
        draw_ir_style_prop("background-radius-br-y", "0"),
        draw_ir_style_prop("background-radius-bl-x", "0"),
        draw_ir_style_prop("background-radius-bl-y", "0")
    ])
val batch = draw_ir_batch(
    "rounded-css-background", DRAW_IR_BACKEND_CPU,
    draw_ir_embedding_config(
        "surface", "window", 0, 0, 10, 8, 0, 1000, false),
    [command])
val image = engine2d_resolved_draw_ir_image(
    "image://rounded-css-background", 1, 1, [RED])
val result = engine2d_draw_ir_adv_batch_with_images(
    engine, batch, false, [image])
expect(result.rendered_command_count).to_equal(1)
expect(result.skipped_command_count).to_equal(0)
expect(result.pixels[0]).to_equal(BG)
expect(result.pixels[1]).to_equal(BG)
expect(result.pixels[2]).to_equal(RED)
expect(result.pixels[2 + 7 * 10]).to_equal(RED)
engine.shutdown()
```

</details>

#### bounds aggregate CSS work without charging a missing image

- var engine = Engine2D create with backend
- engine clear
-  css background style
-  css background style
-  css background style
   - Expected: result.rendered_command_count equals `1`
   - Expected: result.skipped_command_count equals `2`
   - Expected: result.pixels equals `[`
- engine shutdown


<details>
<summary>Executable SSpec</summary>

Runnable source: 43 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var engine = Engine2D.create_with_backend(4, 2, "cpu")
engine.clear(BG)
val first = draw_ir_image_command(
    "first-css-background", 0, 0, 3, 2,
    "image://missing-css-background",
    _css_background_style("repeat", "0", "0", "1", "1"))
val second = draw_ir_image_command(
    "second-css-background", 1, 0, 3, 2,
    "image://aggregate-css-background",
    _css_background_style("repeat", "0", "0", "1", "1"))
val third = draw_ir_image_command(
    "third-css-background", 0, 0, 3, 2,
    "image://aggregate-css-background",
    _css_background_style("repeat", "0", "0", "1", "1"))
val first_batch = draw_ir_batch(
    "first-css-background", DRAW_IR_BACKEND_CPU,
    draw_ir_embedding_config(
        "surface", "window", 0, 0, 4, 2, 0, 1000, false),
    [first])
val second_batch = draw_ir_batch(
    "second-css-background", DRAW_IR_BACKEND_CPU,
    draw_ir_embedding_config(
        "surface", "window", 0, 0, 4, 2, 1, 1000, false),
    [second])
val third_batch = draw_ir_batch(
    "third-css-background", DRAW_IR_BACKEND_CPU,
    draw_ir_embedding_config(
        "surface", "window", 0, 0, 4, 2, 2, 1000, false),
    [third])
val composition = draw_ir_composition(
    "aggregate-css-background", "scene", DRAW_IR_BACKEND_CPU,
    [first_batch, second_batch, third_batch])
val image = engine2d_resolved_draw_ir_image(
    "image://aggregate-css-background", 1, 1, [RED])
val result = engine2d_draw_ir_adv_composition_with_images(
    engine, composition, false, [image])
expect(result.rendered_command_count).to_equal(1)
expect(result.skipped_command_count).to_equal(2)
expect(result.pixels).to_equal([
    BG, RED, RED, RED,
    BG, RED, RED, RED
])
engine.shutdown()
```

</details>

#### rejects noncanonical duplicate overflow and over-target CSS background work

-  css background style
   - Expected: noncanonical.rendered_command_count equals `0`
   - Expected: noncanonical.skipped_command_count equals `1`
   - Expected: noncanonical.pixels equals `[BG; 12]`
- draw ir style prop
   - Expected: duplicate.skipped_command_count equals `1`
   - Expected: overflow.skipped_command_count equals `1`
-  css background style
   - Expected: over_target.rendered_command_count equals `0`
   - Expected: over_target.skipped_command_count equals `1`
   - Expected: over_target.pixels equals `[BG; 16]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 27 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val noncanonical = _css_background_result(
    _css_background_style("repeat", "0", "0", "02", "2"),
    0, 0, 4, 3, 4, 3)
expect(noncanonical.rendered_command_count).to_equal(0)
expect(noncanonical.skipped_command_count).to_equal(1)
expect(noncanonical.pixels).to_equal([BG; 12])

var duplicate_style = _css_background_style(
    "repeat", "0", "0", "2", "2")
duplicate_style.push(
    draw_ir_style_prop("background-shape-width", "2147483647"))
val duplicate = _css_background_result(
    duplicate_style, 0, 0, 4, 3, 4, 3)
expect(duplicate.skipped_command_count).to_equal(1)

val overflow = _css_background_result(
    _css_background_style(
        "repeat", "2147483648", "0", "2", "2"),
    0, 0, 4, 3, 4, 3)
expect(overflow.skipped_command_count).to_equal(1)

val over_target = _css_background_result(
    _css_background_style("repeat", "0", "0", "2", "2"),
    0, 0, 5, 5, 4, 4)
expect(over_target.rendered_command_count).to_equal(0)
expect(over_target.skipped_command_count).to_equal(1)
expect(over_target.pixels).to_equal([BG; 16])
```

</details>

#### admits the canonical CSS background border overlay through fresh-device preflight

- var engine = Engine2D create with backend
- draw ir no rect
- draw ir no rect
- draw ir style prop
- draw ir style prop
- draw ir style prop
- draw ir style prop
- draw ir style prop
- draw ir style prop
- draw ir style prop
- draw ir style prop
- [draw ir rect
   - Expected: result.readback_source equals `cpu_mirror`
   - Expected: result.rendered_command_count equals `2`
   - Expected: result.skipped_command_count equals `0`
   - Expected: result.pixels[0] equals `GREEN`
   - Expected: result.pixels[1 * 4 + 1] equals `BLUE`
- engine shutdown


<details>
<summary>Executable SSpec</summary>

Runnable source: 33 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var engine = Engine2D.create_with_backend(4, 4, "cpu")
val overlay = draw_ir_box_with_style(
    "css-background-border-overlay", 0, 0, 4, 4, 0u32,
    draw_ir_no_rect(), draw_ir_no_rect(), draw_ir_no_rect(),
    draw_ir_no_rect(), [
        draw_ir_style_prop(
            "image-role", "css-background-border-overlay"),
        draw_ir_style_prop("border-top-width", "1"),
        draw_ir_style_prop("border-right-width", "1"),
        draw_ir_style_prop("border-bottom-width", "1"),
        draw_ir_style_prop("border-left-width", "1"),
        draw_ir_style_prop("border-top-color", "{GREEN}"),
        draw_ir_style_prop("border-right-color", "{GREEN}"),
        draw_ir_style_prop("border-bottom-color", "{GREEN}"),
        draw_ir_style_prop("border-left-color", "{GREEN}")
    ])
val batch = draw_ir_batch(
    "css-background-border-overlay", DRAW_IR_BACKEND_CPU,
    draw_ir_embedding_config(
        "surface", "window", 0, 0, 4, 4, 0, 1000, false),
    [draw_ir_rect("canvas", 0, 0, 4, 4, BLUE), overlay])
val composition = draw_ir_composition(
    "css-background-border-overlay", "scene", DRAW_IR_BACKEND_CPU,
    [batch])
var images: [Engine2dResolvedDrawIrImage] = []
val result = engine2d_draw_ir_adv_fresh_device_composition_with_images(
    engine, composition, images)
expect(result.readback_source).to_equal("cpu_mirror")
expect(result.rendered_command_count).to_equal(2)
expect(result.skipped_command_count).to_equal(0)
expect(result.pixels[0]).to_equal(GREEN)
expect(result.pixels[1 * 4 + 1]).to_equal(BLUE)
engine.shutdown()
```

</details>

#### admits the fallback material hash but rejects an unknown sibling key

- draw ir no rect
- draw ir no rect
- draw ir no rect
- draw ir no rect
- var admitted engine = Engine2D create with backend
- admitted engine shutdown
- var unknown engine = Engine2D create with backend
- unknown engine shutdown
   - Expected: admitted_result.readback_source equals `cpu_mirror`
   - Expected: admitted_result.skipped_command_count equals `0`
   - Expected: unknown_result.readback_source equals `preflight_rejected`


<details>
<summary>Executable SSpec</summary>

Runnable source: 60 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val admitted = draw_ir_box_with_style(
    "admitted-material-hash", 0, 0, 4, 4, BLUE,
    draw_ir_no_rect(), draw_ir_no_rect(), draw_ir_no_rect(),
    draw_ir_no_rect(), [
        draw_ir_style_prop(
            "backdrop-filter-fallback-material-hash", ""
        )
    ]
)
val unknown = draw_ir_box_with_style(
    "unknown-material-key", 0, 0, 4, 4, BLUE,
    draw_ir_no_rect(), draw_ir_no_rect(), draw_ir_no_rect(),
    draw_ir_no_rect(), [
        draw_ir_style_prop(
            "backdrop-filter-fallback-material-unknown", ""
        )
    ]
)
val admitted_composition = draw_ir_composition(
    "admitted-material-hash", "scene", DRAW_IR_BACKEND_CPU,
    [draw_ir_batch(
        "admitted-material-hash", DRAW_IR_BACKEND_CPU,
        draw_ir_embedding_config(
            "surface", "window", 0, 0, 4, 4, 0, 1000, false
        ),
        [admitted]
    )]
)
val unknown_composition = draw_ir_composition(
    "unknown-material-key", "scene", DRAW_IR_BACKEND_CPU,
    [draw_ir_batch(
        "unknown-material-key", DRAW_IR_BACKEND_CPU,
        draw_ir_embedding_config(
            "surface", "window", 0, 0, 4, 4, 0, 1000, false
        ),
        [unknown]
    )]
)
var images: [Engine2dResolvedDrawIrImage] = []
var admitted_engine = Engine2D.create_with_backend(4, 4, "cpu")
val admitted_result = (
    engine2d_draw_ir_adv_fresh_device_composition_with_images(
        admitted_engine, admitted_composition, images
    )
)
admitted_engine.shutdown()
var unknown_engine = Engine2D.create_with_backend(4, 4, "cpu")
val unknown_result = (
    engine2d_draw_ir_adv_fresh_device_composition_with_images(
        unknown_engine, unknown_composition, images
    )
)
unknown_engine.shutdown()

expect(admitted_result.readback_source).to_equal("cpu_mirror")
expect(admitted_result.skipped_command_count).to_equal(0)
expect(unknown_result.readback_source).to_equal("preflight_rejected")
expect(unknown_result.fallback_reason).to_contain(
    "fresh-device-command-preflight-required"
)
```

</details>

#### rejects malformed and gap-producing CSS backgrounds in fresh-device preflight

- draw ir style prop
- var duplicate engine = Engine2D create with backend
   - Expected: duplicate_result.readback_source equals `preflight_rejected`
- duplicate engine shutdown
-  css background style
- var no repeat engine = Engine2D create with backend
- no repeat engine shutdown


<details>
<summary>Executable SSpec</summary>

Runnable source: 49 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val image = engine2d_resolved_draw_ir_image(
    "image://fresh-css-background", 2, 2,
    [RED, GREEN, BLUE, YELLOW])

var duplicate_style = _css_background_style(
    "repeat", "0", "0", "2", "2")
duplicate_style.push(
    draw_ir_style_prop("background-tile-width", "2"))
val duplicate_command = draw_ir_image_command(
    "duplicate-css-background", 0, 0, 4, 4,
    "image://fresh-css-background", duplicate_style)
val duplicate_batch = draw_ir_batch(
    "duplicate-css-background", DRAW_IR_BACKEND_CPU,
    draw_ir_embedding_config(
        "surface", "window", 0, 0, 4, 4, 0, 1000, false),
    [duplicate_command])
val duplicate_composition = draw_ir_composition(
    "duplicate-css-background", "scene", DRAW_IR_BACKEND_CPU,
    [duplicate_batch])
var duplicate_engine = Engine2D.create_with_backend(4, 4, "cpu")
val duplicate_result = (
    engine2d_draw_ir_adv_fresh_device_composition_with_images(
        duplicate_engine, duplicate_composition, [image]))
expect(duplicate_result.readback_source).to_equal("preflight_rejected")
expect(duplicate_result.fallback_reason).to_contain(
    "fresh-device-command-preflight-required")
duplicate_engine.shutdown()

val no_repeat_command = draw_ir_image_command(
    "no-repeat-css-background", 0, 0, 4, 4,
    "image://fresh-css-background",
    _css_background_style("no-repeat", "0", "0", "1", "1"))
val no_repeat_batch = draw_ir_batch(
    "no-repeat-css-background", DRAW_IR_BACKEND_CPU,
    draw_ir_embedding_config(
        "surface", "window", 0, 0, 4, 4, 0, 1000, false),
    [no_repeat_command])
val no_repeat_composition = draw_ir_composition(
    "no-repeat-css-background", "scene", DRAW_IR_BACKEND_CPU,
    [no_repeat_batch])
var no_repeat_engine = Engine2D.create_with_backend(4, 4, "cpu")
val no_repeat_result = (
    engine2d_draw_ir_adv_fresh_device_composition_with_images(
        no_repeat_engine, no_repeat_composition, [image]))
expect(no_repeat_result.readback_source).to_equal(
    "preflight_rejected")
expect(no_repeat_result.fallback_reason).to_contain(
    "fresh-device-opaque-full-target-first-command-required")
no_repeat_engine.shutdown()
```

</details>

#### clips Draw IR text and restores the enclosing Engine2D route

- var direct = Engine2D create with backend
- direct clear
- direct draw text
- var engine = Engine2D create with backend
- engine clear
- draw ir rect bounds
- draw ir embedding config
- [clipped, draw ir rect
   - Expected: clipped.clip_rect.width equals `1`
   - Expected: direct_pixels[1] equals `GREEN`
   - Expected: pixels[1] equals `BG`
   - Expected: pixels[12] equals `RED`
- var enclosed = Engine2D create with backend
- enclosed clear
- draw ir embedding config
- draw ir rect bounds
- draw ir rect
- draw ir rect
   - Expected: enclosed_result.pixels[5] equals `RED`
   - Expected: enclosed_result.pixels[9] equals `BG`


<details>
<summary>Executable SSpec</summary>

Runnable source: 40 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var direct = Engine2D.create_with_backend(24, 16, "cpu")
direct.clear(BG)
direct.draw_text(0, 0, "A", GREEN, 12)
val direct_pixels = direct.read_pixels()
var engine = Engine2D.create_with_backend(24, 16, "cpu")
engine.clear(BG)
val clipped = draw_ir_text_styled_clipped(
    "input", 0, 0, "A", GREEN, [],
    draw_ir_rect_bounds(0, 0, 1, 12)
)
val batch = draw_ir_batch(
    "clipped-input", DRAW_IR_BACKEND_CPU,
    draw_ir_embedding_config("surf", "win", 0, 0, 24, 16, 0, 1000, false),
    [clipped, draw_ir_rect("after-text", 12, 0, 2, 2, RED)]
)
val result = engine2d_draw_ir_adv_batch(engine, batch, false)
val pixels = result.pixels

expect(clipped.clip_rect.present).to_be(true)
expect(clipped.clip_rect.width).to_equal(1)
expect(direct_pixels[1]).to_equal(GREEN)
expect(pixels[1]).to_equal(BG)
expect(pixels[12]).to_equal(RED)

var enclosed = Engine2D.create_with_backend(24, 16, "cpu")
enclosed.clear(BG)
val enclosed_batch = draw_ir_batch(
    "enclosed-clipped-input", DRAW_IR_BACKEND_CPU,
    draw_ir_embedding_config("surf", "win", 4, 0, 4, 8, 0, 1000, true), [
        draw_ir_text_styled_clipped(
            "input", 0, 0, "A", GREEN, [],
            draw_ir_rect_bounds(0, 0, 1, 7)
        ),
        draw_ir_rect("inside-enclosing-clip", 1, 0, 1, 1, RED),
        draw_ir_rect("outside-enclosing-clip", 5, 0, 1, 1, RED)
    ]
)
val enclosed_result = engine2d_draw_ir_adv_batch(enclosed, enclosed_batch, false)
expect(enclosed_result.pixels[5]).to_equal(RED)
expect(enclosed_result.pixels[9]).to_equal(BG)
```

</details>

#### fails closed on overflowing numeric style metadata

- var direct = Engine2D create with backend
- direct clear
- direct draw text
- direct draw rect filled
- var routed = Engine2D create with backend
- routed clear
- draw ir style prop
- draw ir no rect
- draw ir style prop
- draw ir style prop
- draw ir style prop
- draw ir style prop
- draw ir style prop
- draw ir style prop
- draw ir style prop
   - Expected: result.pixels equals `expected`
- direct shutdown
- routed shutdown


<details>
<summary>Executable SSpec</summary>

Runnable source: 31 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var direct = Engine2D.create_with_backend(32, 24, "cpu")
direct.clear(BG)
direct.draw_text(2, 3, "A", GREEN, 12)
direct.draw_rect_filled(10, 10, 4, 4, RED)
val expected = direct.read_pixels()

var routed = Engine2D.create_with_backend(32, 24, "cpu")
routed.clear(BG)
val batch = draw_ir_batch("hostile-style", DRAW_IR_BACKEND_CPU, draw_ir_embedding_config("surf", "win", 0, 0, 32, 24, 1, 1000, false), [
    draw_ir_text_styled("label", 2, 3, "A", GREEN, [
        draw_ir_style_prop("font-size", "999999999999999999999999")
    ]),
    draw_ir_box_with_style(
        "box", 10, 10, 4, 4, RED,
        draw_ir_no_rect(), draw_ir_no_rect(), draw_ir_no_rect(), draw_ir_no_rect(),
        [
            draw_ir_style_prop("border-top-width", "18446744073709551617"),
            draw_ir_style_prop("border-top-color", "4278190335"),
            draw_ir_style_prop("backdrop-filter", "blur(0) saturate(9223372036854775807)"),
            draw_ir_style_prop("backdrop-filter-capability", "engine2d-cpu-composited-material-v1"),
            draw_ir_style_prop("backdrop-filter-realized-blur-radius-px", "0"),
            draw_ir_style_prop("backdrop-filter-realized-saturation-milli", "1000"),
            draw_ir_style_prop("wm-material-surface-alpha-milli", "1000")
        ]
    )
])
val result = engine2d_draw_ir_adv_batch(routed, batch, false)

expect(result.pixels).to_equal(expected)
direct.shutdown()
routed.shutdown()
```

</details>

#### keeps unstyled Draw IR text on the legacy Engine2D route

- var direct = Engine2D create with backend
- direct clear
- direct draw text
- var routed = Engine2D create with backend
- routed clear
- draw ir text
   - Expected: result.pixels equals `expected`
- direct shutdown
- routed shutdown


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var direct = Engine2D.create_with_backend(32, 24, "cpu")
direct.clear(BG)
direct.draw_text(2, 3, "A", GREEN, 12)
val expected = direct.read_pixels()

var routed = Engine2D.create_with_backend(32, 24, "cpu")
routed.clear(BG)
val batch = draw_ir_batch("legacy-text", DRAW_IR_BACKEND_GPU, draw_ir_embedding_config("surf", "win", 0, 0, 32, 24, 1, 1000, false), [
    draw_ir_text("label", 2, 3, "A", GREEN)
])
val result = engine2d_draw_ir_adv_batch(routed, batch, false)

expect(result.pixels).to_equal(expected)
direct.shutdown()
routed.shutdown()
```

</details>

#### skips text when its selected font identity cannot load

- var engine = Engine2D create with backend
- engine clear
- draw ir text styled
   - Expected: result.rendered_command_count equals `0`
   - Expected: result.skipped_command_count equals `1`
   - Expected: result.fallback_required is true
   - Expected: result.pixels[3 * 32 + 2] equals `BG`
- engine shutdown


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var engine = Engine2D.create_with_backend(32, 24, "cpu")
engine.clear(BG)
val batch = draw_ir_batch("missing-font", DRAW_IR_BACKEND_CPU, draw_ir_embedding_config("surf", "win", 0, 0, 32, 24, 1, 1000, false), [
    draw_ir_text_styled("label", 2, 3, "A", GREEN, [draw_ir_style_prop("font-identity", "sha256=missing")])
])

val result = engine2d_draw_ir_adv_batch(engine, batch, false)

expect(result.rendered_command_count).to_equal(0)
expect(result.skipped_command_count).to_equal(1)
expect(result.fallback_required).to_equal(true)
expect(result.fallback_reason).to_contain("text-font-identity")
expect(result.pixels[3 * 32 + 2]).to_equal(BG)
engine.shutdown()
```

</details>

#### fails closed when shaped clusters do not index serialized advances

- var engine = Engine2D create with backend
- engine clear
- selected font asset identity
- draw ir embedding config
   - Expected: result.rendered_command_count equals `0`
   - Expected: result.skipped_command_count equals `1`
- engine shutdown


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var engine = Engine2D.create_with_backend(32, 24, "cpu")
engine.clear(BG)
val candidate = selected_font_asset_candidates()[8]
val malformed = draw_ir_glyph_run_payload([36u32], [0], [0], [4], true)
val command = draw_ir_text_shaped_font(
    "shaped", 2, 3, "A", GREEN, candidate.family,
    selected_font_asset_identity(candidate), [7], 7, 14, 12, malformed
)
val batch = draw_ir_batch("malformed-shaped", DRAW_IR_BACKEND_CPU,
    draw_ir_embedding_config("surf", "win", 0, 0, 32, 24, 1, 1000, false), [command])

val result = engine2d_draw_ir_adv_batch(engine, batch, false)

expect(result.rendered_command_count).to_equal(0)
expect(result.skipped_command_count).to_equal(1)
expect(result.fallback_reason).to_contain("text-font-shaping")
engine.shutdown()
```

</details>

#### executes a Draw IR batch through the Simple2D advanced interface with embedding offsets

- var engine = Engine2D create with backend
- engine clear
- draw ir rect
   - Expected: semantic.check_exists("body").unwrap() is true
   - Expected: semantic.check_visible("body").unwrap() is true
   - Expected: body.kind equals `rect`
   - Expected: body.widget_id equals `body`
   - Expected: result.unit_id equals `batch-rect`
   - Expected: result.selected_backend equals `cpu`
   - Expected: result.fallback_required is true
   - Expected: result.rendered_command_count equals `1`
   - Expected: result.skipped_command_count equals `0`
   - Expected: result.pixels[8 * 32 + 6] equals `RED`
- engine shutdown


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var engine = Engine2D.create_with_backend(32, 24, "cpu")
engine.clear(BG)
val embedding = draw_ir_embedding_config("surf1", "win1", 4, 5, 20, 16, 10, 1000, true)
val batch = draw_ir_batch("batch-rect", DRAW_IR_BACKEND_GPU, embedding, [
    draw_ir_rect("body", 2, 3, 6, 5, RED)
])

val semantic = SgttiTestDriver.new(sgtti_snapshot_from_draw_ir_batch(batch, 1000, 5000, 1000))
val body = semantic.get_element("body").unwrap()
expect(semantic.check_exists("body").unwrap()).to_equal(true)
expect(semantic.check_visible("body").unwrap()).to_equal(true)
expect(body.kind).to_equal("rect")
expect(body.widget_id).to_equal("body")

val result = engine2d_draw_ir_adv_batch(engine, batch, false)

expect(result.unit_id).to_equal("batch-rect")
expect(result.selected_backend).to_equal("cpu")
expect(result.fallback_required).to_equal(true)
expect(result.fallback_reason).to_contain("gpu backend unavailable")
expect(result.rendered_command_count).to_equal(1)
expect(result.skipped_command_count).to_equal(0)
expect(result.pixels[8 * 32 + 6]).to_equal(RED)
engine.shutdown()
```

</details>

#### submits a GPU-selected Draw IR batch through the runtime host GPU queue

- engine2d host gpu runtime reset
- var engine = Engine2D create with backend
- engine clear
- draw ir rect
   - Expected: result.render.unit_id equals `runtime-batch-runtime`
   - Expected: result.render.selected_backend equals `gpu`
   - Expected: result.render.rendered_command_count equals `1`
   - Expected: result.runtime_submit.packet_id equals `1`
   - Expected: result.runtime_drain.drained equals `1`
   - Expected: result.runtime_drain.status equals `completed`
   - Expected: result.render.pixels[3 * 32 + 2] equals `GREEN`
- engine shutdown


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
engine2d_host_gpu_runtime_reset()
var engine = Engine2D.create_with_backend(32, 24, "cpu")
engine.clear(BG)
val batch = draw_ir_batch("batch-runtime", DRAW_IR_BACKEND_GPU, draw_ir_embedding_config("surf1", "win1", 0, 0, 20, 16, 10, 1000, false), [
    draw_ir_rect("body", 2, 3, 6, 5, GREEN)
])
val queue = engine2d_host_gpu_runtime_queue_with_backend_handle("vulkan", 7, 7, true, 4096)

val result = engine2d_draw_ir_adv_batch_runtime_queue(engine, batch, true, queue)

expect(result.render.unit_id).to_equal("runtime-batch-runtime")
expect(result.render.selected_backend).to_equal("gpu")
expect(result.render.rendered_command_count).to_equal(1)
expect(result.runtime_submit.submitted).to_be(true)
expect(result.runtime_submit.packet_id).to_equal(1)
expect(result.runtime_drain.drained).to_equal(1)
expect(result.runtime_drain.status).to_equal("completed")
expect(result.queued_for_gpu).to_be(true)
expect(result.render.pixels[3 * 32 + 2]).to_equal(GREEN)
engine.shutdown()
```

</details>

#### executes a composed Draw IR scene in batch order

- var engine = Engine2D create with backend
- engine clear
- draw ir rect
- draw ir rect
   - Expected: result.unit_id equals `wm-composite`
   - Expected: result.rendered_command_count equals `2`
   - Expected: result.skipped_command_count equals `0`
   - Expected: result.pixels[1 * 32 + 1] equals `RED`
   - Expected: result.pixels[8 * 32 + 7] equals `GREEN`
- engine shutdown


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var engine = Engine2D.create_with_backend(32, 24, "cpu")
engine.clear(BG)
val desktop = draw_ir_batch("desktop", DRAW_IR_BACKEND_GPU, draw_ir_embedding_config("wm", "desktop", 0, 0, 32, 24, 0, 1000, false), [
    draw_ir_rect("bg", 0, 0, 32, 24, RED)
])
val window = draw_ir_batch("window", DRAW_IR_BACKEND_GPU, draw_ir_embedding_config("surf1", "win1", 6, 7, 12, 10, 10, 1000, true), [
    draw_ir_rect("body", 0, 0, 4, 4, GREEN)
])
val composition = draw_ir_composition("wm-composite", "scene-key", DRAW_IR_BACKEND_GPU, [desktop, window])

val result = engine2d_draw_ir_adv_composition(engine, composition, false)

expect(result.unit_id).to_equal("wm-composite")
expect(result.rendered_command_count).to_equal(2)
expect(result.skipped_command_count).to_equal(0)
expect(result.pixels[1 * 32 + 1]).to_equal(RED)
expect(result.pixels[8 * 32 + 7]).to_equal(GREEN)
engine.shutdown()
```

</details>

#### presents a production composition without requesting framebuffer readback

- var engine = Engine2D create with backend
- engine clear
- draw ir rect
- Render the production composition directly to the existing Engine2D surface
- Return accounting without allocating a framebuffer snapshot
   - Expected: rendered_pixels[3 * 16 + 2] equals `GREEN`
   - Expected: result.rendered_command_count equals `1`
   - Expected: result.skipped_command_count equals `0`
   - Expected: result.pixels.len() equals `0`
   - Expected: result.readback_source equals `not_requested`
   - Expected: result.backend_handle equals `0`
   - Expected: result.readback_checksum equals `0`
- engine shutdown


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var engine = Engine2D.create_with_backend(16, 16, "cpu")
engine.clear(BG)
val batch = draw_ir_batch("present-only", DRAW_IR_BACKEND_GPU, draw_ir_embedding_config("wm", "desktop", 0, 0, 16, 16, 0, 1000, false), [
    draw_ir_rect("body", 2, 3, 6, 5, GREEN)
])
val composition = draw_ir_composition("present-only", "scene", DRAW_IR_BACKEND_GPU, [batch])
var images: [Engine2dResolvedDrawIrImage] = []

step("Render the production composition directly to the existing Engine2D surface")
val result = engine2d_draw_ir_adv_composition_present_with_images(engine, composition, false, images)

step("Return accounting without allocating a framebuffer snapshot")
val rendered_pixels = engine.read_pixels()
expect(rendered_pixels[3 * 16 + 2]).to_equal(GREEN)
expect(result.rendered_command_count).to_equal(1)
expect(result.skipped_command_count).to_equal(0)
expect(result.fallback_required).to_be(true)
expect(result.fallback_reason).to_contain("gpu backend unavailable")
expect(result.pixels.len()).to_equal(0)
expect(result.readback_source).to_equal("not_requested")
expect(result.backend_handle).to_equal(0)
expect(result.readback_checksum).to_equal(0)
engine.shutdown()
```

</details>

#### rejects an unsupported present-only composition without requesting readback

- var engine = Engine2D create with backend
- engine clear
   - Expected: result.rendered_command_count equals `0`
   - Expected: result.skipped_command_count equals `1`
   - Expected: result.pixels.len() equals `0`
   - Expected: result.readback_source equals `not_requested`
   - Expected: result.backend_handle equals `0`
   - Expected: result.readback_checksum equals `0`
- engine shutdown


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var engine = Engine2D.create_with_backend(16, 16, "cpu")
engine.clear(BG)
val unsupported = DrawIrCommand(kind: "future-path", component_id: "path", x: 1, y: 1, width: 5, height: 5, color: RED, text_value: "", advance_widths: [], border_rect: draw_ir_no_rect(), content_rect: draw_ir_no_rect(), hit_rect: draw_ir_no_rect(), clip_rect: draw_ir_no_rect(), computed_style: [], edge: nil, parent_id: "", image_uri: "", points: [], glyph_run: draw_ir_empty_glyph_run_payload())
val batch = draw_ir_batch("present-rejected", DRAW_IR_BACKEND_GPU, draw_ir_embedding_config("wm", "desktop", 0, 0, 16, 16, 0, 1000, false), [unsupported])
val composition = draw_ir_composition("present-rejected", "scene", DRAW_IR_BACKEND_GPU, [batch])
var images: [Engine2dResolvedDrawIrImage] = []

val result = engine2d_draw_ir_adv_composition_present_with_images(engine, composition, false, images)

expect(result.rendered_command_count).to_equal(0)
expect(result.skipped_command_count).to_equal(1)
expect(result.fallback_required).to_be(true)
expect(result.pixels.len()).to_equal(0)
expect(result.readback_source).to_equal("not_requested")
expect(result.backend_handle).to_equal(0)
expect(result.readback_checksum).to_equal(0)
engine.shutdown()
```

</details>

#### paints a border on a transparent-background box while the interior stays background color

- var engine = Engine2D create with backend
- engine clear
- draw ir style prop
- draw ir style prop
- draw ir style prop
- draw ir style prop
- draw ir style prop
- draw ir style prop
- draw ir style prop
- draw ir style prop
- ], edge: nil, parent id: "", image uri: "", points: [], glyph run: draw ir empty glyph run payload
   - Expected: result.rendered_command_count equals `1`
   - Expected: result.pixels[2 * 16 + 6] equals `RED`
   - Expected: result.pixels[6 * 16 + 2] equals `RED`
   - Expected: result.pixels[6 * 16 + 6] equals `BG`
- engine shutdown


<details>
<summary>Executable SSpec</summary>

Runnable source: 28 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Regression: the executor used to collapse every RECT to a single flat
# draw_rect_filled gated on background opacity, so a transparent box with
# a visible border vanished. It must now stroke the border independently.
var engine = Engine2D.create_with_backend(16, 16, "cpu")
engine.clear(BG)
val TRANSPARENT: u32 = 0x00000000u32
val bordered = DrawIrCommand(kind: "rect", component_id: "bordered", x: 2, y: 2, width: 10, height: 10, color: TRANSPARENT, text_value: "", advance_widths: [], border_rect: draw_ir_no_rect(), content_rect: draw_ir_no_rect(), hit_rect: draw_ir_no_rect(), clip_rect: draw_ir_no_rect(), computed_style: [
    draw_ir_style_prop("border-top-width", "2"),
    draw_ir_style_prop("border-right-width", "2"),
    draw_ir_style_prop("border-bottom-width", "2"),
    draw_ir_style_prop("border-left-width", "2"),
    draw_ir_style_prop("border-top-color", "{RED}"),
    draw_ir_style_prop("border-right-color", "{RED}"),
    draw_ir_style_prop("border-bottom-color", "{RED}"),
    draw_ir_style_prop("border-left-color", "{RED}")
], edge: nil, parent_id: "", image_uri: "", points: [], glyph_run: draw_ir_empty_glyph_run_payload())
val batch = draw_ir_batch("bordered", DRAW_IR_BACKEND_GPU, draw_ir_embedding_config("surf", "win", 0, 0, 16, 16, 1, 1000, false), [bordered])

val result = engine2d_draw_ir_adv_batch(engine, batch, false)

expect(result.rendered_command_count).to_equal(1)
# Top border row (y=2) paints in the border color.
expect(result.pixels[2 * 16 + 6]).to_equal(RED)
# Left border column (x=2) paints in the border color.
expect(result.pixels[6 * 16 + 2]).to_equal(RED)
# Interior (x=6,y=6) stays the cleared background: transparent bg unfilled.
expect(result.pixels[6 * 16 + 6]).to_equal(BG)
engine.shutdown()
```

</details>

#### rasterizes typed WM gradient border and first outer shadow pixels

- var engine = Engine2D create with backend
- engine clear
- draw ir no rect
- draw ir style prop
- draw ir style prop
- draw ir style prop
- draw ir style prop
- draw ir style prop
- draw ir style prop
- draw ir style prop
- draw ir style prop
- draw ir style prop
- draw ir style prop
   - Expected: result.rendered_command_count equals `1`
   - Expected: result.skipped_command_count equals `0`
   - Expected: result.pixels[8 * 32 + 4] equals `BLUE`
   - Expected: result.pixels[4 * 32 + 12] equals `BLUE`
   - Expected: result.pixels[20 * 32 + 20] equals `YELLOW`
- engine shutdown


<details>
<summary>Executable SSpec</summary>

Runnable source: 29 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var engine = Engine2D.create_with_backend(32, 32, "cpu")
engine.clear(BG)
val command = draw_ir_box_with_style(
    "wm-body", 4, 4, 16, 16, 0xff202020u32,
    draw_ir_no_rect(), draw_ir_no_rect(), draw_ir_no_rect(), draw_ir_no_rect(),
    [
        draw_ir_style_prop("background-image", "linear-gradient({RED},{GREEN})"),
        draw_ir_style_prop("border-top-width", "1"),
        draw_ir_style_prop("border-right-width", "1"),
        draw_ir_style_prop("border-bottom-width", "1"),
        draw_ir_style_prop("border-left-width", "1"),
        draw_ir_style_prop("border-top-color", "{BLUE}"),
        draw_ir_style_prop("border-right-color", "{BLUE}"),
        draw_ir_style_prop("border-bottom-color", "{BLUE}"),
        draw_ir_style_prop("border-left-color", "{BLUE}"),
        draw_ir_style_prop("box-shadow", "2 3 {YELLOW}")
    ]
)
val batch = draw_ir_batch("wm-material", DRAW_IR_BACKEND_CPU, draw_ir_embedding_config("surf", "win", 0, 0, 32, 32, 1, 1000, false), [command])

val result = engine2d_draw_ir_adv_batch(engine, batch, false)

expect(result.rendered_command_count).to_equal(1)
expect(result.skipped_command_count).to_equal(0)
expect(result.pixels[5 * 32 + 12]).to_be_greater_than(result.pixels[18 * 32 + 12])
expect(result.pixels[8 * 32 + 4]).to_equal(BLUE)
expect(result.pixels[4 * 32 + 12]).to_equal(BLUE)
expect(result.pixels[20 * 32 + 20]).to_equal(YELLOW)
engine.shutdown()
```

</details>

#### preserves the rounded solid fallback when glass capability is absent

- var engine = Engine2D create with backend
- engine clear
- draw ir no rect
- draw ir style prop
- draw ir style prop
   - Expected: result.pixels[4 * 24 + 4] equals `BG`
   - Expected: result.pixels[12 * 24 + 12] equals `fallback`
- engine shutdown


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var engine = Engine2D.create_with_backend(24, 24, "cpu")
engine.clear(BG)
val fallback: u32 = 0xff1f1f21u32
val command = draw_ir_box_with_style(
    "rounded-gradient", 4, 4, 16, 16, fallback,
    draw_ir_no_rect(), draw_ir_no_rect(), draw_ir_no_rect(), draw_ir_no_rect(),
    [
        draw_ir_style_prop("background-image", "linear-gradient({RED},{GREEN})"),
        draw_ir_style_prop("border-radius", "6")
    ]
)
val batch = draw_ir_batch("rounded-gradient", DRAW_IR_BACKEND_CPU, draw_ir_embedding_config("surf", "win", 0, 0, 24, 24, 1, 1000, false), [command])

val result = engine2d_draw_ir_adv_batch(engine, batch, false)

expect(result.pixels[4 * 24 + 4]).to_equal(BG)
expect(result.pixels[12 * 24 + 12]).to_equal(fallback)
engine.shutdown()
```

</details>

#### composites the requested rounded glass material over existing pixels

- var engine = Engine2D create with backend
- engine clear
- draw ir no rect
- draw ir style prop
- draw ir style prop
- draw ir style prop
- draw ir style prop
- draw ir style prop
- draw ir style prop
- draw ir style prop
- draw ir style prop
- draw ir style prop
   - Expected: result.rendered_command_count equals `1`
   - Expected: result.skipped_command_count equals `0`
   - Expected: result.cpu_composited_material_count equals `1`
   - Expected: result.metal_device_glass_material_count equals `0`
   - Expected: result.glass_execution_target equals `cpu-scalar-glass-v1`
   - Expected: result.glass_backend_handle equals `0`
   - Expected: result.glass_device_identity equals `0`
   - Expected: result.pixels[4 * 12 + 4] equals `BG`
   - Expected: result.pixels[5 * 12 + 5] equals `0xFF7F7F7Fu32`
- engine shutdown


<details>
<summary>Executable SSpec</summary>

Runnable source: 31 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var engine = Engine2D.create_with_backend(12, 12, "cpu")
engine.clear(BG)
val command = draw_ir_box_with_style(
    "rounded-glass", 4, 4, 4, 4, 0xFF1F1F21u32,
    draw_ir_no_rect(), draw_ir_no_rect(), draw_ir_no_rect(), draw_ir_no_rect(),
    [
        draw_ir_style_prop("wm-material-request", "window-surface-glass"),
        draw_ir_style_prop("wm-material-surface-alpha-milli", "500"),
        draw_ir_style_prop("background-color", "4294967295"),
        draw_ir_style_prop("background-image", "none"),
        draw_ir_style_prop("border-radius", "1"),
        draw_ir_style_prop("backdrop-filter", "blur(0px) saturate(100%)"),
        draw_ir_style_prop("backdrop-filter-realized-blur-radius-px", "0"),
        draw_ir_style_prop("backdrop-filter-realized-saturation-milli", "1000"),
        draw_ir_style_prop("backdrop-filter-capability", "engine2d-cpu-composited-material-v1")
    ]
)
val batch = draw_ir_batch("rounded-glass", DRAW_IR_BACKEND_CPU, draw_ir_embedding_config("surf", "win", 0, 0, 12, 12, 1, 1000, false), [command])

val result = engine2d_draw_ir_adv_batch(engine, batch, false)

expect(result.rendered_command_count).to_equal(1)
expect(result.skipped_command_count).to_equal(0)
expect(result.cpu_composited_material_count).to_equal(1)
expect(result.metal_device_glass_material_count).to_equal(0)
expect(result.glass_execution_target).to_equal("cpu-scalar-glass-v1")
expect(result.glass_backend_handle).to_equal(0)
expect(result.glass_device_identity).to_equal(0)
expect(result.pixels[4 * 12 + 4]).to_equal(BG)
expect(result.pixels[5 * 12 + 5]).to_equal(0xFF7F7F7Fu32)
engine.shutdown()
```

</details>

#### samples the painted parent backdrop and receipts an embedded material batch

- var engine = Engine2D create with backend
- engine clear
- draw ir no rect
- draw ir style prop
- draw ir style prop
- draw ir style prop
- draw ir style prop
- draw ir style prop
- draw ir style prop
- draw ir style prop
- draw ir style prop
- draw ir style prop
   - Expected: result.rendered_command_count equals `1`
   - Expected: result.skipped_command_count equals `0`
   - Expected: result.cpu_composited_material_count equals `1`
   - Expected: result.glass_execution_target equals `cpu-scalar-glass-v1`
   - Expected: result.readback_source equals `cpu_mirror`
   - Expected: result.glass_backend_handle equals `0`
   - Expected: result.glass_device_identity equals `0`
   - Expected: result.pixels[4 * 12 + 4] equals `BLUE`
   - Expected: result.pixels[5 * 12 + 5] equals `0xFF7F7FFFu32`
- engine shutdown


<details>
<summary>Executable SSpec</summary>

Runnable source: 31 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var engine = Engine2D.create_with_backend(12, 12, "cpu")
engine.clear(BLUE)
val command = draw_ir_box_with_style(
    "embedded-glass", 0, 0, 4, 4, 0xFF1F1F21u32,
    draw_ir_no_rect(), draw_ir_no_rect(), draw_ir_no_rect(), draw_ir_no_rect(),
    [
        draw_ir_style_prop("wm-material-request", "window-surface-glass"),
        draw_ir_style_prop("wm-material-surface-alpha-milli", "500"),
        draw_ir_style_prop("background-color", "4294967295"),
        draw_ir_style_prop("background-image", "none"),
        draw_ir_style_prop("border-radius", "1"),
        draw_ir_style_prop("backdrop-filter", "blur(0px) saturate(100%)"),
        draw_ir_style_prop("backdrop-filter-realized-blur-radius-px", "0"),
        draw_ir_style_prop("backdrop-filter-realized-saturation-milli", "1000"),
        draw_ir_style_prop("backdrop-filter-capability", "engine2d-composited-glass-material-v1")
    ]
)
val batch = draw_ir_batch("embedded-glass", DRAW_IR_BACKEND_CPU, draw_ir_embedding_config("surf", "win", 4, 4, 4, 4, 1, 1000, true), [command])

val result = engine2d_draw_ir_adv_batch(engine, batch, false)

expect(result.rendered_command_count).to_equal(1)
expect(result.skipped_command_count).to_equal(0)
expect(result.cpu_composited_material_count).to_equal(1)
expect(result.glass_execution_target).to_equal("cpu-scalar-glass-v1")
expect(result.readback_source).to_equal("cpu_mirror")
expect(result.glass_backend_handle).to_equal(0)
expect(result.glass_device_identity).to_equal(0)
expect(result.pixels[4 * 12 + 4]).to_equal(BLUE)
expect(result.pixels[5 * 12 + 5]).to_equal(0xFF7F7FFFu32)
engine.shutdown()
```

</details>

#### preserves 500 and inactive 930 embedding opacity while sampling the painted parent

- var engine = Engine2D create with backend
- draw ir no rect
- draw ir style prop
- draw ir style prop
- draw ir style prop
- draw ir style prop
- draw ir style prop
- draw ir style prop
- draw ir style prop
- draw ir style prop
- draw ir style prop
- engine clear
- draw ir embedding config
   - Expected: half_result.cpu_composited_material_count equals `1`
   - Expected: half_result.pixels[5 * 12 + 5] equals `0xFF3F3FFFu32`
- engine clear
- draw ir embedding config
   - Expected: inactive_result.cpu_composited_material_count equals `1`
   - Expected: inactive_result.pixels[5 * 12 + 5] equals `0xFF7575FFu32`
- engine shutdown


<details>
<summary>Executable SSpec</summary>

Runnable source: 32 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var engine = Engine2D.create_with_backend(12, 12, "cpu")
val command = draw_ir_box_with_style(
    "alpha-parent-glass", 0, 0, 4, 4, 0xFF1F1F21u32,
    draw_ir_no_rect(), draw_ir_no_rect(), draw_ir_no_rect(), draw_ir_no_rect(),
    [
        draw_ir_style_prop("wm-material-request", "window-surface-glass"),
        draw_ir_style_prop("wm-material-surface-alpha-milli", "500"),
        draw_ir_style_prop("background-color", "4294967295"),
        draw_ir_style_prop("background-image", "none"),
        draw_ir_style_prop("border-radius", "1"),
        draw_ir_style_prop("backdrop-filter", "blur(0px) saturate(100%)"),
        draw_ir_style_prop("backdrop-filter-realized-blur-radius-px", "0"),
        draw_ir_style_prop("backdrop-filter-realized-saturation-milli", "1000"),
        draw_ir_style_prop("backdrop-filter-capability", "engine2d-composited-glass-material-v1")
    ]
)

engine.clear(BLUE)
val half = draw_ir_batch("alpha-parent-half", DRAW_IR_BACKEND_CPU,
    draw_ir_embedding_config("surf", "win", 4, 4, 4, 4, 1, 500, true), [command])
val half_result = engine2d_draw_ir_adv_batch(engine, half, false)
expect(half_result.cpu_composited_material_count).to_equal(1)
expect(half_result.pixels[5 * 12 + 5]).to_equal(0xFF3F3FFFu32)

engine.clear(BLUE)
val inactive = draw_ir_batch("alpha-parent-inactive", DRAW_IR_BACKEND_CPU,
    draw_ir_embedding_config("surf", "win", 4, 4, 4, 4, 1, 930, true), [command])
val inactive_result = engine2d_draw_ir_adv_batch(engine, inactive, false)
expect(inactive_result.cpu_composited_material_count).to_equal(1)
expect(inactive_result.pixels[5 * 12 + 5]).to_equal(0xFF7575FFu32)

engine.shutdown()
```

</details>

#### aggregates glass receipts from direct and parent-sampling embedded batches

- var engine = Engine2D create with backend
- engine clear
- draw ir no rect
- draw ir style prop
- draw ir style prop
- draw ir style prop
- draw ir style prop
- draw ir style prop
- draw ir style prop
- draw ir style prop
- draw ir style prop
- draw ir style prop
- draw ir no rect
- draw ir style prop
- draw ir style prop
- draw ir style prop
- draw ir style prop
- draw ir style prop
- draw ir style prop
- draw ir style prop
- draw ir style prop
- draw ir style prop
   - Expected: result.rendered_command_count equals `2`
   - Expected: result.skipped_command_count equals `0`
   - Expected: result.cpu_composited_material_count equals `2`
   - Expected: result.glass_execution_target equals `cpu-scalar-glass-v1`
   - Expected: result.pixels[1 * 12 + 1] equals `0xFF7F7F7Fu32`
   - Expected: result.pixels[7 * 12 + 7] equals `0xFF7F7F7Fu32`
- engine shutdown


<details>
<summary>Executable SSpec</summary>

Runnable source: 45 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var engine = Engine2D.create_with_backend(12, 12, "cpu")
engine.clear(BG)
val direct_glass = draw_ir_box_with_style(
    "direct-glass", 0, 0, 4, 4, 0xFF1F1F21u32,
    draw_ir_no_rect(), draw_ir_no_rect(), draw_ir_no_rect(), draw_ir_no_rect(),
    [
        draw_ir_style_prop("wm-material-request", "window-surface-glass"),
        draw_ir_style_prop("wm-material-surface-alpha-milli", "500"),
        draw_ir_style_prop("background-color", "4294967295"),
        draw_ir_style_prop("background-image", "none"),
        draw_ir_style_prop("border-radius", "1"),
        draw_ir_style_prop("backdrop-filter", "blur(0px) saturate(100%)"),
        draw_ir_style_prop("backdrop-filter-realized-blur-radius-px", "0"),
        draw_ir_style_prop("backdrop-filter-realized-saturation-milli", "1000"),
        draw_ir_style_prop("backdrop-filter-capability", "engine2d-cpu-composited-material-v1")
    ]
)
val embedded_glass = draw_ir_box_with_style(
    "embedded-glass", 0, 0, 4, 4, 0xFF1F1F21u32,
    draw_ir_no_rect(), draw_ir_no_rect(), draw_ir_no_rect(), draw_ir_no_rect(),
    [
        draw_ir_style_prop("wm-material-request", "window-surface-glass"),
        draw_ir_style_prop("wm-material-surface-alpha-milli", "500"),
        draw_ir_style_prop("background-color", "4294967295"),
        draw_ir_style_prop("background-image", "none"),
        draw_ir_style_prop("border-radius", "1"),
        draw_ir_style_prop("backdrop-filter", "blur(0px) saturate(100%)"),
        draw_ir_style_prop("backdrop-filter-realized-blur-radius-px", "0"),
        draw_ir_style_prop("backdrop-filter-realized-saturation-milli", "1000"),
        draw_ir_style_prop("backdrop-filter-capability", "engine2d-cpu-composited-material-v1")
    ]
)
val direct = draw_ir_batch("direct-glass", DRAW_IR_BACKEND_CPU, draw_ir_embedding_config("desktop", "root", 0, 0, 12, 12, 0, 1000, false), [direct_glass])
val embedded = draw_ir_batch("embedded-glass", DRAW_IR_BACKEND_CPU, draw_ir_embedding_config("surf", "win", 6, 6, 4, 4, 1, 1000, true), [embedded_glass])
val composition = draw_ir_composition("glass-receipts", "scene", DRAW_IR_BACKEND_CPU, [direct, embedded])

val result = engine2d_draw_ir_adv_composition(engine, composition, false)

expect(result.rendered_command_count).to_equal(2)
expect(result.skipped_command_count).to_equal(0)
expect(result.cpu_composited_material_count).to_equal(2)
expect(result.glass_execution_target).to_equal("cpu-scalar-glass-v1")
expect(result.pixels[1 * 12 + 1]).to_equal(0xFF7F7F7Fu32)
expect(result.pixels[7 * 12 + 7]).to_equal(0xFF7F7F7Fu32)
engine.shutdown()
```

</details>

#### executes ordered body and title materials for a concrete Metal request and classifies CPU fallback

- var engine = Engine2D create with backend
- engine clear
- draw ir no rect
- draw ir style prop
- draw ir style prop
- draw ir style prop
- draw ir style prop
- draw ir style prop
- draw ir style prop
- draw ir style prop
- draw ir style prop
- draw ir style prop
- draw ir style prop
- draw ir style prop
- draw ir no rect
- draw ir style prop
- draw ir style prop
- draw ir style prop
- draw ir style prop
- draw ir style prop
- draw ir style prop
- draw ir style prop
- draw ir style prop
- draw ir style prop
- draw ir style prop
- draw ir style prop
- draw ir embedding config
   - Expected: result.rendered_command_count equals `2`
   - Expected: result.cpu_composited_material_count equals `2`
   - Expected: result.metal_device_glass_material_count equals `0`
   - Expected: result.metal_device_glass_requested_count equals `2`
   - Expected: result.metal_device_glass_unfulfilled_count equals `2`
   - Expected: result.metal_device_glass_receipts.len() equals `2`
   - Expected: result.metal_device_glass_receipts[0].material_id equals `metal-body`
   - Expected: result.metal_device_glass_receipts[0].fulfilled is false
   - Expected: result.metal_device_glass_receipts[0].readback_source equals `cpu_mirror`
   - Expected: result.metal_device_glass_receipts[0].readback_checksum equals `result.readback_checksum`
   - Expected: result.metal_device_glass_receipts[1].material_id equals `metal-title`
   - Expected: result.metal_device_glass_receipts[1].fulfilled is false
   - Expected: result.glass_execution_target equals `cpu-scalar-glass-v1`
   - Expected: result.selected_backend equals `DRAW_IR_BACKEND_CPU`
   - Expected: result.fallback_reason equals `metal glass material used cpu fallback`
   - Expected: result.readback_source equals `cpu_mirror`
   - Expected: result.glass_backend_handle equals `0`
   - Expected: result.glass_device_identity equals `0`
   - Expected: result.pixels[2 * 12 + 2] equals `RED`
   - Expected: result.pixels[5 * 12 + 2] equals `GREEN`
- engine shutdown


<details>
<summary>Executable SSpec</summary>

Runnable source: 71 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var engine = Engine2D.create_with_backend(12, 12, "cpu")
engine.clear(BG)
val body = draw_ir_box_with_style(
    "metal-body", 0, 0, 6, 6, GREEN,
    draw_ir_no_rect(), draw_ir_no_rect(), draw_ir_no_rect(), draw_ir_no_rect(),
    [
        draw_ir_style_prop("wm-material-request", "window-surface-glass"),
        draw_ir_style_prop("wm-material-surface-alpha-milli", "1000"),
        draw_ir_style_prop("background-color", GREEN.to_string()),
        draw_ir_style_prop("background-image", "none"),
        draw_ir_style_prop("border-radius", "0"),
        draw_ir_style_prop("backdrop-filter", "blur(0px) saturate(100%)"),
        draw_ir_style_prop("backdrop-filter-realized-blur-radius-px", "0"),
        draw_ir_style_prop("backdrop-filter-realized-saturation-milli", "1000"),
        draw_ir_style_prop("backdrop-filter-capability", "engine2d-composited-glass-material-v1"),
        draw_ir_style_prop("backdrop-filter-requested-target", "metal-device-glass-v1"),
        draw_ir_style_prop("backdrop-filter-fallback-target", "cpu-scalar-glass-v1")
    ]
)
val title = draw_ir_box_with_style(
    "metal-title", 0, 0, 6, 2, RED,
    draw_ir_no_rect(), draw_ir_no_rect(), draw_ir_no_rect(), draw_ir_no_rect(),
    [
        draw_ir_style_prop("wm-material-request", "window-surface-glass"),
        draw_ir_style_prop("wm-material-surface-alpha-milli", "1000"),
        draw_ir_style_prop("background-color", RED.to_string()),
        draw_ir_style_prop("background-image", "none"),
        draw_ir_style_prop("border-radius", "0"),
        draw_ir_style_prop("backdrop-filter", "blur(0px) saturate(100%)"),
        draw_ir_style_prop("backdrop-filter-realized-blur-radius-px", "0"),
        draw_ir_style_prop("backdrop-filter-realized-saturation-milli", "1000"),
        draw_ir_style_prop("backdrop-filter-capability", "engine2d-composited-glass-material-v1"),
        draw_ir_style_prop("backdrop-filter-requested-target", "metal-device-glass-v1"),
        draw_ir_style_prop("backdrop-filter-fallback-target", "cpu-scalar-glass-v1")
    ]
)
val batch = draw_ir_batch(
    "metal-window", "metal",
    draw_ir_embedding_config("surface", "window", 2, 2, 6, 6, 1, 1000, true),
    [body, title]
)
val composition = draw_ir_composition(
    "metal-window", "scene", "metal", [batch])

val result = engine2d_draw_ir_adv_composition(
    engine, composition, true)

expect(result.rendered_command_count).to_equal(2)
expect(result.cpu_composited_material_count).to_equal(2)
expect(result.metal_device_glass_material_count).to_equal(0)
expect(result.metal_device_glass_requested_count).to_equal(2)
expect(result.metal_device_glass_unfulfilled_count).to_equal(2)
# Per-material receipts preserve z-order.  This prevents a later
# receipt from overwriting the first failed/mismatched material.
expect(result.metal_device_glass_receipts.len()).to_equal(2)
expect(result.metal_device_glass_receipts[0].material_id).to_equal("metal-body")
expect(result.metal_device_glass_receipts[0].fulfilled).to_equal(false)
expect(result.metal_device_glass_receipts[0].readback_source).to_equal("cpu_mirror")
expect(result.metal_device_glass_receipts[0].readback_checksum).to_equal(result.readback_checksum)
expect(result.metal_device_glass_receipts[1].material_id).to_equal("metal-title")
expect(result.metal_device_glass_receipts[1].fulfilled).to_equal(false)
expect(result.glass_execution_target).to_equal("cpu-scalar-glass-v1")
expect(result.selected_backend).to_equal(DRAW_IR_BACKEND_CPU)
expect(result.fallback_required).to_be(true)
expect(result.fallback_reason).to_equal("metal glass material used cpu fallback")
expect(result.readback_source).to_equal("cpu_mirror")
expect(result.glass_backend_handle).to_equal(0)
expect(result.glass_device_identity).to_equal(0)
expect(result.pixels[2 * 12 + 2]).to_equal(RED)
expect(result.pixels[5 * 12 + 2]).to_equal(GREEN)
engine.shutdown()
```

</details>

#### does not receipt a malformed glass command that uses its solid fallback

- var engine = Engine2D create with backend
- engine clear
- draw ir no rect
- draw ir style prop
- draw ir style prop
- draw ir style prop
- draw ir style prop
- draw ir style prop
- draw ir style prop
   - Expected: result.rendered_command_count equals `1`
   - Expected: result.skipped_command_count equals `0`
   - Expected: result.cpu_composited_material_count equals `0`
   - Expected: result.pixels[5 * 12 + 5] equals `fallback`
- engine shutdown


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var engine = Engine2D.create_with_backend(12, 12, "cpu")
engine.clear(BG)
val fallback: u32 = 0xFF1F1F21u32
val command = draw_ir_box_with_style(
    "malformed-glass", 4, 4, 4, 4, fallback,
    draw_ir_no_rect(), draw_ir_no_rect(), draw_ir_no_rect(), draw_ir_no_rect(),
    [
        draw_ir_style_prop("background-color", "4294967295"),
        draw_ir_style_prop("background-image", "none"),
        draw_ir_style_prop("border-radius", "0"),
        draw_ir_style_prop("backdrop-filter", "blur(0px) saturate(100%)"),
        draw_ir_style_prop("backdrop-filter-realized-blur-radius-px", "0"),
        draw_ir_style_prop("backdrop-filter-capability", "engine2d-cpu-composited-material-v1")
    ]
)
val batch = draw_ir_batch("malformed-glass", DRAW_IR_BACKEND_CPU, draw_ir_embedding_config("surf", "win", 0, 0, 12, 12, 1, 1000, false), [command])

val result = engine2d_draw_ir_adv_batch(engine, batch, false)

expect(result.rendered_command_count).to_equal(1)
expect(result.skipped_command_count).to_equal(0)
expect(result.cpu_composited_material_count).to_equal(0)
expect(result.pixels[5 * 12 + 5]).to_equal(fallback)
engine.shutdown()
```

</details>

#### fails closed when an explicit Metal glass request has malformed metadata

- var engine = Engine2D create with backend
- engine clear
- draw ir no rect
- draw ir style prop
- draw ir style prop
- draw ir style prop
- draw ir style prop
- draw ir style prop
- draw ir embedding config
   - Expected: result.rendered_command_count equals `1`
   - Expected: result.metal_device_glass_requested_count equals `1`
   - Expected: result.metal_device_glass_material_count equals `0`
   - Expected: result.metal_device_glass_unfulfilled_count equals `1`
   - Expected: result.metal_device_glass_receipts.len() equals `1`
   - Expected: result.metal_device_glass_receipts[0].material_id equals `metal-metadata-missing`
   - Expected: result.metal_device_glass_receipts[0].fulfilled is false
   - Expected: result.fallback_reason equals `metal glass material device receipt missing`
- engine shutdown


<details>
<summary>Executable SSpec</summary>

Runnable source: 32 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var engine = Engine2D.create_with_backend(12, 12, "cpu")
engine.clear(BG)
val command = draw_ir_box_with_style(
    "metal-metadata-missing", 2, 2, 4, 4, GREEN,
    draw_ir_no_rect(), draw_ir_no_rect(), draw_ir_no_rect(), draw_ir_no_rect(),
    [
        draw_ir_style_prop("wm-material-request", "window-surface-glass"),
        draw_ir_style_prop("background-color", GREEN.to_string()),
        draw_ir_style_prop("border-radius", "0"),
        # Deliberately no exact composited capability or realized
        # metadata: a solid fallback must not masquerade as Metal.
        draw_ir_style_prop("backdrop-filter", "blur(30px) saturate(170%)"),
        draw_ir_style_prop("backdrop-filter-requested-target", "metal-device-glass-v1")
    ]
)
val batch = draw_ir_batch("metal-metadata-missing", "metal",
    draw_ir_embedding_config("surface", "window", 2, 2, 4, 4, 1, 1000, true), [command])
val composition = draw_ir_composition(
    "metal-metadata-missing", "scene", "metal", [batch])

val result = engine2d_draw_ir_adv_composition(engine, composition, true)

expect(result.rendered_command_count).to_equal(1)
expect(result.metal_device_glass_requested_count).to_equal(1)
expect(result.metal_device_glass_material_count).to_equal(0)
expect(result.metal_device_glass_unfulfilled_count).to_equal(1)
expect(result.metal_device_glass_receipts.len()).to_equal(1)
expect(result.metal_device_glass_receipts[0].material_id).to_equal("metal-metadata-missing")
expect(result.metal_device_glass_receipts[0].fulfilled).to_equal(false)
expect(result.fallback_required).to_be(true)
expect(result.fallback_reason).to_equal("metal glass material device receipt missing")
engine.shutdown()
```

</details>

#### requires an exact glass capability token for execution receipts

- var engine = Engine2D create with backend
- engine clear
- draw ir no rect
- draw ir style prop
- draw ir style prop
- draw ir style prop
- draw ir style prop
- draw ir style prop
- draw ir style prop
- draw ir style prop
   - Expected: result.cpu_composited_material_count equals `0`
   - Expected: result.pixels[5 * 12 + 5] equals `fallback`
- engine shutdown


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var engine = Engine2D.create_with_backend(12, 12, "cpu")
engine.clear(BG)
val fallback: u32 = 0xFF1F1F21u32
val command = draw_ir_box_with_style(
    "nonexact-glass", 4, 4, 4, 4, fallback,
    draw_ir_no_rect(), draw_ir_no_rect(), draw_ir_no_rect(), draw_ir_no_rect(),
    [
        draw_ir_style_prop("background-color", "4294967295"),
        draw_ir_style_prop("background-image", "none"),
        draw_ir_style_prop("border-radius", "0"),
        draw_ir_style_prop("backdrop-filter", "blur(0px) saturate(100%)"),
        draw_ir_style_prop("backdrop-filter-realized-blur-radius-px", "0"),
        draw_ir_style_prop("backdrop-filter-realized-saturation-milli", "1000"),
        draw_ir_style_prop("backdrop-filter-capability", "engine2d-cpu-composited-material-v1-extra")
    ]
)
val batch = draw_ir_batch("nonexact-glass", DRAW_IR_BACKEND_CPU, draw_ir_embedding_config("surf", "win", 0, 0, 12, 12, 1, 1000, false), [command])

val result = engine2d_draw_ir_adv_batch(engine, batch, false)

expect(result.cpu_composited_material_count).to_equal(0)
expect(result.pixels[5 * 12 + 5]).to_equal(fallback)
engine.shutdown()
```

</details>

#### rasterizes the explicit solid WM fallback with rounded corners

- var engine = Engine2D create with backend
- engine clear
- draw ir no rect
- [draw ir style prop
   - Expected: result.rendered_command_count equals `1`
   - Expected: result.pixels[4 * 32 + 4] equals `BG`
   - Expected: result.pixels[12 * 32 + 12] equals `fallback`
- engine shutdown


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var engine = Engine2D.create_with_backend(32, 32, "cpu")
engine.clear(BG)
val fallback: u32 = 0xff1f1f21u32
val command = draw_ir_box_with_style(
    "wm-body-fallback", 4, 4, 16, 16, fallback,
    draw_ir_no_rect(), draw_ir_no_rect(), draw_ir_no_rect(), draw_ir_no_rect(),
    [draw_ir_style_prop("border-radius", "4")]
)
val batch = draw_ir_batch("wm-material-fallback", DRAW_IR_BACKEND_CPU, draw_ir_embedding_config("surf", "win", 0, 0, 32, 32, 1, 1000, false), [command])

val result = engine2d_draw_ir_adv_batch(engine, batch, false)

expect(result.rendered_command_count).to_equal(1)
expect(result.pixels[4 * 32 + 4]).to_equal(BG)
expect(result.pixels[12 * 32 + 12]).to_equal(fallback)
engine.shutdown()
```

</details>

#### reports unsupported Draw IR commands without rendering them

- var engine = Engine2D create with backend
- engine clear
   - Expected: result.rendered_command_count equals `0`
   - Expected: result.skipped_command_count equals `1`
   - Expected: result.pixels[1 * 16 + 1] equals `BG`
- engine shutdown


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var engine = Engine2D.create_with_backend(16, 16, "cpu")
engine.clear(BG)
val unsupported = DrawIrCommand(kind: "future-path", component_id: "path", x: 1, y: 1, width: 5, height: 5, color: RED, text_value: "", advance_widths: [], border_rect: draw_ir_no_rect(), content_rect: draw_ir_no_rect(), hit_rect: draw_ir_no_rect(), clip_rect: draw_ir_no_rect(), computed_style: [], edge: nil, parent_id: "", image_uri: "", points: [], glyph_run: draw_ir_empty_glyph_run_payload())
val batch = draw_ir_batch("unsupported", DRAW_IR_BACKEND_GPU, draw_ir_embedding_config("surf", "win", 0, 0, 16, 16, 1, 1000, false), [unsupported])

val result = engine2d_draw_ir_adv_batch(engine, batch, false)

expect(result.rendered_command_count).to_equal(0)
expect(result.skipped_command_count).to_equal(1)
expect(result.pixels[1 * 16 + 1]).to_equal(BG)
engine.shutdown()
```

</details>

#### renders supported commands while reporting unsupported siblings

- var engine = Engine2D create with backend
- engine clear
   - Expected: result.rendered_command_count equals `1`
   - Expected: result.skipped_command_count equals `1`
   - Expected: result.fallback_required is true
   - Expected: result.pixels[0] equals `RED`
- engine shutdown


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var engine = Engine2D.create_with_backend(16, 16, "cpu")
engine.clear(BG)
val unsupported = DrawIrCommand(kind: "future-path", component_id: "path", x: 1, y: 1, width: 5, height: 5, color: RED, text_value: "", advance_widths: [], border_rect: draw_ir_no_rect(), content_rect: draw_ir_no_rect(), hit_rect: draw_ir_no_rect(), clip_rect: draw_ir_no_rect(), computed_style: [], edge: nil, parent_id: "", image_uri: "", points: [], glyph_run: draw_ir_empty_glyph_run_payload())
val batch = draw_ir_batch("transactional", DRAW_IR_BACKEND_GPU, draw_ir_embedding_config("surf", "win", 0, 0, 16, 16, 1, 1000, false), [draw_ir_rect("would-paint", 0, 0, 16, 16, RED), unsupported])
val composition = draw_ir_composition("transactional", "scene", DRAW_IR_BACKEND_GPU, [batch])

val result = engine2d_draw_ir_adv_composition(engine, composition, false)

expect(result.rendered_command_count).to_equal(1)
expect(result.skipped_command_count).to_equal(1)
expect(result.fallback_required).to_equal(true)
expect(result.fallback_reason).to_contain("future-path")
expect(result.pixels[0]).to_equal(RED)
engine.shutdown()
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 33 |
| Active scenarios | 33 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Plan:** `doc/03_plan/ui/ui_test/ui_test_sgtti_plan.md`
- **Design:** `doc/04_architecture/ui/ui_test_architecture.md`
- **Research:** `doc/01_research/ui/draw_ir/draw_io_sdn_draw_ir.md`


</details>

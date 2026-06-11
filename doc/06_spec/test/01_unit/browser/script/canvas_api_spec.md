# Canvas API Spec

> Unit tests for the Simple browser engine Canvas 2D API.

<!-- sdn-diagram:id=canvas_api_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=canvas_api_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

canvas_api_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=canvas_api_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 71 | 71 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Canvas API Spec

Unit tests for the Simple browser engine Canvas 2D API.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/01_unit/browser/script/canvas_api_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Unit tests for the Simple browser engine Canvas 2D API.

## Scenarios

### Canvas API - Context Creation

#### creates a context with correct dimensions

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ctx = canvas_create(800, 600)
expect(ctx.width).to_equal(800)
```

</details>

#### context has correct height

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ctx = canvas_create(800, 600)
expect(ctx.height).to_equal(600)
```

</details>

#### context starts with default fill color

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ctx = canvas_create(100, 100)
expect(ctx.fill_color).to_equal("#000000")
```

</details>

### Canvas API - Shape Drawing

#### fillRect adds a command

1. var ctx = canvas create
2. ctx fill rect
   - Expected: cmds.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ctx = canvas_create(100, 100)
ctx.fill_rect(10.0, 20.0, 50.0, 30.0)
val cmds = canvas_get_commands(ctx)
expect(cmds.len()).to_equal(1)
```

</details>

#### fillRect command contains coordinates

1. var ctx = canvas create
2. ctx fill rect


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ctx = canvas_create(100, 100)
ctx.fill_rect(10.0, 20.0, 50.0, 30.0)
val cmds = canvas_get_commands(ctx)
expect(cmds[0]).to_contain("fillRect")
```

</details>

#### strokeRect adds a command

1. var ctx = canvas create
2. ctx stroke rect


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ctx = canvas_create(100, 100)
ctx.stroke_rect(0.0, 0.0, 100.0, 100.0)
val cmds = canvas_get_commands(ctx)
expect(cmds[0]).to_contain("strokeRect")
```

</details>

#### clearRect adds a command

1. var ctx = canvas create
2. ctx clear rect


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ctx = canvas_create(100, 100)
ctx.clear_rect(0.0, 0.0, 100.0, 100.0)
val cmds = canvas_get_commands(ctx)
expect(cmds[0]).to_contain("clearRect")
```

</details>

### Canvas API - Text Drawing

#### fillText adds a command

1. var ctx = canvas create
2. ctx fill text


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ctx = canvas_create(100, 100)
ctx.fill_text("Hello", 10.0, 20.0)
val cmds = canvas_get_commands(ctx)
expect(cmds[0]).to_contain("fillText")
```

</details>

### Canvas API - Path Operations

#### path operations accumulate commands

1. var ctx = canvas create
2. ctx begin path
3. ctx move to
4. ctx line to
5. ctx close path
6. ctx stroke
   - Expected: cmds.len() equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ctx = canvas_create(100, 100)
ctx.begin_path()
ctx.move_to(0.0, 0.0)
ctx.line_to(100.0, 100.0)
ctx.close_path()
ctx.stroke()
val cmds = canvas_get_commands(ctx)
expect(cmds.len()).to_equal(5)
```

</details>

#### records bezier and quadratic curve path commands

1. var ctx = canvas create
2. ctx begin path
3. ctx move to
4. ctx bezier curve to
5. ctx quadratic curve to
6. ctx close path
   - Expected: cmds.len() equals `5`
   - Expected: cmds[2] equals `bezierCurveTo 3 4 5 6 7 8`
   - Expected: cmds[3] equals `quadraticCurveTo 9 10 11 12`
   - Expected: cmds[4] equals `closePath`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ctx = canvas_create(100, 100)
ctx.begin_path()
ctx.move_to(1.0, 2.0)
ctx.bezier_curve_to(3.0, 4.0, 5.0, 6.0, 7.0, 8.0)
ctx.quadratic_curve_to(9.0, 10.0, 11.0, 12.0)
ctx.close_path()
val cmds = canvas_get_commands(ctx)
expect(cmds.len()).to_equal(5)
expect(cmds[2]).to_equal("bezierCurveTo 3 4 5 6 7 8")
expect(cmds[3]).to_equal("quadraticCurveTo 9 10 11 12")
expect(cmds[4]).to_equal("closePath")
```

</details>

#### records ellipse path metadata through context method

1. var ctx = canvas create
2. ctx ellipse
   - Expected: cmds[0] equals `ellipse 10 20 30 40 0.5 1 2 true`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ctx = canvas_create(100, 100)
ctx.ellipse(10.0, 20.0, 30.0, 40.0, 0.5, 1.0, 2.0, true)
val cmds = canvas_get_commands(ctx)
expect(cmds[0]).to_equal("ellipse 10 20 30 40 0.5 1 2 true")
```

</details>

#### records arc anticlockwise metadata through context method

1. var ctx = canvas create
2. ctx arc with direction
   - Expected: cmds[0] equals `arc 10 20 30 0 3.14 true`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ctx = canvas_create(100, 100)
ctx.arc_with_direction(10.0, 20.0, 30.0, 0.0, 3.14, true)
val cmds = canvas_get_commands(ctx)
expect(cmds[0]).to_equal("arc 10 20 30 0 3.14 true")
```

</details>

#### records arc anticlockwise metadata through canvas helper

1. var ctx = canvas create
2. ctx = canvas arc with direction
   - Expected: cmds[0] equals `arc 11 22 33 1 4 false`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ctx = canvas_create(100, 100)
ctx = canvas_arc_with_direction(ctx, 11.0, 22.0, 33.0, 1.0, 4.0, false)
val cmds = canvas_get_commands(ctx)
expect(cmds[0]).to_equal("arc 11 22 33 1 4 false")
```

</details>

#### records ellipse path metadata through canvas helper

1. var ctx = canvas create
2. ctx = canvas ellipse
   - Expected: cmds[0] equals `ellipse 11 22 33 44 0.25 0 6.28 false`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ctx = canvas_create(100, 100)
ctx = canvas_ellipse(ctx, 11.0, 22.0, 33.0, 44.0, 0.25, 0.0, 6.28, false)
val cmds = canvas_get_commands(ctx)
expect(cmds[0]).to_equal("ellipse 11 22 33 44 0.25 0 6.28 false")
```

</details>

### Canvas API - Image Drawing

#### records drawImage destination metadata

1. var ctx = canvas create
2. ctx = canvas draw image
   - Expected: cmds[0] equals `drawImage sprite.png 10 20 30 40`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ctx = canvas_create(100, 100)
ctx = canvas_draw_image(ctx, "sprite.png", 10.0, 20.0, 30.0, 40.0)
val cmds = canvas_get_commands(ctx)
expect(cmds[0]).to_equal("drawImage sprite.png 10 20 30 40")
```

</details>

#### records drawImage source and destination rectangle metadata

1. var ctx = canvas create
2. ctx = canvas draw image region
   - Expected: cmds[0] equals `drawImageRegion atlas.png 1 2 16 18 20 22 32 36`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ctx = canvas_create(100, 100)
ctx = canvas_draw_image_region(ctx, "atlas.png", 1.0, 2.0, 16.0, 18.0, 20.0, 22.0, 32.0, 36.0)
val cmds = canvas_get_commands(ctx)
expect(cmds[0]).to_equal("drawImageRegion atlas.png 1 2 16 18 20 22 32 36")
```

</details>

### Canvas API - Style

#### changes fill style

1. var ctx = canvas create
2. ctx set fill style
   - Expected: ctx.fill_color equals `#ff0000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ctx = canvas_create(100, 100)
ctx.set_fill_style("#ff0000")
expect(ctx.fill_color).to_equal("#ff0000")
```

</details>

#### changes stroke style

1. var ctx = canvas create
2. ctx set stroke style
   - Expected: ctx.stroke_color equals `#00ff00`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ctx = canvas_create(100, 100)
ctx.set_stroke_style("#00ff00")
expect(ctx.stroke_color).to_equal("#00ff00")
```

</details>

#### changes line width

1. var ctx = canvas create
2. ctx set line width
   - Expected: ctx.line_width equals `3.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ctx = canvas_create(100, 100)
ctx.set_line_width(3.0)
expect(ctx.line_width).to_equal(3.0)
```

</details>

### Canvas API - State Save/Restore

#### save and restore preserves fill color

1. var ctx = canvas create
2. ctx set fill style
3. ctx save
4. ctx set fill style
5. ctx restore
   - Expected: ctx.fill_color equals `#ff0000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ctx = canvas_create(100, 100)
ctx.set_fill_style("#ff0000")
ctx.save()
ctx.set_fill_style("#0000ff")
ctx.restore()
expect(ctx.fill_color).to_equal("#ff0000")
```

</details>

### Canvas API - Transforms

#### translate adds a command

1. var ctx = canvas create
2. ctx translate


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ctx = canvas_create(100, 100)
ctx.translate(50.0, 50.0)
val cmds = canvas_get_commands(ctx)
expect(cmds[0]).to_contain("translate")
```

</details>

#### rotate adds a command

1. var ctx = canvas create
2. ctx rotate


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ctx = canvas_create(100, 100)
ctx.rotate(1.57)
val cmds = canvas_get_commands(ctx)
expect(cmds[0]).to_contain("rotate")
```

</details>

### Canvas API - Text Measurement

#### measures text width

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ctx = canvas_create(100, 100)
val w = canvas_measure_text(ctx, "Hello")
expect(w > 0.0).to_equal(true)
```

</details>

### Canvas API - Image Data

#### returns transparent black pixels from a new canvas

1. var ctx = canvas create
   - Expected: image.width equals `1`
   - Expected: image.height equals `1`
   - Expected: image.data.len() equals `4`
   - Expected: image.data[3] equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ctx = canvas_create(2, 2)
val image = canvas_get_image_data(ctx, 0, 0, 1, 1)
expect(image.width).to_equal(1)
expect(image.height).to_equal(1)
expect(image.data.len()).to_equal(4)
expect(image.data[3]).to_equal(0)
```

</details>

#### copies putImageData pixels into getImageData output

1. var ctx = canvas create
2. ctx = canvas put image data
   - Expected: copied.data[0] equals `255`
   - Expected: copied.data[1] equals `10`
   - Expected: copied.data[2] equals `20`
   - Expected: copied.data[3] equals `255`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ctx = canvas_create(2, 2)
val image = CanvasImageData(width: 1, height: 1, data: [255, 10, 20, 255])
ctx = canvas_put_image_data(ctx, image, 1, 1)
val copied = canvas_get_image_data(ctx, 1, 1, 1, 1)
expect(copied.data[0]).to_equal(255)
expect(copied.data[1]).to_equal(10)
expect(copied.data[2]).to_equal(20)
expect(copied.data[3]).to_equal(255)
```

</details>

#### fills out-of-bounds getImageData pixels with zeros

1. var ctx = canvas create
2. ctx put image data
   - Expected: copied.data[0] equals `0`
   - Expected: copied.data[3] equals `0`
   - Expected: copied.data[4] equals `7`
   - Expected: copied.data[7] equals `255`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ctx = canvas_create(1, 1)
val image = CanvasImageData(width: 1, height: 1, data: [7, 8, 9, 255])
ctx.put_image_data(image, 0, 0)
val copied = canvas_get_image_data(ctx, -1, 0, 2, 1)
expect(copied.data[0]).to_equal(0)
expect(copied.data[3]).to_equal(0)
expect(copied.data[4]).to_equal(7)
expect(copied.data[7]).to_equal(255)
```

</details>

### Canvas API - WebGPU Context

#### recognizes webgpu context kind

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(canvas_get_context_kind("webgpu")).to_equal("webgpu")
```

</details>

#### recognizes webgl context kind

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(canvas_get_context_kind("webgl")).to_equal("webgl")
```

</details>

#### recognizes webgl2 context kind

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(canvas_get_context_kind("WebGL2")).to_equal("webgl2")
```

</details>

#### creates WebGL canvas contexts

1. var ctx: CanvasWebGLContext = canvas get context webgl
   - Expected: ctx.context_type equals `webgl`
   - Expected: ctx.gl.version equals `1`
   - Expected: ctx.is_available() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ctx: CanvasWebGLContext = canvas_get_context_webgl(320, 240)
expect(ctx.context_type).to_equal("webgl")
expect(ctx.gl.version).to_equal(1)
expect(ctx.is_available()).to_equal(true)
```

</details>

#### creates WebGL2 canvas contexts

1. var ctx: CanvasWebGLContext = canvas get context webgl2
   - Expected: ctx.context_type equals `webgl2`
   - Expected: ctx.gl.version equals `2`
   - Expected: ctx.is_available() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ctx: CanvasWebGLContext = canvas_get_context_webgl2(320, 240)
expect(ctx.context_type).to_equal("webgl2")
expect(ctx.gl.version).to_equal(2)
expect(ctx.is_available()).to_equal(true)
```

</details>

#### records WebGL commands through canvas bridge helpers

1. var ctx: CanvasWebGLContext = canvas get context webgl
2. ctx = canvas webgl viewport
3. ctx = canvas webgl clear color
4. ctx = canvas webgl clear depth
5. ctx = canvas webgl depth range
6. ctx = canvas webgl clear stencil
7. ctx = canvas webgl clear
8. ctx = canvas webgl flush
9. ctx = canvas webgl finish
   - Expected: ctx.gl.render_commands.len() equals `8`
   - Expected: ctx.gl.render_commands[6].kind equals `WEBGL_RENDER_COMMAND_FLUSH`
   - Expected: ctx.gl.render_commands[7].kind equals `WEBGL_RENDER_COMMAND_FINISH`
   - Expected: ctx.gl.clear_red equals `1.0`
   - Expected: ctx.gl.clear_green equals `0.0`
   - Expected: canvas_webgl_get_parameter(ctx, CANVAS_WEBGL_VIEWPORT).int_values[2] equals `320`
   - Expected: canvas_webgl_get_parameter(ctx, CANVAS_WEBGL_COLOR_CLEAR_VALUE).float_values[1] equals `0.0`
   - Expected: canvas_webgl_get_parameter(ctx, CANVAS_WEBGL_DEPTH_CLEAR_VALUE).float_value equals `1.0`
   - Expected: canvas_webgl_get_parameter(ctx, CANVAS_WEBGL_DEPTH_RANGE).float_values[0] equals `0.0`
   - Expected: canvas_webgl_get_parameter(ctx, CANVAS_WEBGL_DEPTH_RANGE).float_values[1] equals `1.0`
   - Expected: canvas_webgl_get_parameter(ctx, CANVAS_WEBGL_STENCIL_CLEAR_VALUE).int_value equals `7`


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ctx: CanvasWebGLContext = canvas_get_context_webgl(320, 240)
ctx = canvas_webgl_viewport(ctx, 0, 0, 320, 240)
ctx = canvas_webgl_clear_color(ctx, 1.5, -1.0, 0.5, 1.0)
ctx = canvas_webgl_clear_depth(ctx, 1.5)
ctx = canvas_webgl_depth_range(ctx, -1.0, 2.0)
ctx = canvas_webgl_clear_stencil(ctx, 7)
ctx = canvas_webgl_clear(ctx, CANVAS_WEBGL_COLOR_BUFFER_BIT)
ctx = canvas_webgl_flush(ctx)
ctx = canvas_webgl_finish(ctx)
expect(ctx.gl.render_commands.len()).to_equal(8)
expect(ctx.gl.render_commands[6].kind).to_equal(WEBGL_RENDER_COMMAND_FLUSH)
expect(ctx.gl.render_commands[7].kind).to_equal(WEBGL_RENDER_COMMAND_FINISH)
expect(ctx.gl.clear_red).to_equal(1.0)
expect(ctx.gl.clear_green).to_equal(0.0)
expect(canvas_webgl_get_parameter(ctx, CANVAS_WEBGL_VIEWPORT).int_values[2]).to_equal(320)
expect(canvas_webgl_get_parameter(ctx, CANVAS_WEBGL_COLOR_CLEAR_VALUE).float_values[1]).to_equal(0.0)
expect(canvas_webgl_get_parameter(ctx, CANVAS_WEBGL_DEPTH_CLEAR_VALUE).float_value).to_equal(1.0)
expect(canvas_webgl_get_parameter(ctx, CANVAS_WEBGL_DEPTH_RANGE).float_values[0]).to_equal(0.0)
expect(canvas_webgl_get_parameter(ctx, CANVAS_WEBGL_DEPTH_RANGE).float_values[1]).to_equal(1.0)
expect(canvas_webgl_get_parameter(ctx, CANVAS_WEBGL_STENCIL_CLEAR_VALUE).int_value).to_equal(7)
```

</details>

#### queries WebGL extensions through canvas bridge helpers

1. var ctx: CanvasWebGLContext = canvas get context webgl
   - Expected: ext.valid is true
   - Expected: canvas_webgl_get_supported_extensions(ctx) contains `OES_texture_float`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ctx: CanvasWebGLContext = canvas_get_context_webgl(320, 240)
val ext = canvas_webgl_get_extension(ctx, "OES_texture_float")
expect(ext.valid).to_equal(true)
expect(canvas_webgl_get_supported_extensions(ctx).contains("OES_texture_float")).to_equal(true)
```

</details>

#### bridges WebGL context metadata helpers

1. var ctx: CanvasWebGLContext = canvas get context webgl
   - Expected: canvas_webgl_drawing_buffer_width(ctx) equals `320`
   - Expected: canvas_webgl_drawing_buffer_height(ctx) equals `240`
   - Expected: canvas_webgl_is_context_lost(ctx) is false
2. ctx = canvas webgl lose context
   - Expected: canvas_webgl_is_context_lost(ctx) is true
   - Expected: canvas_webgl_get_error(ctx) equals `CANVAS_WEBGL_CONTEXT_LOST_WEBGL`
3. ctx = canvas webgl restore context
   - Expected: canvas_webgl_is_context_lost(ctx) is false
   - Expected: canvas_webgl_get_error(ctx) equals `CANVAS_WEBGL_NO_ERROR`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ctx: CanvasWebGLContext = canvas_get_context_webgl(320, 240)
expect(canvas_webgl_drawing_buffer_width(ctx)).to_equal(320)
expect(canvas_webgl_drawing_buffer_height(ctx)).to_equal(240)
expect(canvas_webgl_is_context_lost(ctx)).to_equal(false)
ctx = canvas_webgl_lose_context(ctx)
expect(canvas_webgl_is_context_lost(ctx)).to_equal(true)
expect(canvas_webgl_get_error(ctx)).to_equal(CANVAS_WEBGL_CONTEXT_LOST_WEBGL)
ctx = canvas_webgl_restore_context(ctx)
expect(canvas_webgl_is_context_lost(ctx)).to_equal(false)
expect(canvas_webgl_get_error(ctx)).to_equal(CANVAS_WEBGL_NO_ERROR)
```

</details>

#### queries WebGL state through canvas bridge helpers

1. var ctx: CanvasWebGLContext = canvas get context webgl
   - Expected: attrs.valid is true
   - Expected: attrs.depth is true
   - Expected: canvas_webgl_is_enabled(ctx, CANVAS_WEBGL_DITHER) is true
2. ctx = canvas webgl disable
   - Expected: canvas_webgl_is_enabled(ctx, CANVAS_WEBGL_DITHER) is false
3. ctx = canvas webgl enable
4. ctx = canvas webgl line width
5. ctx = canvas webgl hint
6. ctx = canvas webgl front face
7. ctx = canvas webgl cull face
8. ctx = canvas webgl polygon offset
9. ctx = canvas webgl sample coverage
10. ctx = canvas webgl blend color
   - Expected: canvas_webgl_get_parameter(ctx, CANVAS_WEBGL_LINE_WIDTH).float_value equals `2.0`
   - Expected: canvas_webgl_get_parameter(ctx, CANVAS_WEBGL_GENERATE_MIPMAP_HINT).int_value equals `CANVAS_WEBGL_NICEST`
   - Expected: ctx.gl.render_commands[3].kind equals `WEBGL_RENDER_COMMAND_HINT`
   - Expected: canvas_webgl_get_parameter(ctx, CANVAS_WEBGL_FRONT_FACE).int_value equals `CANVAS_WEBGL_CW`
   - Expected: canvas_webgl_get_parameter(ctx, CANVAS_WEBGL_CULL_FACE_MODE).int_value equals `CANVAS_WEBGL_FRONT_AND_BACK`
   - Expected: canvas_webgl_get_parameter(ctx, CANVAS_WEBGL_POLYGON_OFFSET_FILL).bool_value is true
   - Expected: canvas_webgl_get_parameter(ctx, CANVAS_WEBGL_POLYGON_OFFSET_FACTOR).float_value equals `-1.0`
   - Expected: canvas_webgl_get_parameter(ctx, CANVAS_WEBGL_POLYGON_OFFSET_UNITS).float_value equals `3.0`
   - Expected: canvas_webgl_get_parameter(ctx, CANVAS_WEBGL_SAMPLE_COVERAGE).bool_value is false
   - Expected: canvas_webgl_get_parameter(ctx, CANVAS_WEBGL_SAMPLE_COVERAGE_VALUE).float_value equals `1.0`
   - Expected: canvas_webgl_get_parameter(ctx, CANVAS_WEBGL_SAMPLE_COVERAGE_INVERT).bool_value is true
   - Expected: canvas_webgl_get_parameter(ctx, CANVAS_WEBGL_BLEND_COLOR).float_values[2] equals `0.3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 27 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ctx: CanvasWebGLContext = canvas_get_context_webgl(320, 240)
val attrs = canvas_webgl_get_context_attributes(ctx)
expect(attrs.valid).to_equal(true)
expect(attrs.depth).to_equal(true)
expect(canvas_webgl_is_enabled(ctx, CANVAS_WEBGL_DITHER)).to_equal(true)
ctx = canvas_webgl_disable(ctx, CANVAS_WEBGL_DITHER)
expect(canvas_webgl_is_enabled(ctx, CANVAS_WEBGL_DITHER)).to_equal(false)
ctx = canvas_webgl_enable(ctx, CANVAS_WEBGL_POLYGON_OFFSET_FILL)
ctx = canvas_webgl_line_width(ctx, 2.0)
ctx = canvas_webgl_hint(ctx, CANVAS_WEBGL_GENERATE_MIPMAP_HINT, CANVAS_WEBGL_NICEST)
ctx = canvas_webgl_front_face(ctx, CANVAS_WEBGL_CW)
ctx = canvas_webgl_cull_face(ctx, CANVAS_WEBGL_FRONT_AND_BACK)
ctx = canvas_webgl_polygon_offset(ctx, -1.0, 3.0)
ctx = canvas_webgl_sample_coverage(ctx, 1.5, true)
ctx = canvas_webgl_blend_color(ctx, 0.1, 0.2, 0.3, 0.4)
expect(canvas_webgl_get_parameter(ctx, CANVAS_WEBGL_LINE_WIDTH).float_value).to_equal(2.0)
expect(canvas_webgl_get_parameter(ctx, CANVAS_WEBGL_GENERATE_MIPMAP_HINT).int_value).to_equal(CANVAS_WEBGL_NICEST)
expect(ctx.gl.render_commands[3].kind).to_equal(WEBGL_RENDER_COMMAND_HINT)
expect(canvas_webgl_get_parameter(ctx, CANVAS_WEBGL_FRONT_FACE).int_value).to_equal(CANVAS_WEBGL_CW)
expect(canvas_webgl_get_parameter(ctx, CANVAS_WEBGL_CULL_FACE_MODE).int_value).to_equal(CANVAS_WEBGL_FRONT_AND_BACK)
expect(canvas_webgl_get_parameter(ctx, CANVAS_WEBGL_POLYGON_OFFSET_FILL).bool_value).to_equal(true)
expect(canvas_webgl_get_parameter(ctx, CANVAS_WEBGL_POLYGON_OFFSET_FACTOR).float_value).to_equal(-1.0)
expect(canvas_webgl_get_parameter(ctx, CANVAS_WEBGL_POLYGON_OFFSET_UNITS).float_value).to_equal(3.0)
expect(canvas_webgl_get_parameter(ctx, CANVAS_WEBGL_SAMPLE_COVERAGE).bool_value).to_equal(false)
expect(canvas_webgl_get_parameter(ctx, CANVAS_WEBGL_SAMPLE_COVERAGE_VALUE).float_value).to_equal(1.0)
expect(canvas_webgl_get_parameter(ctx, CANVAS_WEBGL_SAMPLE_COVERAGE_INVERT).bool_value).to_equal(true)
expect(canvas_webgl_get_parameter(ctx, CANVAS_WEBGL_BLEND_COLOR).float_values[2]).to_equal(0.3)
```

</details>

#### bridges WebGL depth stencil blend and mask state helpers

1. var ctx: CanvasWebGLContext = canvas get context webgl
2. ctx = canvas webgl scissor
3. ctx = canvas webgl depth func
4. ctx = canvas webgl depth mask
5. ctx = canvas webgl color mask
6. ctx = canvas webgl stencil func
7. ctx = canvas webgl stencil func separate
8. ctx = canvas webgl stencil op
9. ctx = canvas webgl stencil op separate
10. ctx = canvas webgl stencil mask
11. ctx = canvas webgl stencil mask separate
12. ctx = canvas webgl blend func
13. ctx = canvas webgl blend func separate
14. ctx = canvas webgl blend equation
15. ctx = canvas webgl blend equation separate
   - Expected: canvas_webgl_get_parameter(ctx, CANVAS_WEBGL_SCISSOR_BOX).int_values[2] equals `64`
   - Expected: canvas_webgl_get_parameter(ctx, CANVAS_WEBGL_DEPTH_FUNC).int_value equals `CANVAS_WEBGL_LEQUAL`
   - Expected: canvas_webgl_get_parameter(ctx, CANVAS_WEBGL_DEPTH_WRITEMASK).bool_value is false
   - Expected: canvas_webgl_get_parameter(ctx, CANVAS_WEBGL_COLOR_WRITEMASK).bool_values[1] is false
   - Expected: canvas_webgl_get_parameter(ctx, CANVAS_WEBGL_STENCIL_FUNC).int_value equals `CANVAS_WEBGL_ALWAYS`
   - Expected: canvas_webgl_get_parameter(ctx, CANVAS_WEBGL_STENCIL_REF).int_value equals `3`
   - Expected: canvas_webgl_get_parameter(ctx, CANVAS_WEBGL_STENCIL_VALUE_MASK).int_value equals `255`
   - Expected: canvas_webgl_get_parameter(ctx, CANVAS_WEBGL_STENCIL_FAIL).int_value equals `CANVAS_WEBGL_KEEP`
   - Expected: canvas_webgl_get_parameter(ctx, CANVAS_WEBGL_STENCIL_PASS_DEPTH_FAIL).int_value equals `CANVAS_WEBGL_REPLACE`
   - Expected: canvas_webgl_get_parameter(ctx, CANVAS_WEBGL_STENCIL_PASS_DEPTH_PASS).int_value equals `CANVAS_WEBGL_ZERO`
   - Expected: canvas_webgl_get_parameter(ctx, CANVAS_WEBGL_STENCIL_BACK_FUNC).int_value equals `CANVAS_WEBGL_LEQUAL`
   - Expected: canvas_webgl_get_parameter(ctx, CANVAS_WEBGL_STENCIL_BACK_REF).int_value equals `4`
   - Expected: canvas_webgl_get_parameter(ctx, CANVAS_WEBGL_STENCIL_BACK_VALUE_MASK).int_value equals `127`
   - Expected: canvas_webgl_get_parameter(ctx, CANVAS_WEBGL_STENCIL_BACK_FAIL).int_value equals `CANVAS_WEBGL_REPLACE`
   - Expected: canvas_webgl_get_parameter(ctx, CANVAS_WEBGL_STENCIL_BACK_PASS_DEPTH_FAIL).int_value equals `CANVAS_WEBGL_KEEP`
   - Expected: canvas_webgl_get_parameter(ctx, CANVAS_WEBGL_STENCIL_BACK_PASS_DEPTH_PASS).int_value equals `CANVAS_WEBGL_ZERO`
   - Expected: canvas_webgl_get_parameter(ctx, CANVAS_WEBGL_STENCIL_WRITEMASK).int_value equals `15`
   - Expected: canvas_webgl_get_parameter(ctx, CANVAS_WEBGL_STENCIL_BACK_WRITEMASK).int_value equals `7`
   - Expected: canvas_webgl_get_parameter(ctx, CANVAS_WEBGL_BLEND_SRC_RGB).int_value equals `CANVAS_WEBGL_ONE`
   - Expected: canvas_webgl_get_parameter(ctx, CANVAS_WEBGL_BLEND_DST_RGB).int_value equals `CANVAS_WEBGL_ZERO`
   - Expected: canvas_webgl_get_parameter(ctx, CANVAS_WEBGL_BLEND_SRC_ALPHA).int_value equals `CANVAS_WEBGL_SRC_ALPHA`
   - Expected: canvas_webgl_get_parameter(ctx, CANVAS_WEBGL_BLEND_DST_ALPHA).int_value equals `CANVAS_WEBGL_ONE_MINUS_SRC_ALPHA`
   - Expected: canvas_webgl_get_parameter(ctx, CANVAS_WEBGL_BLEND_EQUATION_RGB).int_value equals `CANVAS_WEBGL_FUNC_ADD`
   - Expected: canvas_webgl_get_parameter(ctx, CANVAS_WEBGL_BLEND_EQUATION_ALPHA).int_value equals `CANVAS_WEBGL_FUNC_SUBTRACT`


<details>
<summary>Executable SSpec</summary>

Runnable source: 39 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ctx: CanvasWebGLContext = canvas_get_context_webgl(320, 240)
ctx = canvas_webgl_scissor(ctx, 4, 5, 64, 32)
ctx = canvas_webgl_depth_func(ctx, CANVAS_WEBGL_LEQUAL)
ctx = canvas_webgl_depth_mask(ctx, false)
ctx = canvas_webgl_color_mask(ctx, true, false, true, false)
ctx = canvas_webgl_stencil_func(ctx, CANVAS_WEBGL_ALWAYS, 3, 255)
ctx = canvas_webgl_stencil_func_separate(ctx, CANVAS_WEBGL_BACK, CANVAS_WEBGL_LEQUAL, 4, 127)
ctx = canvas_webgl_stencil_op(ctx, CANVAS_WEBGL_KEEP, CANVAS_WEBGL_REPLACE, CANVAS_WEBGL_ZERO)
ctx = canvas_webgl_stencil_op_separate(ctx, CANVAS_WEBGL_BACK, CANVAS_WEBGL_REPLACE, CANVAS_WEBGL_KEEP, CANVAS_WEBGL_ZERO)
ctx = canvas_webgl_stencil_mask(ctx, 15)
ctx = canvas_webgl_stencil_mask_separate(ctx, CANVAS_WEBGL_BACK, 7)
ctx = canvas_webgl_blend_func(ctx, CANVAS_WEBGL_SRC_ALPHA, CANVAS_WEBGL_ONE_MINUS_SRC_ALPHA)
ctx = canvas_webgl_blend_func_separate(ctx, CANVAS_WEBGL_ONE, CANVAS_WEBGL_ZERO, CANVAS_WEBGL_SRC_ALPHA, CANVAS_WEBGL_ONE_MINUS_SRC_ALPHA)
ctx = canvas_webgl_blend_equation(ctx, CANVAS_WEBGL_FUNC_ADD)
ctx = canvas_webgl_blend_equation_separate(ctx, CANVAS_WEBGL_FUNC_ADD, CANVAS_WEBGL_FUNC_SUBTRACT)
expect(canvas_webgl_get_parameter(ctx, CANVAS_WEBGL_SCISSOR_BOX).int_values[2]).to_equal(64)
expect(canvas_webgl_get_parameter(ctx, CANVAS_WEBGL_DEPTH_FUNC).int_value).to_equal(CANVAS_WEBGL_LEQUAL)
expect(canvas_webgl_get_parameter(ctx, CANVAS_WEBGL_DEPTH_WRITEMASK).bool_value).to_equal(false)
expect(canvas_webgl_get_parameter(ctx, CANVAS_WEBGL_COLOR_WRITEMASK).bool_values[1]).to_equal(false)
expect(canvas_webgl_get_parameter(ctx, CANVAS_WEBGL_STENCIL_FUNC).int_value).to_equal(CANVAS_WEBGL_ALWAYS)
expect(canvas_webgl_get_parameter(ctx, CANVAS_WEBGL_STENCIL_REF).int_value).to_equal(3)
expect(canvas_webgl_get_parameter(ctx, CANVAS_WEBGL_STENCIL_VALUE_MASK).int_value).to_equal(255)
expect(canvas_webgl_get_parameter(ctx, CANVAS_WEBGL_STENCIL_FAIL).int_value).to_equal(CANVAS_WEBGL_KEEP)
expect(canvas_webgl_get_parameter(ctx, CANVAS_WEBGL_STENCIL_PASS_DEPTH_FAIL).int_value).to_equal(CANVAS_WEBGL_REPLACE)
expect(canvas_webgl_get_parameter(ctx, CANVAS_WEBGL_STENCIL_PASS_DEPTH_PASS).int_value).to_equal(CANVAS_WEBGL_ZERO)
expect(canvas_webgl_get_parameter(ctx, CANVAS_WEBGL_STENCIL_BACK_FUNC).int_value).to_equal(CANVAS_WEBGL_LEQUAL)
expect(canvas_webgl_get_parameter(ctx, CANVAS_WEBGL_STENCIL_BACK_REF).int_value).to_equal(4)
expect(canvas_webgl_get_parameter(ctx, CANVAS_WEBGL_STENCIL_BACK_VALUE_MASK).int_value).to_equal(127)
expect(canvas_webgl_get_parameter(ctx, CANVAS_WEBGL_STENCIL_BACK_FAIL).int_value).to_equal(CANVAS_WEBGL_REPLACE)
expect(canvas_webgl_get_parameter(ctx, CANVAS_WEBGL_STENCIL_BACK_PASS_DEPTH_FAIL).int_value).to_equal(CANVAS_WEBGL_KEEP)
expect(canvas_webgl_get_parameter(ctx, CANVAS_WEBGL_STENCIL_BACK_PASS_DEPTH_PASS).int_value).to_equal(CANVAS_WEBGL_ZERO)
expect(canvas_webgl_get_parameter(ctx, CANVAS_WEBGL_STENCIL_WRITEMASK).int_value).to_equal(15)
expect(canvas_webgl_get_parameter(ctx, CANVAS_WEBGL_STENCIL_BACK_WRITEMASK).int_value).to_equal(7)
expect(canvas_webgl_get_parameter(ctx, CANVAS_WEBGL_BLEND_SRC_RGB).int_value).to_equal(CANVAS_WEBGL_ONE)
expect(canvas_webgl_get_parameter(ctx, CANVAS_WEBGL_BLEND_DST_RGB).int_value).to_equal(CANVAS_WEBGL_ZERO)
expect(canvas_webgl_get_parameter(ctx, CANVAS_WEBGL_BLEND_SRC_ALPHA).int_value).to_equal(CANVAS_WEBGL_SRC_ALPHA)
expect(canvas_webgl_get_parameter(ctx, CANVAS_WEBGL_BLEND_DST_ALPHA).int_value).to_equal(CANVAS_WEBGL_ONE_MINUS_SRC_ALPHA)
expect(canvas_webgl_get_parameter(ctx, CANVAS_WEBGL_BLEND_EQUATION_RGB).int_value).to_equal(CANVAS_WEBGL_FUNC_ADD)
expect(canvas_webgl_get_parameter(ctx, CANVAS_WEBGL_BLEND_EQUATION_ALPHA).int_value).to_equal(CANVAS_WEBGL_FUNC_SUBTRACT)
```

</details>

#### bridges WebGL pixel-store readback and errors

1. var ctx: CanvasWebGLContext = canvas get context webgl
   - Expected: canvas_webgl_get_error(ctx) equals `CANVAS_WEBGL_NO_ERROR`
2. ctx = canvas webgl pixel store i
3. ctx = canvas webgl pixel store i
   - Expected: canvas_webgl_get_parameter(ctx, CANVAS_WEBGL_PACK_ALIGNMENT).int_value equals `1`
   - Expected: canvas_webgl_get_parameter(ctx, CANVAS_WEBGL_UNPACK_ALIGNMENT).int_value equals `8`
   - Expected: canvas_webgl_read_pixels(ctx, 0, 0, 1, 2, CANVAS_WEBGL_RGB, CANVAS_WEBGL_UNSIGNED_BYTE).len() equals `6`
   - Expected: canvas_webgl_get_error(ctx) equals `CANVAS_WEBGL_NO_ERROR`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ctx: CanvasWebGLContext = canvas_get_context_webgl(320, 240)
expect(canvas_webgl_get_error(ctx)).to_equal(CANVAS_WEBGL_NO_ERROR)
ctx = canvas_webgl_pixel_store_i(ctx, CANVAS_WEBGL_PACK_ALIGNMENT, 1)
ctx = canvas_webgl_pixel_store_i(ctx, CANVAS_WEBGL_UNPACK_ALIGNMENT, 8)
expect(canvas_webgl_get_parameter(ctx, CANVAS_WEBGL_PACK_ALIGNMENT).int_value).to_equal(1)
expect(canvas_webgl_get_parameter(ctx, CANVAS_WEBGL_UNPACK_ALIGNMENT).int_value).to_equal(8)
expect(canvas_webgl_read_pixels(ctx, 0, 0, 1, 2, CANVAS_WEBGL_RGB, CANVAS_WEBGL_UNSIGNED_BYTE).len()).to_equal(6)
expect(canvas_webgl_get_error(ctx)).to_equal(CANVAS_WEBGL_NO_ERROR)
```

</details>

#### bridges WebGL identity and implementation limit constants

1. var ctx: CanvasWebGLContext = canvas get context webgl
   - Expected: canvas_webgl_get_parameter(ctx, CANVAS_WEBGL_VENDOR).text_value equals `Simple Browser`
   - Expected: canvas_webgl_get_parameter(ctx, CANVAS_WEBGL_VERSION).text_value equals `WebGL 1.0 Simple Browser`
   - Expected: canvas_webgl_get_parameter(ctx, CANVAS_WEBGL_MAX_TEXTURE_SIZE).int_value equals `4096`
   - Expected: canvas_webgl_get_parameter(ctx, CANVAS_WEBGL_MAX_VIEWPORT_DIMS).int_values[0] equals `4096`
   - Expected: canvas_webgl_get_parameter(ctx, CANVAS_WEBGL_ALIASED_LINE_WIDTH_RANGE).float_values[1] equals `1.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ctx: CanvasWebGLContext = canvas_get_context_webgl(320, 240)
expect(canvas_webgl_get_parameter(ctx, CANVAS_WEBGL_VENDOR).text_value).to_equal("Simple Browser")
expect(canvas_webgl_get_parameter(ctx, CANVAS_WEBGL_VERSION).text_value).to_equal("WebGL 1.0 Simple Browser")
expect(canvas_webgl_get_parameter(ctx, CANVAS_WEBGL_MAX_TEXTURE_SIZE).int_value).to_equal(4096)
expect(canvas_webgl_get_parameter(ctx, CANVAS_WEBGL_MAX_VIEWPORT_DIMS).int_values[0]).to_equal(4096)
expect(canvas_webgl_get_parameter(ctx, CANVAS_WEBGL_ALIASED_LINE_WIDTH_RANGE).float_values[1]).to_equal(1.0)
```

</details>

#### drives a WebGL draw path through canvas bridge helpers

1. var ctx: CanvasWebGLContext = canvas get context webgl
2. ctx = canvas webgl create shader
3. ctx = canvas webgl create shader
4. ctx = canvas webgl shader source
5. ctx = canvas webgl shader source
6. ctx = canvas webgl compile shader
7. ctx = canvas webgl compile shader
8. ctx = canvas webgl create program
9. ctx = canvas webgl attach shader
10. ctx = canvas webgl attach shader
11. ctx = canvas webgl link program
12. ctx = canvas webgl use program
13. ctx = canvas webgl create buffer
14. ctx = canvas webgl bind buffer
15. ctx = canvas webgl buffer data size
   - Expected: canvas_webgl_get_buffer_parameter(ctx, CANVAS_WEBGL_ARRAY_BUFFER, CANVAS_WEBGL_BUFFER_SIZE).int_value equals `48`
   - Expected: canvas_webgl_get_buffer_parameter(ctx, CANVAS_WEBGL_ARRAY_BUFFER, CANVAS_WEBGL_BUFFER_USAGE).int_value equals `CANVAS_WEBGL_STATIC_DRAW`
16. ctx = canvas webgl enable vertex attrib array
17. ctx = canvas webgl vertex attrib pointer
   - Expected: canvas_webgl_get_vertex_attrib(ctx, 0, CANVAS_WEBGL_VERTEX_ATTRIB_ARRAY_ENABLED).bool_value is true
   - Expected: canvas_webgl_get_vertex_attrib(ctx, 0, CANVAS_WEBGL_VERTEX_ATTRIB_ARRAY_SIZE).int_value equals `4`
   - Expected: canvas_webgl_get_vertex_attrib(ctx, 0, CANVAS_WEBGL_VERTEX_ATTRIB_ARRAY_TYPE).int_value equals `CANVAS_WEBGL_FLOAT`
   - Expected: canvas_webgl_get_vertex_attrib(ctx, 0, CANVAS_WEBGL_VERTEX_ATTRIB_ARRAY_NORMALIZED).bool_value is false
   - Expected: canvas_webgl_get_vertex_attrib(ctx, 0, CANVAS_WEBGL_VERTEX_ATTRIB_ARRAY_BUFFER_BINDING).int_value equals `buffer.id`
18. ctx = canvas webgl vertex attrib divisor
   - Expected: canvas_webgl_get_vertex_attrib(ctx, 0, CANVAS_WEBGL_VERTEX_ATTRIB_ARRAY_DIVISOR).int_value equals `2`
   - Expected: canvas_webgl_get_vertex_attrib_offset(ctx, 0, CANVAS_WEBGL_VERTEX_ATTRIB_ARRAY_POINTER) equals `0`
19. ctx = canvas webgl vertex attrib pointer
   - Expected: canvas_webgl_get_vertex_attrib(ctx, 1, CANVAS_WEBGL_VERTEX_ATTRIB_ARRAY_TYPE).int_value equals `CANVAS_WEBGL_UNSIGNED_BYTE`
20. ctx = canvas webgl vertex attrib pointer
   - Expected: canvas_webgl_get_vertex_attrib(ctx, 2, CANVAS_WEBGL_VERTEX_ATTRIB_ARRAY_TYPE).int_value equals `CANVAS_WEBGL_SHORT`
21. ctx = canvas webgl vertex attrib 1f
   - Expected: canvas_webgl_get_vertex_attrib(ctx, 0, CANVAS_WEBGL_CURRENT_VERTEX_ATTRIB).float_values[0] equals `0.125`
22. ctx = canvas webgl vertex attrib 2f
   - Expected: canvas_webgl_get_vertex_attrib(ctx, 0, CANVAS_WEBGL_CURRENT_VERTEX_ATTRIB).float_values[1] equals `0.5`
23. ctx = canvas webgl vertex attrib 3f
   - Expected: canvas_webgl_get_vertex_attrib(ctx, 0, CANVAS_WEBGL_CURRENT_VERTEX_ATTRIB).float_values[2] equals `0.75`
24. ctx = canvas webgl vertex attrib 4f
   - Expected: canvas_webgl_get_vertex_attrib(ctx, 0, CANVAS_WEBGL_CURRENT_VERTEX_ATTRIB).float_values[2] equals `0.75`
25. ctx = canvas webgl vertex attrib 1fv
   - Expected: canvas_webgl_get_vertex_attrib(ctx, 0, CANVAS_WEBGL_CURRENT_VERTEX_ATTRIB).float_values[0] equals `0.375`
26. ctx = canvas webgl vertex attrib 2fv
   - Expected: canvas_webgl_get_vertex_attrib(ctx, 0, CANVAS_WEBGL_CURRENT_VERTEX_ATTRIB).float_values[1] equals `0.625`
27. ctx = canvas webgl vertex attrib 3fv
   - Expected: canvas_webgl_get_vertex_attrib(ctx, 0, CANVAS_WEBGL_CURRENT_VERTEX_ATTRIB).float_values[2] equals `0.875`
28. ctx = canvas webgl vertex attrib 4fv
   - Expected: canvas_webgl_get_vertex_attrib(ctx, 0, CANVAS_WEBGL_CURRENT_VERTEX_ATTRIB).float_values[3] equals `1.0`
   - Expected: ctx.gl.render_commands[13].kind equals `WEBGL_RENDER_COMMAND_VERTEX_ATTRIB_4F`
29. ctx = canvas webgl disable vertex attrib array
   - Expected: canvas_webgl_get_vertex_attrib(ctx, 0, CANVAS_WEBGL_VERTEX_ATTRIB_ARRAY_ENABLED).bool_value is false
30. ctx = canvas webgl enable vertex attrib array
31. ctx = canvas webgl draw arrays
32. ctx = canvas webgl draw arrays
33. ctx = canvas webgl draw arrays
34. ctx = canvas webgl draw arrays
35. ctx = canvas webgl draw arrays instanced
   - Expected: ctx.gl.draw_call_count equals `5`
   - Expected: ctx.gl.last_draw_count equals `3`
   - Expected: ctx.gl.last_draw_mode equals `CANVAS_WEBGL_TRIANGLES`
   - Expected: ctx.gl.render_commands[5].kind equals `WEBGL_RENDER_COMMAND_VERTEX_ATTRIB_DIVISOR`
   - Expected: ctx.gl.render_commands[5].mask equals `2`
   - Expected: ctx.gl.render_commands[last_draw_command].kind equals `WEBGL_RENDER_COMMAND_DRAW_ARRAYS_INSTANCED`
   - Expected: ctx.gl.render_commands[last_draw_command].mask equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 68 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ctx: CanvasWebGLContext = canvas_get_context_webgl(320, 240)
ctx = canvas_webgl_create_shader(ctx, CANVAS_WEBGL_VERTEX_SHADER)
val vs = canvas_webgl_last_shader(ctx)
ctx = canvas_webgl_create_shader(ctx, CANVAS_WEBGL_FRAGMENT_SHADER)
val fs = canvas_webgl_last_shader(ctx)
ctx = canvas_webgl_shader_source(ctx, vs, "attribute vec4 position; void main() { gl_Position = position; }")
ctx = canvas_webgl_shader_source(ctx, fs, "void main() { gl_FragColor = vec4(1.0); }")
ctx = canvas_webgl_compile_shader(ctx, vs)
ctx = canvas_webgl_compile_shader(ctx, fs)
ctx = canvas_webgl_create_program(ctx)
val program = canvas_webgl_last_program(ctx)
ctx = canvas_webgl_attach_shader(ctx, program, vs)
ctx = canvas_webgl_attach_shader(ctx, program, fs)
ctx = canvas_webgl_link_program(ctx, program)
ctx = canvas_webgl_use_program(ctx, program)
ctx = canvas_webgl_create_buffer(ctx)
val buffer = canvas_webgl_last_buffer(ctx)
ctx = canvas_webgl_bind_buffer(ctx, CANVAS_WEBGL_ARRAY_BUFFER, buffer)
ctx = canvas_webgl_buffer_data_size(ctx, CANVAS_WEBGL_ARRAY_BUFFER, 48, CANVAS_WEBGL_STATIC_DRAW)
expect(canvas_webgl_get_buffer_parameter(ctx, CANVAS_WEBGL_ARRAY_BUFFER, CANVAS_WEBGL_BUFFER_SIZE).int_value).to_equal(48)
expect(canvas_webgl_get_buffer_parameter(ctx, CANVAS_WEBGL_ARRAY_BUFFER, CANVAS_WEBGL_BUFFER_USAGE).int_value).to_equal(CANVAS_WEBGL_STATIC_DRAW)
ctx = canvas_webgl_enable_vertex_attrib_array(ctx, 0)
ctx = canvas_webgl_vertex_attrib_pointer(ctx, 0, 4, CANVAS_WEBGL_FLOAT, false, 0, 0)
expect(canvas_webgl_get_vertex_attrib(ctx, 0, CANVAS_WEBGL_VERTEX_ATTRIB_ARRAY_ENABLED).bool_value).to_equal(true)
expect(canvas_webgl_get_vertex_attrib(ctx, 0, CANVAS_WEBGL_VERTEX_ATTRIB_ARRAY_SIZE).int_value).to_equal(4)
expect(canvas_webgl_get_vertex_attrib(ctx, 0, CANVAS_WEBGL_VERTEX_ATTRIB_ARRAY_TYPE).int_value).to_equal(CANVAS_WEBGL_FLOAT)
expect(canvas_webgl_get_vertex_attrib(ctx, 0, CANVAS_WEBGL_VERTEX_ATTRIB_ARRAY_NORMALIZED).bool_value).to_equal(false)
expect(canvas_webgl_get_vertex_attrib(ctx, 0, CANVAS_WEBGL_VERTEX_ATTRIB_ARRAY_BUFFER_BINDING).int_value).to_equal(buffer.id)
ctx = canvas_webgl_vertex_attrib_divisor(ctx, 0, 2)
expect(canvas_webgl_get_vertex_attrib(ctx, 0, CANVAS_WEBGL_VERTEX_ATTRIB_ARRAY_DIVISOR).int_value).to_equal(2)
expect(canvas_webgl_get_vertex_attrib_offset(ctx, 0, CANVAS_WEBGL_VERTEX_ATTRIB_ARRAY_POINTER)).to_equal(0)
ctx = canvas_webgl_vertex_attrib_pointer(ctx, 1, 4, CANVAS_WEBGL_UNSIGNED_BYTE, true, 4, 0)
expect(canvas_webgl_get_vertex_attrib(ctx, 1, CANVAS_WEBGL_VERTEX_ATTRIB_ARRAY_TYPE).int_value).to_equal(CANVAS_WEBGL_UNSIGNED_BYTE)
ctx = canvas_webgl_vertex_attrib_pointer(ctx, 2, 2, CANVAS_WEBGL_SHORT, false, 4, 2)
expect(canvas_webgl_get_vertex_attrib(ctx, 2, CANVAS_WEBGL_VERTEX_ATTRIB_ARRAY_TYPE).int_value).to_equal(CANVAS_WEBGL_SHORT)
ctx = canvas_webgl_vertex_attrib_1f(ctx, 0, 0.125)
expect(canvas_webgl_get_vertex_attrib(ctx, 0, CANVAS_WEBGL_CURRENT_VERTEX_ATTRIB).float_values[0]).to_equal(0.125)
ctx = canvas_webgl_vertex_attrib_2f(ctx, 0, 0.25, 0.5)
expect(canvas_webgl_get_vertex_attrib(ctx, 0, CANVAS_WEBGL_CURRENT_VERTEX_ATTRIB).float_values[1]).to_equal(0.5)
ctx = canvas_webgl_vertex_attrib_3f(ctx, 0, 0.25, 0.5, 0.75)
expect(canvas_webgl_get_vertex_attrib(ctx, 0, CANVAS_WEBGL_CURRENT_VERTEX_ATTRIB).float_values[2]).to_equal(0.75)
ctx = canvas_webgl_vertex_attrib_4f(ctx, 0, 0.25, 0.5, 0.75, 1.0)
expect(canvas_webgl_get_vertex_attrib(ctx, 0, CANVAS_WEBGL_CURRENT_VERTEX_ATTRIB).float_values[2]).to_equal(0.75)
ctx = canvas_webgl_vertex_attrib_1fv(ctx, 0, [0.375])
expect(canvas_webgl_get_vertex_attrib(ctx, 0, CANVAS_WEBGL_CURRENT_VERTEX_ATTRIB).float_values[0]).to_equal(0.375)
ctx = canvas_webgl_vertex_attrib_2fv(ctx, 0, [0.25, 0.625])
expect(canvas_webgl_get_vertex_attrib(ctx, 0, CANVAS_WEBGL_CURRENT_VERTEX_ATTRIB).float_values[1]).to_equal(0.625)
ctx = canvas_webgl_vertex_attrib_3fv(ctx, 0, [0.25, 0.5, 0.875])
expect(canvas_webgl_get_vertex_attrib(ctx, 0, CANVAS_WEBGL_CURRENT_VERTEX_ATTRIB).float_values[2]).to_equal(0.875)
ctx = canvas_webgl_vertex_attrib_4fv(ctx, 0, [0.25, 0.5, 0.75, 1.0])
expect(canvas_webgl_get_vertex_attrib(ctx, 0, CANVAS_WEBGL_CURRENT_VERTEX_ATTRIB).float_values[3]).to_equal(1.0)
expect(ctx.gl.render_commands[13].kind).to_equal(WEBGL_RENDER_COMMAND_VERTEX_ATTRIB_4F)
ctx = canvas_webgl_disable_vertex_attrib_array(ctx, 0)
expect(canvas_webgl_get_vertex_attrib(ctx, 0, CANVAS_WEBGL_VERTEX_ATTRIB_ARRAY_ENABLED).bool_value).to_equal(false)
ctx = canvas_webgl_enable_vertex_attrib_array(ctx, 0)
ctx = canvas_webgl_draw_arrays(ctx, CANVAS_WEBGL_TRIANGLES, 0, 3)
ctx = canvas_webgl_draw_arrays(ctx, CANVAS_WEBGL_LINE_LOOP, 0, 3)
ctx = canvas_webgl_draw_arrays(ctx, CANVAS_WEBGL_LINE_STRIP, 0, 3)
ctx = canvas_webgl_draw_arrays(ctx, CANVAS_WEBGL_TRIANGLE_STRIP, 0, 3)
ctx = canvas_webgl_draw_arrays_instanced(ctx, CANVAS_WEBGL_TRIANGLES, 0, 3, 4)
expect(ctx.gl.draw_call_count).to_equal(5)
expect(ctx.gl.last_draw_count).to_equal(3)
expect(ctx.gl.last_draw_mode).to_equal(CANVAS_WEBGL_TRIANGLES)
expect(ctx.gl.render_commands[5].kind).to_equal(WEBGL_RENDER_COMMAND_VERTEX_ATTRIB_DIVISOR)
expect(ctx.gl.render_commands[5].mask).to_equal(2)
val last_draw_command = ctx.gl.render_commands.len() - 1
expect(ctx.gl.render_commands[last_draw_command].kind).to_equal(WEBGL_RENDER_COMMAND_DRAW_ARRAYS_INSTANCED)
expect(ctx.gl.render_commands[last_draw_command].mask).to_equal(4)
```

</details>

#### bridges WebGL2 vertex array object state

1. var ctx: CanvasWebGLContext = canvas get context webgl2
2. ctx = canvas webgl create vertex array
   - Expected: canvas_webgl_is_vertex_array(ctx, vao) is true
3. ctx = canvas webgl bind vertex array
   - Expected: ctx.gl.render_commands[0].kind equals `WEBGL_RENDER_COMMAND_BIND_VERTEX_ARRAY`
4. ctx = canvas webgl create buffer
5. ctx = canvas webgl bind buffer
6. ctx = canvas webgl buffer data size
7. ctx = canvas webgl enable vertex attrib array
8. ctx = canvas webgl vertex attrib pointer
9. ctx = canvas webgl bind vertex array
   - Expected: canvas_webgl_get_vertex_attrib(ctx, 1, CANVAS_WEBGL_VERTEX_ATTRIB_ARRAY_BUFFER_BINDING).int_value equals `vao_buffer.id`
   - Expected: ctx.gl.render_commands[last_bind_command].kind equals `WEBGL_RENDER_COMMAND_BIND_VERTEX_ARRAY`
10. ctx = canvas webgl delete vertex array
   - Expected: canvas_webgl_is_vertex_array(ctx, vao) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ctx: CanvasWebGLContext = canvas_get_context_webgl2(320, 240)
ctx = canvas_webgl_create_vertex_array(ctx)
val vao = canvas_webgl_last_vertex_array(ctx)
expect(canvas_webgl_is_vertex_array(ctx, vao)).to_equal(true)
ctx = canvas_webgl_bind_vertex_array(ctx, vao)
expect(ctx.gl.render_commands[0].kind).to_equal(WEBGL_RENDER_COMMAND_BIND_VERTEX_ARRAY)
ctx = canvas_webgl_create_buffer(ctx)
val vao_buffer = canvas_webgl_last_buffer(ctx)
ctx = canvas_webgl_bind_buffer(ctx, CANVAS_WEBGL_ARRAY_BUFFER, vao_buffer)
ctx = canvas_webgl_buffer_data_size(ctx, CANVAS_WEBGL_ARRAY_BUFFER, 32, CANVAS_WEBGL_STATIC_DRAW)
ctx = canvas_webgl_enable_vertex_attrib_array(ctx, 1)
ctx = canvas_webgl_vertex_attrib_pointer(ctx, 1, 2, CANVAS_WEBGL_FLOAT, false, 0, 0)
ctx = canvas_webgl_bind_vertex_array(ctx, vao)
expect(canvas_webgl_get_vertex_attrib(ctx, 1, CANVAS_WEBGL_VERTEX_ATTRIB_ARRAY_BUFFER_BINDING).int_value).to_equal(vao_buffer.id)
val last_bind_command = ctx.gl.render_commands.len() - 1
expect(ctx.gl.render_commands[last_bind_command].kind).to_equal(WEBGL_RENDER_COMMAND_BIND_VERTEX_ARRAY)
ctx = canvas_webgl_delete_vertex_array(ctx, vao)
expect(canvas_webgl_is_vertex_array(ctx, vao)).to_equal(false)
```

</details>

#### drives a WebGL indexed draw path through canvas bridge helpers

1. var ctx: CanvasWebGLContext = canvas get context webgl
2. ctx = canvas webgl create shader
3. ctx = canvas webgl create shader
4. ctx = canvas webgl shader source
5. ctx = canvas webgl shader source
6. ctx = canvas webgl compile shader
7. ctx = canvas webgl compile shader
8. ctx = canvas webgl create program
9. ctx = canvas webgl attach shader
10. ctx = canvas webgl attach shader
11. ctx = canvas webgl link program
12. ctx = canvas webgl use program
13. ctx = canvas webgl create buffer
14. ctx = canvas webgl bind buffer
15. ctx = canvas webgl buffer data size
16. ctx = canvas webgl enable vertex attrib array
17. ctx = canvas webgl vertex attrib pointer
18. ctx = canvas webgl create buffer
19. ctx = canvas webgl bind buffer
20. ctx = canvas webgl buffer data size
21. ctx = canvas webgl draw elements
22. ctx = canvas webgl draw elements
23. ctx = canvas webgl draw elements instanced
   - Expected: ctx.gl.indexed_draw_call_count equals `3`
   - Expected: ctx.gl.render_commands[7].element_type equals `CANVAS_WEBGL_UNSIGNED_SHORT`
   - Expected: ctx.gl.render_commands[8].mode equals `CANVAS_WEBGL_TRIANGLE_FAN`
   - Expected: ctx.gl.render_commands[9].kind equals `WEBGL_RENDER_COMMAND_DRAW_ELEMENTS_INSTANCED`
   - Expected: ctx.gl.render_commands[9].mask equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 33 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ctx: CanvasWebGLContext = canvas_get_context_webgl(320, 240)
ctx = canvas_webgl_create_shader(ctx, CANVAS_WEBGL_VERTEX_SHADER)
val vs = canvas_webgl_last_shader(ctx)
ctx = canvas_webgl_create_shader(ctx, CANVAS_WEBGL_FRAGMENT_SHADER)
val fs = canvas_webgl_last_shader(ctx)
ctx = canvas_webgl_shader_source(ctx, vs, "attribute vec4 position; void main() { gl_Position = position; }")
ctx = canvas_webgl_shader_source(ctx, fs, "void main() { gl_FragColor = vec4(1.0); }")
ctx = canvas_webgl_compile_shader(ctx, vs)
ctx = canvas_webgl_compile_shader(ctx, fs)
ctx = canvas_webgl_create_program(ctx)
val program = canvas_webgl_last_program(ctx)
ctx = canvas_webgl_attach_shader(ctx, program, vs)
ctx = canvas_webgl_attach_shader(ctx, program, fs)
ctx = canvas_webgl_link_program(ctx, program)
ctx = canvas_webgl_use_program(ctx, program)
ctx = canvas_webgl_create_buffer(ctx)
val vertex_buffer = canvas_webgl_last_buffer(ctx)
ctx = canvas_webgl_bind_buffer(ctx, CANVAS_WEBGL_ARRAY_BUFFER, vertex_buffer)
ctx = canvas_webgl_buffer_data_size(ctx, CANVAS_WEBGL_ARRAY_BUFFER, 48, CANVAS_WEBGL_STATIC_DRAW)
ctx = canvas_webgl_enable_vertex_attrib_array(ctx, 0)
ctx = canvas_webgl_vertex_attrib_pointer(ctx, 0, 4, CANVAS_WEBGL_FLOAT, false, 0, 0)
ctx = canvas_webgl_create_buffer(ctx)
val index_buffer = canvas_webgl_last_buffer(ctx)
ctx = canvas_webgl_bind_buffer(ctx, CANVAS_WEBGL_ELEMENT_ARRAY_BUFFER, index_buffer)
ctx = canvas_webgl_buffer_data_size(ctx, CANVAS_WEBGL_ELEMENT_ARRAY_BUFFER, 6, CANVAS_WEBGL_STATIC_DRAW)
ctx = canvas_webgl_draw_elements(ctx, CANVAS_WEBGL_LINES, 2, CANVAS_WEBGL_UNSIGNED_SHORT, 0)
ctx = canvas_webgl_draw_elements(ctx, CANVAS_WEBGL_TRIANGLE_FAN, 2, CANVAS_WEBGL_UNSIGNED_SHORT, 0)
ctx = canvas_webgl_draw_elements_instanced(ctx, CANVAS_WEBGL_LINES, 2, CANVAS_WEBGL_UNSIGNED_SHORT, 0, 5)
expect(ctx.gl.indexed_draw_call_count).to_equal(3)
expect(ctx.gl.render_commands[7].element_type).to_equal(CANVAS_WEBGL_UNSIGNED_SHORT)
expect(ctx.gl.render_commands[8].mode).to_equal(CANVAS_WEBGL_TRIANGLE_FAN)
expect(ctx.gl.render_commands[9].kind).to_equal(WEBGL_RENDER_COMMAND_DRAW_ELEMENTS_INSTANCED)
expect(ctx.gl.render_commands[9].mask).to_equal(5)
```

</details>

#### bridges WebGL shader and program lifecycle helpers

1. var ctx: CanvasWebGLContext = canvas get context webgl
2. ctx = canvas webgl create shader
3. ctx = canvas webgl create shader
4. ctx = canvas webgl shader source
5. ctx = canvas webgl shader source
6. ctx = canvas webgl compile shader
7. ctx = canvas webgl compile shader
   - Expected: canvas_webgl_is_shader(ctx, vs) is true
   - Expected: canvas_webgl_get_shader_source(ctx, vs) equals `attribute vec4 position; void main() { gl_Position = position; }`
   - Expected: canvas_webgl_get_shader_info_log(ctx, vs) equals ``
8. ctx = canvas webgl create program
   - Expected: canvas_webgl_is_program(ctx, program) is true
9. ctx = canvas webgl attach shader
10. ctx = canvas webgl attach shader
   - Expected: canvas_webgl_get_attached_shaders(ctx, program).len() equals `2`
11. ctx = canvas webgl link program
12. ctx = canvas webgl validate program
   - Expected: canvas_webgl_get_program_info_log(ctx, program) equals ``
   - Expected: canvas_webgl_get_active_attrib(ctx, program, 0).name equals `position`
13. ctx = canvas webgl detach shader
   - Expected: canvas_webgl_get_attached_shaders(ctx, program).len() equals `1`
14. ctx = canvas webgl delete shader
15. ctx = canvas webgl delete program
   - Expected: canvas_webgl_is_shader(ctx, fs) is false
   - Expected: canvas_webgl_is_program(ctx, program) is false
   - Expected: canvas_webgl_get_program_parameter(ctx, program, CANVAS_WEBGL_DELETE_STATUS).bool_value is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 29 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ctx: CanvasWebGLContext = canvas_get_context_webgl(320, 240)
ctx = canvas_webgl_create_shader(ctx, CANVAS_WEBGL_VERTEX_SHADER)
val vs = canvas_webgl_last_shader(ctx)
ctx = canvas_webgl_create_shader(ctx, CANVAS_WEBGL_FRAGMENT_SHADER)
val fs = canvas_webgl_last_shader(ctx)
ctx = canvas_webgl_shader_source(ctx, vs, "attribute vec4 position; void main() { gl_Position = position; }")
ctx = canvas_webgl_shader_source(ctx, fs, "void main() { gl_FragColor = vec4(1.0); }")
ctx = canvas_webgl_compile_shader(ctx, vs)
ctx = canvas_webgl_compile_shader(ctx, fs)
expect(canvas_webgl_is_shader(ctx, vs)).to_equal(true)
expect(canvas_webgl_get_shader_source(ctx, vs)).to_equal("attribute vec4 position; void main() { gl_Position = position; }")
expect(canvas_webgl_get_shader_info_log(ctx, vs)).to_equal("")
ctx = canvas_webgl_create_program(ctx)
val program = canvas_webgl_last_program(ctx)
expect(canvas_webgl_is_program(ctx, program)).to_equal(true)
ctx = canvas_webgl_attach_shader(ctx, program, vs)
ctx = canvas_webgl_attach_shader(ctx, program, fs)
expect(canvas_webgl_get_attached_shaders(ctx, program).len()).to_equal(2)
ctx = canvas_webgl_link_program(ctx, program)
ctx = canvas_webgl_validate_program(ctx, program)
expect(canvas_webgl_get_program_info_log(ctx, program)).to_equal("")
expect(canvas_webgl_get_active_attrib(ctx, program, 0).name).to_equal("position")
ctx = canvas_webgl_detach_shader(ctx, program, fs)
expect(canvas_webgl_get_attached_shaders(ctx, program).len()).to_equal(1)
ctx = canvas_webgl_delete_shader(ctx, fs)
ctx = canvas_webgl_delete_program(ctx, program)
expect(canvas_webgl_is_shader(ctx, fs)).to_equal(false)
expect(canvas_webgl_is_program(ctx, program)).to_equal(false)
expect(canvas_webgl_get_program_parameter(ctx, program, CANVAS_WEBGL_DELETE_STATUS).bool_value).to_equal(true)
```

</details>

#### bridges WebGL shader precision and reflection constants

1. var ctx: CanvasWebGLContext = canvas get context webgl
2. ctx = canvas webgl create shader
   - Expected: canvas_webgl_get_shader_parameter(ctx, shader, CANVAS_WEBGL_SHADER_TYPE).int_value equals `CANVAS_WEBGL_VERTEX_SHADER`
   - Expected: high_float.valid is true
   - Expected: high_float.precision equals `23`
   - Expected: medium_int.valid is true
   - Expected: medium_int.range_max equals `16`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ctx: CanvasWebGLContext = canvas_get_context_webgl(320, 240)
ctx = canvas_webgl_create_shader(ctx, CANVAS_WEBGL_VERTEX_SHADER)
val shader = canvas_webgl_last_shader(ctx)
expect(canvas_webgl_get_shader_parameter(ctx, shader, CANVAS_WEBGL_SHADER_TYPE).int_value).to_equal(CANVAS_WEBGL_VERTEX_SHADER)
val high_float = canvas_webgl_get_shader_precision_format(ctx, CANVAS_WEBGL_VERTEX_SHADER, CANVAS_WEBGL_HIGH_FLOAT)
expect(high_float.valid).to_equal(true)
expect(high_float.precision).to_equal(23)
val medium_int = canvas_webgl_get_shader_precision_format(ctx, CANVAS_WEBGL_FRAGMENT_SHADER, CANVAS_WEBGL_MEDIUM_INT)
expect(medium_int.valid).to_equal(true)
expect(medium_int.range_max).to_equal(16)
```

</details>

#### bridges WebGL uniform reflection and setters

1. var ctx: CanvasWebGLContext = canvas get context webgl
2. ctx = canvas webgl create shader
3. ctx = canvas webgl create shader
4. ctx = canvas webgl shader source
5. ctx = canvas webgl shader source
6. ctx = canvas webgl compile shader
7. ctx = canvas webgl compile shader
8. ctx = canvas webgl create program
9. ctx = canvas webgl attach shader
10. ctx = canvas webgl attach shader
11. ctx = canvas webgl link program
12. ctx = canvas webgl use program
   - Expected: canvas_webgl_get_active_uniform(ctx, program, 0).data_type equals `CANVAS_WEBGL_FLOAT_MAT4`
   - Expected: canvas_webgl_get_active_uniform(ctx, program, 1).data_type equals `CANVAS_WEBGL_FLOAT_MAT2`
   - Expected: canvas_webgl_get_active_uniform(ctx, program, 2).data_type equals `CANVAS_WEBGL_FLOAT_MAT3`
   - Expected: canvas_webgl_get_active_uniform(ctx, program, 4).data_type equals `CANVAS_WEBGL_FLOAT_VEC2`
   - Expected: canvas_webgl_get_active_uniform(ctx, program, 5).data_type equals `CANVAS_WEBGL_FLOAT_VEC3`
   - Expected: canvas_webgl_get_active_uniform(ctx, program, 6).data_type equals `CANVAS_WEBGL_INT`
   - Expected: canvas_webgl_get_active_uniform(ctx, program, 7).data_type equals `CANVAS_WEBGL_INT_VEC2`
   - Expected: canvas_webgl_get_active_uniform(ctx, program, 8).data_type equals `CANVAS_WEBGL_INT_VEC3`
   - Expected: canvas_webgl_get_active_uniform(ctx, program, 9).data_type equals `CANVAS_WEBGL_FLOAT_VEC4`
   - Expected: canvas_webgl_get_active_uniform(ctx, program, 10).data_type equals `CANVAS_WEBGL_SAMPLER_2D`
   - Expected: canvas_webgl_get_active_uniform(ctx, program, 11).data_type equals `CANVAS_WEBGL_INT_VEC4`
13. ctx = canvas webgl uniform 1f
14. ctx = canvas webgl uniform 2f
15. ctx = canvas webgl uniform 3f
16. ctx = canvas webgl uniform 4f
17. ctx = canvas webgl uniform 1i
18. ctx = canvas webgl uniform matrix4fv
19. ctx = canvas webgl uniform matrix2fv
20. ctx = canvas webgl uniform matrix3fv
   - Expected: ctx.gl.render_commands[1].kind equals `WEBGL_RENDER_COMMAND_UNIFORM_1F`
   - Expected: ctx.gl.render_commands[1].x equals `opacity`
   - Expected: ctx.gl.render_commands[2].kind equals `WEBGL_RENDER_COMMAND_UNIFORM_2F`
   - Expected: ctx.gl.render_commands[2].green equals `4.0`
   - Expected: ctx.gl.render_commands[3].kind equals `WEBGL_RENDER_COMMAND_UNIFORM_3F`
   - Expected: ctx.gl.render_commands[3].blue equals `0.3`
   - Expected: ctx.gl.render_commands[4].kind equals `WEBGL_RENDER_COMMAND_UNIFORM_4F`
   - Expected: ctx.gl.render_commands[4].red equals `0.4`
   - Expected: ctx.gl.render_commands[5].kind equals `WEBGL_RENDER_COMMAND_UNIFORM_1I`
   - Expected: ctx.gl.render_commands[5].mask equals `2`
   - Expected: ctx.gl.render_commands[6].kind equals `WEBGL_RENDER_COMMAND_UNIFORM_MATRIX4FV`
   - Expected: ctx.gl.render_commands[6].float_values[12] equals `2.0`
   - Expected: ctx.gl.render_commands[7].kind equals `WEBGL_RENDER_COMMAND_UNIFORM_MATRIX2FV`
   - Expected: ctx.gl.render_commands[7].float_values[3] equals `4.0`
   - Expected: ctx.gl.render_commands[8].kind equals `WEBGL_RENDER_COMMAND_UNIFORM_MATRIX3FV`
   - Expected: ctx.gl.render_commands[8].float_values[7] equals `3.0`
21. ctx = canvas webgl uniform 1i
22. ctx = canvas webgl uniform 2i
23. ctx = canvas webgl uniform 3i
24. ctx = canvas webgl uniform 4i
   - Expected: ctx.gl.render_commands[9].kind equals `WEBGL_RENDER_COMMAND_UNIFORM_1I`
   - Expected: ctx.gl.render_commands[9].mask equals `3`
   - Expected: ctx.gl.render_commands[10].kind equals `WEBGL_RENDER_COMMAND_UNIFORM_2I`
   - Expected: ctx.gl.render_commands[10].width equals `5`
   - Expected: ctx.gl.render_commands[11].kind equals `WEBGL_RENDER_COMMAND_UNIFORM_3I`
   - Expected: ctx.gl.render_commands[11].height equals `8`
   - Expected: ctx.gl.render_commands[12].kind equals `WEBGL_RENDER_COMMAND_UNIFORM_4I`
   - Expected: ctx.gl.render_commands[12].mask equals `12`
   - Expected: canvas_webgl_get_uniform(ctx, program, flags).int_values[1] equals `5`
25. ctx = canvas webgl uniform 1iv
26. ctx = canvas webgl uniform 2iv
27. ctx = canvas webgl uniform 3iv
28. ctx = canvas webgl uniform 4iv
   - Expected: ctx.gl.render_commands[13].kind equals `WEBGL_RENDER_COMMAND_UNIFORM_1IV`
   - Expected: ctx.gl.render_commands[13].mask equals `13`
   - Expected: ctx.gl.render_commands[14].kind equals `WEBGL_RENDER_COMMAND_UNIFORM_2IV`
   - Expected: ctx.gl.render_commands[14].width equals `15`
   - Expected: ctx.gl.render_commands[15].kind equals `WEBGL_RENDER_COMMAND_UNIFORM_3IV`
   - Expected: ctx.gl.render_commands[15].height equals `18`
   - Expected: ctx.gl.render_commands[16].kind equals `WEBGL_RENDER_COMMAND_UNIFORM_4IV`
   - Expected: ctx.gl.render_commands[16].mask equals `22`
   - Expected: canvas_webgl_get_uniform(ctx, program, mask).int_values[3] equals `22`
29. ctx = canvas webgl uniform 1fv
30. ctx = canvas webgl uniform 2fv
31. ctx = canvas webgl uniform 3fv
32. ctx = canvas webgl uniform 4fv
   - Expected: ctx.gl.render_commands[17].kind equals `WEBGL_RENDER_COMMAND_UNIFORM_1FV`
   - Expected: ctx.gl.render_commands[17].float_values[0] equals `0.75`
   - Expected: ctx.gl.render_commands[18].kind equals `WEBGL_RENDER_COMMAND_UNIFORM_2FV`
   - Expected: ctx.gl.render_commands[18].float_values[1] equals `8.0`
   - Expected: ctx.gl.render_commands[19].kind equals `WEBGL_RENDER_COMMAND_UNIFORM_3FV`
   - Expected: ctx.gl.render_commands[19].float_values[2] equals `0.9`
   - Expected: ctx.gl.render_commands[20].kind equals `WEBGL_RENDER_COMMAND_UNIFORM_4FV`
   - Expected: ctx.gl.render_commands[20].float_values[3] equals `1.0`
   - Expected: canvas_webgl_get_uniform(ctx, program, opacity).float_value equals `0.75`
   - Expected: canvas_webgl_get_uniform(ctx, program, uv_scale).float_values[1] equals `8.0`
   - Expected: canvas_webgl_get_uniform(ctx, program, diffuse).int_value equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 104 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ctx: CanvasWebGLContext = canvas_get_context_webgl(320, 240)
ctx = canvas_webgl_create_shader(ctx, CANVAS_WEBGL_VERTEX_SHADER)
val vs = canvas_webgl_last_shader(ctx)
ctx = canvas_webgl_create_shader(ctx, CANVAS_WEBGL_FRAGMENT_SHADER)
val fs = canvas_webgl_last_shader(ctx)
ctx = canvas_webgl_shader_source(ctx, vs, "attribute vec4 position; uniform mat4 model; uniform mat2 basis; uniform mat3 normalMatrix; uniform float opacity; uniform vec2 uvScale; uniform vec3 normalBias; uniform int layer; uniform ivec2 flags; uniform ivec3 range; void main() { gl_Position = model * position; }")
ctx = canvas_webgl_shader_source(ctx, fs, "uniform vec4 tint; uniform sampler2D diffuse; uniform ivec4 mask; void main() { gl_FragColor = tint; }")
ctx = canvas_webgl_compile_shader(ctx, vs)
ctx = canvas_webgl_compile_shader(ctx, fs)
ctx = canvas_webgl_create_program(ctx)
val program = canvas_webgl_last_program(ctx)
ctx = canvas_webgl_attach_shader(ctx, program, vs)
ctx = canvas_webgl_attach_shader(ctx, program, fs)
ctx = canvas_webgl_link_program(ctx, program)
ctx = canvas_webgl_use_program(ctx, program)
val model = canvas_webgl_get_uniform_location(ctx, program, "model")
val basis = canvas_webgl_get_uniform_location(ctx, program, "basis")
val normal_matrix = canvas_webgl_get_uniform_location(ctx, program, "normalMatrix")
val opacity = canvas_webgl_get_uniform_location(ctx, program, "opacity")
val uv_scale = canvas_webgl_get_uniform_location(ctx, program, "uvScale")
val normal_bias = canvas_webgl_get_uniform_location(ctx, program, "normalBias")
val layer = canvas_webgl_get_uniform_location(ctx, program, "layer")
val flags = canvas_webgl_get_uniform_location(ctx, program, "flags")
val range = canvas_webgl_get_uniform_location(ctx, program, "range")
val tint = canvas_webgl_get_uniform_location(ctx, program, "tint")
val diffuse = canvas_webgl_get_uniform_location(ctx, program, "diffuse")
val mask = canvas_webgl_get_uniform_location(ctx, program, "mask")
expect(canvas_webgl_get_active_uniform(ctx, program, 0).data_type).to_equal(CANVAS_WEBGL_FLOAT_MAT4)
expect(canvas_webgl_get_active_uniform(ctx, program, 1).data_type).to_equal(CANVAS_WEBGL_FLOAT_MAT2)
expect(canvas_webgl_get_active_uniform(ctx, program, 2).data_type).to_equal(CANVAS_WEBGL_FLOAT_MAT3)
expect(canvas_webgl_get_active_uniform(ctx, program, 4).data_type).to_equal(CANVAS_WEBGL_FLOAT_VEC2)
expect(canvas_webgl_get_active_uniform(ctx, program, 5).data_type).to_equal(CANVAS_WEBGL_FLOAT_VEC3)
expect(canvas_webgl_get_active_uniform(ctx, program, 6).data_type).to_equal(CANVAS_WEBGL_INT)
expect(canvas_webgl_get_active_uniform(ctx, program, 7).data_type).to_equal(CANVAS_WEBGL_INT_VEC2)
expect(canvas_webgl_get_active_uniform(ctx, program, 8).data_type).to_equal(CANVAS_WEBGL_INT_VEC3)
expect(canvas_webgl_get_active_uniform(ctx, program, 9).data_type).to_equal(CANVAS_WEBGL_FLOAT_VEC4)
expect(canvas_webgl_get_active_uniform(ctx, program, 10).data_type).to_equal(CANVAS_WEBGL_SAMPLER_2D)
expect(canvas_webgl_get_active_uniform(ctx, program, 11).data_type).to_equal(CANVAS_WEBGL_INT_VEC4)
ctx = canvas_webgl_uniform_1f(ctx, opacity, 0.5)
ctx = canvas_webgl_uniform_2f(ctx, uv_scale, 2.0, 4.0)
ctx = canvas_webgl_uniform_3f(ctx, normal_bias, 0.1, 0.2, 0.3)
ctx = canvas_webgl_uniform_4f(ctx, tint, 0.4, 0.5, 0.6, 1.0)
ctx = canvas_webgl_uniform_1i(ctx, diffuse, 2)
val matrix: [f64] = [1.0, 0.0, 0.0, 0.0, 0.0, 1.0, 0.0, 0.0, 0.0, 0.0, 1.0, 0.0, 2.0, 3.0, 4.0, 1.0]
ctx = canvas_webgl_uniform_matrix4fv(ctx, model, false, matrix)
ctx = canvas_webgl_uniform_matrix2fv(ctx, basis, false, [1.0, 2.0, 3.0, 4.0])
ctx = canvas_webgl_uniform_matrix3fv(ctx, normal_matrix, false, [1.0, 0.0, 0.0, 0.0, 1.0, 0.0, 2.0, 3.0, 1.0])
expect(ctx.gl.render_commands[1].kind).to_equal(WEBGL_RENDER_COMMAND_UNIFORM_1F)
expect(ctx.gl.render_commands[1].x).to_equal(opacity)
expect(ctx.gl.render_commands[2].kind).to_equal(WEBGL_RENDER_COMMAND_UNIFORM_2F)
expect(ctx.gl.render_commands[2].green).to_equal(4.0)
expect(ctx.gl.render_commands[3].kind).to_equal(WEBGL_RENDER_COMMAND_UNIFORM_3F)
expect(ctx.gl.render_commands[3].blue).to_equal(0.3)
expect(ctx.gl.render_commands[4].kind).to_equal(WEBGL_RENDER_COMMAND_UNIFORM_4F)
expect(ctx.gl.render_commands[4].red).to_equal(0.4)
expect(ctx.gl.render_commands[5].kind).to_equal(WEBGL_RENDER_COMMAND_UNIFORM_1I)
expect(ctx.gl.render_commands[5].mask).to_equal(2)
expect(ctx.gl.render_commands[6].kind).to_equal(WEBGL_RENDER_COMMAND_UNIFORM_MATRIX4FV)
expect(ctx.gl.render_commands[6].float_values[12]).to_equal(2.0)
expect(ctx.gl.render_commands[7].kind).to_equal(WEBGL_RENDER_COMMAND_UNIFORM_MATRIX2FV)
expect(ctx.gl.render_commands[7].float_values[3]).to_equal(4.0)
expect(ctx.gl.render_commands[8].kind).to_equal(WEBGL_RENDER_COMMAND_UNIFORM_MATRIX3FV)
expect(ctx.gl.render_commands[8].float_values[7]).to_equal(3.0)
ctx = canvas_webgl_uniform_1i(ctx, layer, 3)
ctx = canvas_webgl_uniform_2i(ctx, flags, 4, 5)
ctx = canvas_webgl_uniform_3i(ctx, range, 6, 7, 8)
ctx = canvas_webgl_uniform_4i(ctx, mask, 9, 10, 11, 12)
expect(ctx.gl.render_commands[9].kind).to_equal(WEBGL_RENDER_COMMAND_UNIFORM_1I)
expect(ctx.gl.render_commands[9].mask).to_equal(3)
expect(ctx.gl.render_commands[10].kind).to_equal(WEBGL_RENDER_COMMAND_UNIFORM_2I)
expect(ctx.gl.render_commands[10].width).to_equal(5)
expect(ctx.gl.render_commands[11].kind).to_equal(WEBGL_RENDER_COMMAND_UNIFORM_3I)
expect(ctx.gl.render_commands[11].height).to_equal(8)
expect(ctx.gl.render_commands[12].kind).to_equal(WEBGL_RENDER_COMMAND_UNIFORM_4I)
expect(ctx.gl.render_commands[12].mask).to_equal(12)
expect(canvas_webgl_get_uniform(ctx, program, flags).int_values[1]).to_equal(5)
ctx = canvas_webgl_uniform_1iv(ctx, layer, [13])
ctx = canvas_webgl_uniform_2iv(ctx, flags, [14, 15])
ctx = canvas_webgl_uniform_3iv(ctx, range, [16, 17, 18])
ctx = canvas_webgl_uniform_4iv(ctx, mask, [19, 20, 21, 22])
expect(ctx.gl.render_commands[13].kind).to_equal(WEBGL_RENDER_COMMAND_UNIFORM_1IV)
expect(ctx.gl.render_commands[13].mask).to_equal(13)
expect(ctx.gl.render_commands[14].kind).to_equal(WEBGL_RENDER_COMMAND_UNIFORM_2IV)
expect(ctx.gl.render_commands[14].width).to_equal(15)
expect(ctx.gl.render_commands[15].kind).to_equal(WEBGL_RENDER_COMMAND_UNIFORM_3IV)
expect(ctx.gl.render_commands[15].height).to_equal(18)
expect(ctx.gl.render_commands[16].kind).to_equal(WEBGL_RENDER_COMMAND_UNIFORM_4IV)
expect(ctx.gl.render_commands[16].mask).to_equal(22)
expect(canvas_webgl_get_uniform(ctx, program, mask).int_values[3]).to_equal(22)
ctx = canvas_webgl_uniform_1fv(ctx, opacity, [0.75])
ctx = canvas_webgl_uniform_2fv(ctx, uv_scale, [6.0, 8.0])
ctx = canvas_webgl_uniform_3fv(ctx, normal_bias, [0.7, 0.8, 0.9])
ctx = canvas_webgl_uniform_4fv(ctx, tint, [0.2, 0.3, 0.4, 1.0])
expect(ctx.gl.render_commands[17].kind).to_equal(WEBGL_RENDER_COMMAND_UNIFORM_1FV)
expect(ctx.gl.render_commands[17].float_values[0]).to_equal(0.75)
expect(ctx.gl.render_commands[18].kind).to_equal(WEBGL_RENDER_COMMAND_UNIFORM_2FV)
expect(ctx.gl.render_commands[18].float_values[1]).to_equal(8.0)
expect(ctx.gl.render_commands[19].kind).to_equal(WEBGL_RENDER_COMMAND_UNIFORM_3FV)
expect(ctx.gl.render_commands[19].float_values[2]).to_equal(0.9)
expect(ctx.gl.render_commands[20].kind).to_equal(WEBGL_RENDER_COMMAND_UNIFORM_4FV)
expect(ctx.gl.render_commands[20].float_values[3]).to_equal(1.0)
expect(canvas_webgl_get_uniform(ctx, program, opacity).float_value).to_equal(0.75)
expect(canvas_webgl_get_uniform(ctx, program, uv_scale).float_values[1]).to_equal(8.0)
expect(canvas_webgl_get_uniform(ctx, program, diffuse).int_value).to_equal(2)
```

</details>

#### bridges WebGL resource probes and deletion

1. var ctx: CanvasWebGLContext = canvas get context webgl
2. ctx = canvas webgl create buffer
3. ctx = canvas webgl create texture
4. ctx = canvas webgl create framebuffer
5. ctx = canvas webgl create renderbuffer
   - Expected: canvas_webgl_is_buffer(ctx, buffer) is true
   - Expected: canvas_webgl_is_texture(ctx, texture) is true
   - Expected: canvas_webgl_is_framebuffer(ctx, framebuffer) is true
   - Expected: canvas_webgl_is_renderbuffer(ctx, renderbuffer) is true
6. ctx = canvas webgl delete buffer
7. ctx = canvas webgl delete texture
8. ctx = canvas webgl delete framebuffer
9. ctx = canvas webgl delete renderbuffer
   - Expected: canvas_webgl_is_buffer(ctx, buffer) is false
   - Expected: canvas_webgl_is_texture(ctx, texture) is false
   - Expected: canvas_webgl_is_framebuffer(ctx, framebuffer) is false
   - Expected: canvas_webgl_is_renderbuffer(ctx, renderbuffer) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ctx: CanvasWebGLContext = canvas_get_context_webgl(320, 240)
ctx = canvas_webgl_create_buffer(ctx)
val buffer = canvas_webgl_last_buffer(ctx)
ctx = canvas_webgl_create_texture(ctx)
val texture = canvas_webgl_last_texture(ctx)
ctx = canvas_webgl_create_framebuffer(ctx)
val framebuffer = canvas_webgl_last_framebuffer(ctx)
ctx = canvas_webgl_create_renderbuffer(ctx)
val renderbuffer = canvas_webgl_last_renderbuffer(ctx)
expect(canvas_webgl_is_buffer(ctx, buffer)).to_equal(true)
expect(canvas_webgl_is_texture(ctx, texture)).to_equal(true)
expect(canvas_webgl_is_framebuffer(ctx, framebuffer)).to_equal(true)
expect(canvas_webgl_is_renderbuffer(ctx, renderbuffer)).to_equal(true)
ctx = canvas_webgl_delete_buffer(ctx, buffer)
ctx = canvas_webgl_delete_texture(ctx, texture)
ctx = canvas_webgl_delete_framebuffer(ctx, framebuffer)
ctx = canvas_webgl_delete_renderbuffer(ctx, renderbuffer)
expect(canvas_webgl_is_buffer(ctx, buffer)).to_equal(false)
expect(canvas_webgl_is_texture(ctx, texture)).to_equal(false)
expect(canvas_webgl_is_framebuffer(ctx, framebuffer)).to_equal(false)
expect(canvas_webgl_is_renderbuffer(ctx, renderbuffer)).to_equal(false)
```

</details>

#### bridges WebGL2 sampler object state

1. var ctx: CanvasWebGLContext = canvas get context webgl2
2. ctx = canvas webgl create sampler
   - Expected: canvas_webgl_is_sampler(ctx, sampler) is true
3. ctx = canvas webgl bind sampler
4. ctx = canvas webgl active texture
   - Expected: canvas_webgl_get_parameter(ctx, CANVAS_WEBGL_SAMPLER_BINDING).int_value equals `sampler.id`
5. ctx = canvas webgl sampler parameter i
6. ctx = canvas webgl sampler parameter i
   - Expected: canvas_webgl_get_sampler_parameter(ctx, sampler, CANVAS_WEBGL_TEXTURE_MIN_FILTER).int_value equals `CANVAS_WEBGL_LINEAR_MIPMAP_LINEAR`
   - Expected: canvas_webgl_get_sampler_parameter(ctx, sampler, CANVAS_WEBGL_TEXTURE_WRAP_S).int_value equals `CANVAS_WEBGL_CLAMP_TO_EDGE`
   - Expected: ctx.gl.render_commands[0].kind equals `WEBGL_RENDER_COMMAND_BIND_SAMPLER`
   - Expected: ctx.gl.render_commands[2].kind equals `WEBGL_RENDER_COMMAND_SAMPLER_PARAMETER`
7. ctx = canvas webgl delete sampler
   - Expected: canvas_webgl_is_sampler(ctx, sampler) is false
   - Expected: canvas_webgl_get_parameter(ctx, CANVAS_WEBGL_SAMPLER_BINDING).int_value equals `-1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ctx: CanvasWebGLContext = canvas_get_context_webgl2(320, 240)
ctx = canvas_webgl_create_sampler(ctx)
val sampler = canvas_webgl_last_sampler(ctx)
expect(canvas_webgl_is_sampler(ctx, sampler)).to_equal(true)
ctx = canvas_webgl_bind_sampler(ctx, 1, sampler)
ctx = canvas_webgl_active_texture(ctx, CANVAS_WEBGL_TEXTURE0 + 1)
expect(canvas_webgl_get_parameter(ctx, CANVAS_WEBGL_SAMPLER_BINDING).int_value).to_equal(sampler.id)
ctx = canvas_webgl_sampler_parameter_i(ctx, sampler, CANVAS_WEBGL_TEXTURE_MIN_FILTER, CANVAS_WEBGL_LINEAR_MIPMAP_LINEAR)
ctx = canvas_webgl_sampler_parameter_i(ctx, sampler, CANVAS_WEBGL_TEXTURE_WRAP_S, CANVAS_WEBGL_CLAMP_TO_EDGE)
expect(canvas_webgl_get_sampler_parameter(ctx, sampler, CANVAS_WEBGL_TEXTURE_MIN_FILTER).int_value).to_equal(CANVAS_WEBGL_LINEAR_MIPMAP_LINEAR)
expect(canvas_webgl_get_sampler_parameter(ctx, sampler, CANVAS_WEBGL_TEXTURE_WRAP_S).int_value).to_equal(CANVAS_WEBGL_CLAMP_TO_EDGE)
expect(ctx.gl.render_commands[0].kind).to_equal(WEBGL_RENDER_COMMAND_BIND_SAMPLER)
expect(ctx.gl.render_commands[2].kind).to_equal(WEBGL_RENDER_COMMAND_SAMPLER_PARAMETER)
ctx = canvas_webgl_delete_sampler(ctx, sampler)
expect(canvas_webgl_is_sampler(ctx, sampler)).to_equal(false)
expect(canvas_webgl_get_parameter(ctx, CANVAS_WEBGL_SAMPLER_BINDING).int_value).to_equal(-1)
```

</details>

#### uploads a WebGL texture through canvas bridge helpers

1. var ctx: CanvasWebGLContext = canvas get context webgl
2. ctx = canvas webgl create texture
3. ctx = canvas webgl active texture
4. ctx = canvas webgl bind texture
5. ctx = canvas webgl tex parameter i
6. ctx = canvas webgl tex parameter i
7. ctx = canvas webgl tex parameter i
8. ctx = canvas webgl tex parameter i
9. ctx = canvas webgl tex image 2d
   - Expected: canvas_webgl_get_parameter(ctx, CANVAS_WEBGL_ACTIVE_TEXTURE).int_value equals `CANVAS_WEBGL_TEXTURE0 + 1`
   - Expected: canvas_webgl_get_parameter(ctx, CANVAS_WEBGL_TEXTURE_BINDING_2D).int_value equals `tex.id`
   - Expected: ctx.gl.render_commands[0].kind equals `WEBGL_RENDER_COMMAND_ACTIVE_TEXTURE`
   - Expected: ctx.gl.render_commands[0].target equals `CANVAS_WEBGL_TEXTURE0 + 1`
   - Expected: ctx.gl.textures[0].initialized is true
   - Expected: ctx.gl.textures[0].width equals `1`
   - Expected: canvas_webgl_get_tex_parameter(ctx, CANVAS_WEBGL_TEXTURE_2D, CANVAS_WEBGL_TEXTURE_MIN_FILTER).int_value equals `CANVAS_WEBGL_LINEAR_MIPMAP_LINEAR`
   - Expected: canvas_webgl_get_tex_parameter(ctx, CANVAS_WEBGL_TEXTURE_2D, CANVAS_WEBGL_TEXTURE_WRAP_S).int_value equals `CANVAS_WEBGL_CLAMP_TO_EDGE`
   - Expected: canvas_webgl_get_tex_parameter(ctx, CANVAS_WEBGL_TEXTURE_2D, CANVAS_WEBGL_TEXTURE_WRAP_T).int_value equals `CANVAS_WEBGL_MIRRORED_REPEAT`
10. ctx = canvas webgl create texture
11. ctx = canvas webgl bind texture
12. ctx = canvas webgl tex image 2d
   - Expected: canvas_webgl_get_parameter(ctx, CANVAS_WEBGL_TEXTURE_BINDING_CUBE_MAP).int_value equals `cube.id`
   - Expected: ctx.gl.textures[1].target equals `CANVAS_WEBGL_TEXTURE_CUBE_MAP`
13. ctx = canvas webgl tex image 2d
   - Expected: ctx.gl.textures[0].pixel_type equals `CANVAS_WEBGL_UNSIGNED_SHORT_5_6_5`
14. ctx = canvas webgl tex image 2d
   - Expected: ctx.gl.textures[0].pixel_type equals `CANVAS_WEBGL_UNSIGNED_SHORT_4_4_4_4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 29 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ctx: CanvasWebGLContext = canvas_get_context_webgl(320, 240)
ctx = canvas_webgl_create_texture(ctx)
val tex = canvas_webgl_last_texture(ctx)
ctx = canvas_webgl_active_texture(ctx, CANVAS_WEBGL_TEXTURE0 + 1)
ctx = canvas_webgl_bind_texture(ctx, CANVAS_WEBGL_TEXTURE_2D, tex)
ctx = canvas_webgl_tex_parameter_i(ctx, CANVAS_WEBGL_TEXTURE_2D, CANVAS_WEBGL_TEXTURE_MIN_FILTER, CANVAS_WEBGL_LINEAR)
ctx = canvas_webgl_tex_parameter_i(ctx, CANVAS_WEBGL_TEXTURE_2D, CANVAS_WEBGL_TEXTURE_MIN_FILTER, CANVAS_WEBGL_LINEAR_MIPMAP_LINEAR)
ctx = canvas_webgl_tex_parameter_i(ctx, CANVAS_WEBGL_TEXTURE_2D, CANVAS_WEBGL_TEXTURE_WRAP_S, CANVAS_WEBGL_CLAMP_TO_EDGE)
ctx = canvas_webgl_tex_parameter_i(ctx, CANVAS_WEBGL_TEXTURE_2D, CANVAS_WEBGL_TEXTURE_WRAP_T, CANVAS_WEBGL_MIRRORED_REPEAT)
ctx = canvas_webgl_tex_image_2d(ctx, CANVAS_WEBGL_TEXTURE_2D, 0, CANVAS_WEBGL_RGBA, 1, 1, 0, CANVAS_WEBGL_RGBA, CANVAS_WEBGL_UNSIGNED_BYTE, [0xFF, 0x00, 0x00, 0xFF])
expect(canvas_webgl_get_parameter(ctx, CANVAS_WEBGL_ACTIVE_TEXTURE).int_value).to_equal(CANVAS_WEBGL_TEXTURE0 + 1)
expect(canvas_webgl_get_parameter(ctx, CANVAS_WEBGL_TEXTURE_BINDING_2D).int_value).to_equal(tex.id)
expect(ctx.gl.render_commands[0].kind).to_equal(WEBGL_RENDER_COMMAND_ACTIVE_TEXTURE)
expect(ctx.gl.render_commands[0].target).to_equal(CANVAS_WEBGL_TEXTURE0 + 1)
expect(ctx.gl.textures[0].initialized).to_equal(true)
expect(ctx.gl.textures[0].width).to_equal(1)
expect(canvas_webgl_get_tex_parameter(ctx, CANVAS_WEBGL_TEXTURE_2D, CANVAS_WEBGL_TEXTURE_MIN_FILTER).int_value).to_equal(CANVAS_WEBGL_LINEAR_MIPMAP_LINEAR)
expect(canvas_webgl_get_tex_parameter(ctx, CANVAS_WEBGL_TEXTURE_2D, CANVAS_WEBGL_TEXTURE_WRAP_S).int_value).to_equal(CANVAS_WEBGL_CLAMP_TO_EDGE)
expect(canvas_webgl_get_tex_parameter(ctx, CANVAS_WEBGL_TEXTURE_2D, CANVAS_WEBGL_TEXTURE_WRAP_T).int_value).to_equal(CANVAS_WEBGL_MIRRORED_REPEAT)
ctx = canvas_webgl_create_texture(ctx)
val cube = canvas_webgl_last_texture(ctx)
ctx = canvas_webgl_bind_texture(ctx, CANVAS_WEBGL_TEXTURE_CUBE_MAP, cube)
ctx = canvas_webgl_tex_image_2d(ctx, CANVAS_WEBGL_TEXTURE_CUBE_MAP_POSITIVE_X, 0, CANVAS_WEBGL_RGBA, 1, 1, 0, CANVAS_WEBGL_RGBA, CANVAS_WEBGL_UNSIGNED_BYTE, [0xFF, 0x00, 0x00, 0xFF])
expect(canvas_webgl_get_parameter(ctx, CANVAS_WEBGL_TEXTURE_BINDING_CUBE_MAP).int_value).to_equal(cube.id)
expect(ctx.gl.textures[1].target).to_equal(CANVAS_WEBGL_TEXTURE_CUBE_MAP)
ctx = canvas_webgl_tex_image_2d(ctx, CANVAS_WEBGL_TEXTURE_2D, 0, CANVAS_WEBGL_RGB, 2, 1, 0, CANVAS_WEBGL_RGB, CANVAS_WEBGL_UNSIGNED_SHORT_5_6_5, [1, 2, 3, 4])
expect(ctx.gl.textures[0].pixel_type).to_equal(CANVAS_WEBGL_UNSIGNED_SHORT_5_6_5)
ctx = canvas_webgl_tex_image_2d(ctx, CANVAS_WEBGL_TEXTURE_2D, 0, CANVAS_WEBGL_RGBA, 2, 1, 0, CANVAS_WEBGL_RGBA, CANVAS_WEBGL_UNSIGNED_SHORT_4_4_4_4, [5, 6, 7, 8])
expect(ctx.gl.textures[0].pixel_type).to_equal(CANVAS_WEBGL_UNSIGNED_SHORT_4_4_4_4)
```

</details>

#### bridges WebGL texture sub image and mipmap helpers

1. var ctx: CanvasWebGLContext = canvas get context webgl
2. ctx = canvas webgl create texture
3. ctx = canvas webgl bind texture
4. ctx = canvas webgl tex image 2d
5. ctx = canvas webgl tex sub image 2d
   - Expected: ctx.gl.textures[0].pixels[4] equals `9`
6. ctx = canvas webgl generate mipmap
   - Expected: ctx.gl.textures[0].mipmap_generated is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ctx: CanvasWebGLContext = canvas_get_context_webgl(320, 240)
ctx = canvas_webgl_create_texture(ctx)
val tex = canvas_webgl_last_texture(ctx)
ctx = canvas_webgl_bind_texture(ctx, CANVAS_WEBGL_TEXTURE_2D, tex)
ctx = canvas_webgl_tex_image_2d(ctx, CANVAS_WEBGL_TEXTURE_2D, 0, CANVAS_WEBGL_RGBA, 2, 2, 0, CANVAS_WEBGL_RGBA, CANVAS_WEBGL_UNSIGNED_BYTE, [0, 0, 0, 255, 1, 1, 1, 255, 2, 2, 2, 255, 3, 3, 3, 255])
ctx = canvas_webgl_tex_sub_image_2d(ctx, CANVAS_WEBGL_TEXTURE_2D, 0, 1, 0, 1, 1, CANVAS_WEBGL_RGBA, CANVAS_WEBGL_UNSIGNED_BYTE, [9, 8, 7, 6])
expect(ctx.gl.textures[0].pixels[4]).to_equal(9)
ctx = canvas_webgl_generate_mipmap(ctx, CANVAS_WEBGL_TEXTURE_2D)
expect(ctx.gl.textures[0].mipmap_generated).to_equal(true)
```

</details>

#### rejects unsupported WebGL compressed texture uploads

1. var ctx: CanvasWebGLContext = canvas get context webgl
2. ctx = canvas webgl create texture
3. ctx = canvas webgl bind texture
   - Expected: canvas_webgl_get_parameter(ctx, CANVAS_WEBGL_COMPRESSED_TEXTURE_FORMATS).int_values.len() equals `0`
4. ctx = canvas webgl compressed tex image 2d
   - Expected: canvas_webgl_get_error(ctx) equals `CANVAS_WEBGL_INVALID_ENUM`
   - Expected: ctx.gl.textures[0].initialized is false
5. ctx = canvas webgl tex image 2d
6. ctx = canvas webgl compressed tex sub image 2d
   - Expected: canvas_webgl_get_error(ctx) equals `CANVAS_WEBGL_INVALID_ENUM`
   - Expected: ctx.gl.textures[0].pixels[0] equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ctx: CanvasWebGLContext = canvas_get_context_webgl(320, 240)
ctx = canvas_webgl_create_texture(ctx)
val tex = canvas_webgl_last_texture(ctx)
ctx = canvas_webgl_bind_texture(ctx, CANVAS_WEBGL_TEXTURE_2D, tex)
expect(canvas_webgl_get_parameter(ctx, CANVAS_WEBGL_COMPRESSED_TEXTURE_FORMATS).int_values.len()).to_equal(0)
ctx = canvas_webgl_compressed_tex_image_2d(ctx, CANVAS_WEBGL_TEXTURE_2D, 0, CANVAS_WEBGL_RGBA, 2, 2, 0, [1, 2, 3, 4])
expect(canvas_webgl_get_error(ctx)).to_equal(CANVAS_WEBGL_INVALID_ENUM)
expect(ctx.gl.textures[0].initialized).to_equal(false)
ctx = canvas_webgl_tex_image_2d(ctx, CANVAS_WEBGL_TEXTURE_2D, 0, CANVAS_WEBGL_RGBA, 2, 2, 0, CANVAS_WEBGL_RGBA, CANVAS_WEBGL_UNSIGNED_BYTE, [0, 0, 0, 255, 1, 1, 1, 255, 2, 2, 2, 255, 3, 3, 3, 255])
ctx = canvas_webgl_compressed_tex_sub_image_2d(ctx, CANVAS_WEBGL_TEXTURE_2D, 0, 0, 0, 1, 1, CANVAS_WEBGL_RGBA, [9, 8, 7, 6])
expect(canvas_webgl_get_error(ctx)).to_equal(CANVAS_WEBGL_INVALID_ENUM)
expect(ctx.gl.textures[0].pixels[0]).to_equal(0)
```

</details>

#### bridges WebGL framebuffer copy texture helpers

1. var ctx: CanvasWebGLContext = canvas get context webgl
2. ctx = canvas webgl create texture
3. ctx = canvas webgl bind texture
4. ctx = canvas webgl copy tex image 2d
   - Expected: ctx.gl.textures[0].initialized is true
   - Expected: ctx.gl.textures[0].width equals `2`
   - Expected: ctx.gl.textures[0].pixels.len() equals `16`
   - Expected: ctx.gl.render_commands[1].kind equals `WEBGL_RENDER_COMMAND_COPY_TEX_IMAGE_2D`
   - Expected: ctx.gl.render_commands[1].x equals `4`
   - Expected: ctx.gl.render_commands[1].y equals `5`
5. ctx = canvas webgl copy tex sub image 2d
   - Expected: ctx.gl.textures[0].pixels[12] equals `0`
   - Expected: ctx.gl.render_commands[2].kind equals `WEBGL_RENDER_COMMAND_COPY_TEX_SUB_IMAGE_2D`
   - Expected: ctx.gl.render_commands[2].x equals `1`
   - Expected: ctx.gl.render_commands[2].first equals `8`
   - Expected: ctx.gl.render_commands[2].count equals `9`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ctx: CanvasWebGLContext = canvas_get_context_webgl(320, 240)
ctx = canvas_webgl_create_texture(ctx)
val tex = canvas_webgl_last_texture(ctx)
ctx = canvas_webgl_bind_texture(ctx, CANVAS_WEBGL_TEXTURE_2D, tex)
ctx = canvas_webgl_copy_tex_image_2d(ctx, CANVAS_WEBGL_TEXTURE_2D, 0, CANVAS_WEBGL_RGBA, 4, 5, 2, 2, 0)
expect(ctx.gl.textures[0].initialized).to_equal(true)
expect(ctx.gl.textures[0].width).to_equal(2)
expect(ctx.gl.textures[0].pixels.len()).to_equal(16)
expect(ctx.gl.render_commands[1].kind).to_equal(WEBGL_RENDER_COMMAND_COPY_TEX_IMAGE_2D)
expect(ctx.gl.render_commands[1].x).to_equal(4)
expect(ctx.gl.render_commands[1].y).to_equal(5)
ctx = canvas_webgl_copy_tex_sub_image_2d(ctx, CANVAS_WEBGL_TEXTURE_2D, 0, 1, 1, 8, 9, 1, 1)
expect(ctx.gl.textures[0].pixels[12]).to_equal(0)
expect(ctx.gl.render_commands[2].kind).to_equal(WEBGL_RENDER_COMMAND_COPY_TEX_SUB_IMAGE_2D)
expect(ctx.gl.render_commands[2].x).to_equal(1)
expect(ctx.gl.render_commands[2].first).to_equal(8)
expect(ctx.gl.render_commands[2].count).to_equal(9)
```

</details>

#### bridges WebGL framebuffer texture attachments

1. var ctx: CanvasWebGLContext = canvas get context webgl
2. ctx = canvas webgl create texture
3. ctx = canvas webgl bind texture
4. ctx = canvas webgl tex image 2d
5. ctx = canvas webgl create framebuffer
6. ctx = canvas webgl bind framebuffer
   - Expected: canvas_webgl_check_framebuffer_status(ctx, CANVAS_WEBGL_FRAMEBUFFER) equals `CANVAS_WEBGL_FRAMEBUFFER_INCOMPLETE_MISSING_ATTACHMENT`
7. ctx = canvas webgl framebuffer texture 2d
   - Expected: canvas_webgl_check_framebuffer_status(ctx, CANVAS_WEBGL_FRAMEBUFFER) equals `CANVAS_WEBGL_FRAMEBUFFER_COMPLETE`
   - Expected: canvas_webgl_get_framebuffer_attachment_parameter(ctx, CANVAS_WEBGL_FRAMEBUFFER, CANVAS_WEBGL_COLOR_ATTACHMENT0, CANVAS_WEBGL_FRAMEBUFFER_ATTACHMENT_OBJECT_TYPE).int_value equals `CANVAS_WEBGL_TEXTURE`
   - Expected: canvas_webgl_get_framebuffer_attachment_parameter(ctx, CANVAS_WEBGL_FRAMEBUFFER, CANVAS_WEBGL_COLOR_ATTACHMENT0, CANVAS_WEBGL_FRAMEBUFFER_ATTACHMENT_OBJECT_NAME).int_value equals `tex.id`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ctx: CanvasWebGLContext = canvas_get_context_webgl(320, 240)
ctx = canvas_webgl_create_texture(ctx)
val tex = canvas_webgl_last_texture(ctx)
ctx = canvas_webgl_bind_texture(ctx, CANVAS_WEBGL_TEXTURE_2D, tex)
ctx = canvas_webgl_tex_image_2d(ctx, CANVAS_WEBGL_TEXTURE_2D, 0, CANVAS_WEBGL_RGBA, 1, 1, 0, CANVAS_WEBGL_RGBA, CANVAS_WEBGL_UNSIGNED_BYTE, [0x00, 0x00, 0x00, 0xFF])
ctx = canvas_webgl_create_framebuffer(ctx)
val fb = canvas_webgl_last_framebuffer(ctx)
ctx = canvas_webgl_bind_framebuffer(ctx, CANVAS_WEBGL_FRAMEBUFFER, fb)
expect(canvas_webgl_check_framebuffer_status(ctx, CANVAS_WEBGL_FRAMEBUFFER)).to_equal(CANVAS_WEBGL_FRAMEBUFFER_INCOMPLETE_MISSING_ATTACHMENT)
ctx = canvas_webgl_framebuffer_texture_2d(ctx, CANVAS_WEBGL_FRAMEBUFFER, CANVAS_WEBGL_COLOR_ATTACHMENT0, CANVAS_WEBGL_TEXTURE_2D, tex, 0)
expect(canvas_webgl_check_framebuffer_status(ctx, CANVAS_WEBGL_FRAMEBUFFER)).to_equal(CANVAS_WEBGL_FRAMEBUFFER_COMPLETE)
expect(canvas_webgl_get_framebuffer_attachment_parameter(ctx, CANVAS_WEBGL_FRAMEBUFFER, CANVAS_WEBGL_COLOR_ATTACHMENT0, CANVAS_WEBGL_FRAMEBUFFER_ATTACHMENT_OBJECT_TYPE).int_value).to_equal(CANVAS_WEBGL_TEXTURE)
expect(canvas_webgl_get_framebuffer_attachment_parameter(ctx, CANVAS_WEBGL_FRAMEBUFFER, CANVAS_WEBGL_COLOR_ATTACHMENT0, CANVAS_WEBGL_FRAMEBUFFER_ATTACHMENT_OBJECT_NAME).int_value).to_equal(tex.id)
```

</details>

#### bridges WebGL renderbuffer storage and attachments

1. var ctx: CanvasWebGLContext = canvas get context webgl
2. ctx = canvas webgl create framebuffer
3. ctx = canvas webgl bind framebuffer
4. ctx = canvas webgl create renderbuffer
5. ctx = canvas webgl bind renderbuffer
6. ctx = canvas webgl renderbuffer storage
   - Expected: canvas_webgl_get_renderbuffer_parameter(ctx, CANVAS_WEBGL_RENDERBUFFER, CANVAS_WEBGL_RENDERBUFFER_WIDTH).int_value equals `16`
   - Expected: canvas_webgl_get_renderbuffer_parameter(ctx, CANVAS_WEBGL_RENDERBUFFER, CANVAS_WEBGL_RENDERBUFFER_HEIGHT).int_value equals `16`
   - Expected: canvas_webgl_get_renderbuffer_parameter(ctx, CANVAS_WEBGL_RENDERBUFFER, CANVAS_WEBGL_RENDERBUFFER_INTERNAL_FORMAT).int_value equals `CANVAS_WEBGL_RGBA4`
7. ctx = canvas webgl framebuffer renderbuffer
   - Expected: canvas_webgl_check_framebuffer_status(ctx, CANVAS_WEBGL_FRAMEBUFFER) equals `CANVAS_WEBGL_FRAMEBUFFER_COMPLETE`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ctx: CanvasWebGLContext = canvas_get_context_webgl(320, 240)
ctx = canvas_webgl_create_framebuffer(ctx)
val fb = canvas_webgl_last_framebuffer(ctx)
ctx = canvas_webgl_bind_framebuffer(ctx, CANVAS_WEBGL_FRAMEBUFFER, fb)
ctx = canvas_webgl_create_renderbuffer(ctx)
val rb = canvas_webgl_last_renderbuffer(ctx)
ctx = canvas_webgl_bind_renderbuffer(ctx, CANVAS_WEBGL_RENDERBUFFER, rb)
ctx = canvas_webgl_renderbuffer_storage(ctx, CANVAS_WEBGL_RENDERBUFFER, CANVAS_WEBGL_RGBA4, 16, 16)
expect(canvas_webgl_get_renderbuffer_parameter(ctx, CANVAS_WEBGL_RENDERBUFFER, CANVAS_WEBGL_RENDERBUFFER_WIDTH).int_value).to_equal(16)
expect(canvas_webgl_get_renderbuffer_parameter(ctx, CANVAS_WEBGL_RENDERBUFFER, CANVAS_WEBGL_RENDERBUFFER_HEIGHT).int_value).to_equal(16)
expect(canvas_webgl_get_renderbuffer_parameter(ctx, CANVAS_WEBGL_RENDERBUFFER, CANVAS_WEBGL_RENDERBUFFER_INTERNAL_FORMAT).int_value).to_equal(CANVAS_WEBGL_RGBA4)
ctx = canvas_webgl_framebuffer_renderbuffer(ctx, CANVAS_WEBGL_FRAMEBUFFER, CANVAS_WEBGL_COLOR_ATTACHMENT0, CANVAS_WEBGL_RENDERBUFFER, rb)
expect(canvas_webgl_check_framebuffer_status(ctx, CANVAS_WEBGL_FRAMEBUFFER)).to_equal(CANVAS_WEBGL_FRAMEBUFFER_COMPLETE)
```

</details>

#### bridges WebGL2 draw buffer state

1. var ctx: CanvasWebGLContext = canvas get context webgl2
   - Expected: canvas_webgl_get_parameter(ctx, CANVAS_WEBGL_MAX_DRAW_BUFFERS).int_value equals `1`
2. ctx = canvas webgl draw buffers
   - Expected: canvas_webgl_get_parameter(ctx, CANVAS_WEBGL_DRAW_BUFFER0).int_value equals `CANVAS_WEBGL_NONE`
3. ctx = canvas webgl read buffer
   - Expected: canvas_webgl_get_parameter(ctx, CANVAS_WEBGL_READ_BUFFER).int_value equals `CANVAS_WEBGL_NONE`
4. ctx = canvas webgl create framebuffer
5. ctx = canvas webgl bind framebuffer
6. ctx = canvas webgl draw buffers
7. ctx = canvas webgl read buffer
   - Expected: canvas_webgl_get_parameter(ctx, CANVAS_WEBGL_DRAW_BUFFER0).int_value equals `CANVAS_WEBGL_COLOR_ATTACHMENT0`
   - Expected: canvas_webgl_get_parameter(ctx, CANVAS_WEBGL_READ_BUFFER).int_value equals `CANVAS_WEBGL_COLOR_ATTACHMENT0`
   - Expected: ctx.gl.render_commands[3].kind equals `WEBGL_RENDER_COMMAND_DRAW_BUFFERS`
   - Expected: ctx.gl.render_commands[3].int_values[0] equals `CANVAS_WEBGL_COLOR_ATTACHMENT0`
   - Expected: ctx.gl.render_commands[4].kind equals `WEBGL_RENDER_COMMAND_READ_BUFFER`
   - Expected: ctx.gl.render_commands[4].target equals `CANVAS_WEBGL_COLOR_ATTACHMENT0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ctx: CanvasWebGLContext = canvas_get_context_webgl2(320, 240)
expect(canvas_webgl_get_parameter(ctx, CANVAS_WEBGL_MAX_DRAW_BUFFERS).int_value).to_equal(1)
ctx = canvas_webgl_draw_buffers(ctx, [CANVAS_WEBGL_NONE])
expect(canvas_webgl_get_parameter(ctx, CANVAS_WEBGL_DRAW_BUFFER0).int_value).to_equal(CANVAS_WEBGL_NONE)
ctx = canvas_webgl_read_buffer(ctx, CANVAS_WEBGL_NONE)
expect(canvas_webgl_get_parameter(ctx, CANVAS_WEBGL_READ_BUFFER).int_value).to_equal(CANVAS_WEBGL_NONE)
ctx = canvas_webgl_create_framebuffer(ctx)
val fb = canvas_webgl_last_framebuffer(ctx)
ctx = canvas_webgl_bind_framebuffer(ctx, CANVAS_WEBGL_FRAMEBUFFER, fb)
ctx = canvas_webgl_draw_buffers(ctx, [CANVAS_WEBGL_COLOR_ATTACHMENT0])
ctx = canvas_webgl_read_buffer(ctx, CANVAS_WEBGL_COLOR_ATTACHMENT0)
expect(canvas_webgl_get_parameter(ctx, CANVAS_WEBGL_DRAW_BUFFER0).int_value).to_equal(CANVAS_WEBGL_COLOR_ATTACHMENT0)
expect(canvas_webgl_get_parameter(ctx, CANVAS_WEBGL_READ_BUFFER).int_value).to_equal(CANVAS_WEBGL_COLOR_ATTACHMENT0)
expect(ctx.gl.render_commands[3].kind).to_equal(WEBGL_RENDER_COMMAND_DRAW_BUFFERS)
expect(ctx.gl.render_commands[3].int_values[0]).to_equal(CANVAS_WEBGL_COLOR_ATTACHMENT0)
expect(ctx.gl.render_commands[4].kind).to_equal(WEBGL_RENDER_COMMAND_READ_BUFFER)
expect(ctx.gl.render_commands[4].target).to_equal(CANVAS_WEBGL_COLOR_ATTACHMENT0)
```

</details>

#### does not expose WebGPU from insecure canvas

1. var ctx = canvas get context webgpu
   - Expected: ctx.context_type equals `webgpu`
   - Expected: ctx.is_available() is false
   - Expected: ctx.request_device() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ctx = canvas_get_context_webgpu(320, 240, false)
expect(ctx.context_type).to_equal("webgpu")
expect(ctx.is_available()).to_equal(false)
expect(ctx.request_device()).to_equal(false)
```

</details>

#### configures secure WebGPU canvas

1. var ctx = canvas get context webgpu
   - Expected: ctx.is_available() is true
   - Expected: ctx.request_device() is true
   - Expected: ctx.configure() is true
   - Expected: ctx.gpu.canvas_configured is true
   - Expected: ctx.gpu.canvas_config.width equals `320`
   - Expected: ctx.gpu.canvas_config.alpha_mode equals `opaque`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ctx = canvas_get_context_webgpu(320, 240, true)
expect(ctx.is_available()).to_equal(true)
expect(ctx.request_device()).to_equal(true)
expect(ctx.configure()).to_equal(true)
expect(ctx.gpu.canvas_configured).to_equal(true)
expect(ctx.gpu.canvas_config.width).to_equal(320)
expect(ctx.gpu.canvas_config.alpha_mode).to_equal("opaque")
```

</details>

#### configures alpha mode and presents WebGPU canvas frames

1. var ctx = canvas get context webgpu
   - Expected: ctx.request_device() is true
   - Expected: ctx.configure_with_alpha("premultiplied") is true
   - Expected: ctx.gpu.canvas_config.alpha_mode equals `premultiplied`
   - Expected: ctx.present() is true
   - Expected: ctx.gpu.present_count equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ctx = canvas_get_context_webgpu(320, 240, true)
expect(ctx.request_device()).to_equal(true)
expect(ctx.configure_with_alpha("premultiplied")).to_equal(true)
expect(ctx.gpu.canvas_config.alpha_mode).to_equal("premultiplied")
expect(ctx.present()).to_equal(true)
expect(ctx.gpu.present_count).to_equal(1)
```

</details>

#### creates render and compute pipelines through canvas WebGPU context

1. var ctx = canvas get context webgpu
   - Expected: ctx.request_device() is true
   - Expected: ctx.configure() is true
   - Expected: rp.valid is true
   - Expected: cp.valid is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ctx = canvas_get_context_webgpu(320, 240, true)
expect(ctx.request_device()).to_equal(true)
expect(ctx.configure()).to_equal(true)
val vs = ctx.create_shader_module("vs", "@vertex fn main() -> @builtin(position) vec4f { return vec4f(0.0, 0.0, 0.0, 1.0); }")
val fs = ctx.create_shader_module("fs", "@fragment fn main() -> @location(0) vec4f { return vec4f(0.0, 1.0, 0.0, 1.0); }")
val cs = ctx.create_shader_module("cs", "@compute @workgroup_size(1) fn main() { }")
val rp = ctx.create_render_pipeline(vs, fs)
val cp = ctx.create_compute_pipeline(cs)
expect(rp.valid).to_equal(true)
expect(cp.valid).to_equal(true)
```

</details>

#### creates auto-layout render pipelines through canvas WebGPU context

1. var ctx = canvas get context webgpu
   - Expected: ctx.request_device() is true
   - Expected: ctx.configure() is true
   - Expected: rp.valid is true
   - Expected: ctx.gpu.resources.bind_group_layouts.len() equals `1`
   - Expected: ctx.gpu.resources.bind_group_layouts[0].entries.len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ctx = canvas_get_context_webgpu(320, 240, true)
expect(ctx.request_device()).to_equal(true)
expect(ctx.configure()).to_equal(true)
val vs = ctx.create_shader_module("vs", "@vertex fn main() -> @builtin(position) vec4f { return vec4f(0.0, 0.0, 0.0, 1.0); }\n@group(0) @binding(0) var<uniform> camera: mat4x4f;")
val fs = ctx.create_shader_module("fs", "@fragment fn main() -> @location(0) vec4f { return vec4f(0.0, 1.0, 0.0, 1.0); }\n@group(0) @binding(1) var diffuse: texture_2d<f32>;")
val rp = ctx.create_render_pipeline_auto_layout(vs, fs)
expect(rp.valid).to_equal(true)
expect(ctx.gpu.resources.bind_group_layouts.len()).to_equal(1)
expect(ctx.gpu.resources.bind_group_layouts[0].entries.len()).to_equal(2)
```

</details>

#### exposes WebGPU shader diagnostics through canvas wrappers

1. var ctx = canvas get context webgpu
   - Expected: ctx.request_device() is true
   - Expected: module.valid is false
   - Expected: direct.line equals `2`
   - Expected: direct.stage equals `fragment`
   - Expected: diagnostic.message equals `module.error`
   - Expected: diagnostic.formatted() equals `error: WGSL fragment shader line 2:1: WGSL fragment stage must declare @locat... (full value in folded executable source)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ctx = canvas_get_context_webgpu(320, 240, true)
expect(ctx.request_device()).to_equal(true)
val source = "// prelude\n@fragment fn main() -> vec4f { return vec4f(1.0); }"
val direct = ctx.diagnose_wgsl(source)
val module = ctx.create_shader_module("bad-fragment", source)
val diagnostic = ctx.shader_module_diagnostic(module)
expect(module.valid).to_equal(false)
expect(direct.line).to_equal(2)
expect(direct.stage).to_equal("fragment")
expect(diagnostic.message).to_equal(module.error)
expect(diagnostic.formatted()).to_equal("error: WGSL fragment shader line 2:1: WGSL fragment stage must declare @location(0) output")
```

</details>

#### records and submits WebGPU commands through canvas wrappers

1. var ctx = canvas get context webgpu
   - Expected: ctx.request_device() is true
   - Expected: ctx.configure() is true
2. var encoder = ctx create command encoder
   - Expected: encoder.begin_render_pass() is true
   - Expected: encoder.set_pipeline(pipeline.id) is true
   - Expected: encoder.draw(3, 1) is true
   - Expected: encoder.end_render_pass() is true
   - Expected: ctx.queue_submit([command_buffer]) is true
   - Expected: ctx.gpu.queue.submitted_count() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ctx = canvas_get_context_webgpu(320, 240, true)
expect(ctx.request_device()).to_equal(true)
expect(ctx.configure()).to_equal(true)
val vs = ctx.create_shader_module("vs", "@vertex fn main() -> @builtin(position) vec4f { return vec4f(0.0, 0.0, 0.0, 1.0); }")
val fs = ctx.create_shader_module("fs", "@fragment fn main() -> @location(0) vec4f { return vec4f(1.0, 0.0, 0.0, 1.0); }")
val pipeline = ctx.create_render_pipeline(vs, fs)
var encoder = ctx.create_command_encoder("frame")
expect(encoder.begin_render_pass()).to_equal(true)
expect(encoder.set_pipeline(pipeline.id)).to_equal(true)
expect(encoder.draw(3, 1)).to_equal(true)
expect(encoder.end_render_pass()).to_equal(true)
val command_buffer = encoder.finish("frame-commands")
expect(ctx.queue_submit([command_buffer])).to_equal(true)
expect(ctx.gpu.queue.submitted_count()).to_equal(1)
```

</details>

#### records WebGPU bind groups through resource-aware canvas command encoders

1. var ctx = canvas get context webgpu
   - Expected: ctx.request_device() is true
2. GPUBindGroupLayoutEntry dynamic buffer
3. GPUBindGroupEntry buffer
4. var encoder = gpu ctx create command encoder
   - Expected: encoder.begin_render_pass() is true
   - Expected: encoder.set_bind_group_with_dynamic_offsets_and_resources(gpu_ctx.resources, 0, bind_group.id, [256]) is true
   - Expected: encoder.set_bind_group_with_dynamic_offsets_and_resources(gpu_ctx.resources, 0, bind_group.id, [512]) is false
   - Expected: encoder.last_error equals `GPUPassEncoder dynamic offset exceeds buffer size`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ctx = canvas_get_context_webgpu(320, 240, true)
expect(ctx.request_device()).to_equal(true)
var gpu_ctx: WebGPUContext = ctx.gpu
var resources = gpu_ctx.resources
val uniform = resources.create_buffer("uniforms", 512, WEBGPU_BUFFER_USAGE_UNIFORM)
val layout = resources.create_bind_group_layout("dynamic", [
    GPUBindGroupLayoutEntry.dynamic_buffer(0, WEBGPU_SHADER_STAGE_VERTEX)
])
val bind_group = resources.create_bind_group("dynamic-0", layout.id, [
    GPUBindGroupEntry.buffer(0, uniform.id)
])
gpu_ctx.resources = resources
var encoder = gpu_ctx.create_command_encoder("frame")
expect(encoder.begin_render_pass()).to_equal(true)
expect(encoder.set_bind_group_with_dynamic_offsets_and_resources(gpu_ctx.resources, 0, bind_group.id, [256])).to_equal(true)
expect(encoder.set_bind_group_with_dynamic_offsets_and_resources(gpu_ctx.resources, 0, bind_group.id, [512])).to_equal(false)
expect(encoder.last_error).to_equal("GPUPassEncoder dynamic offset exceeds buffer size")
```

</details>

#### creates WebGPU resources and queue writes through canvas wrappers

1. var ctx = canvas get context webgpu
   - Expected: ctx.request_device() is true
   - Expected: buffer.valid is true
   - Expected: ctx.queue_write_buffer(buffer.id, 0, 32) is true
   - Expected: ctx.gpu.queue.write_count() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ctx = canvas_get_context_webgpu(320, 240, true)
expect(ctx.request_device()).to_equal(true)
val buffer = ctx.create_buffer("upload", 64, WEBGPU_BUFFER_USAGE_COPY_DST)
expect(buffer.valid).to_equal(true)
expect(ctx.queue_write_buffer(buffer.id, 0, 32)).to_equal(true)
expect(ctx.gpu.queue.write_count()).to_equal(1)
```

</details>

#### creates dimension-aware WebGPU textures through canvas wrappers

1. var ctx = canvas get context webgpu
   - Expected: ctx.request_device() is true
   - Expected: texture.valid is true
   - Expected: texture.depth_or_layers equals `4`
   - Expected: ctx.gpu.resources.textures.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ctx = canvas_get_context_webgpu(320, 240, true)
expect(ctx.request_device()).to_equal(true)
val texture = ctx.create_texture_with_dimension("volume", 8, 8, 4, GPU_TEXTURE_FORMAT_RGBA8_UNORM, WEBGPU_TEXTURE_USAGE_COPY_DST, WEBGPU_TEXTURE_DIMENSION_3D)
expect(texture.valid).to_equal(true)
expect(texture.depth_or_layers).to_equal(4)
expect(ctx.gpu.resources.textures.len()).to_equal(1)
```

</details>

#### creates mip-level WebGPU textures through canvas wrappers

1. var ctx = canvas get context webgpu
   - Expected: ctx.request_device() is true
   - Expected: texture.valid is true
   - Expected: texture.mip_level_count equals `4`
   - Expected: ctx.gpu.resources.textures.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ctx = canvas_get_context_webgpu(320, 240, true)
expect(ctx.request_device()).to_equal(true)
val texture = ctx.create_texture_with_mip_levels("mip-volume", 8, 8, 4, GPU_TEXTURE_FORMAT_RGBA8_UNORM, WEBGPU_TEXTURE_USAGE_COPY_DST, WEBGPU_TEXTURE_DIMENSION_3D, 4)
expect(texture.valid).to_equal(true)
expect(texture.mip_level_count).to_equal(4)
expect(ctx.gpu.resources.textures.len()).to_equal(1)
```

</details>

#### creates descriptor WebGPU textures with sample counts through canvas wrappers

1. var ctx = canvas get context webgpu
   - Expected: ctx.request_device() is true
   - Expected: texture.valid is true
   - Expected: texture.sample_count equals `4`
   - Expected: texture.mip_level_count equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ctx = canvas_get_context_webgpu(320, 240, true)
expect(ctx.request_device()).to_equal(true)
val texture = ctx.create_texture_with_descriptor("msaa-color", 320, 240, 1, GPU_TEXTURE_FORMAT_RGBA8_UNORM, WEBGPU_TEXTURE_USAGE_RENDER_ATTACHMENT, WEBGPU_TEXTURE_DIMENSION_2D, 1, 4)
expect(texture.valid).to_equal(true)
expect(texture.sample_count).to_equal(4)
expect(texture.mip_level_count).to_equal(1)
```

</details>

#### creates depth stencil WebGPU textures through canvas wrappers

1. var ctx = canvas get context webgpu
   - Expected: ctx.request_device() is true
   - Expected: texture.valid is true
   - Expected: texture.format equals `GPU_TEXTURE_FORMAT_DEPTH24_PLUS_STENCIL8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ctx = canvas_get_context_webgpu(320, 240, true)
expect(ctx.request_device()).to_equal(true)
val texture = ctx.create_texture_with_descriptor("depth-stencil", 320, 240, 1, CANVAS_WEBGPU_TEXTURE_FORMAT_DEPTH24_PLUS_STENCIL8, CANVAS_WEBGPU_TEXTURE_USAGE_RENDER_ATTACHMENT, CANVAS_WEBGPU_TEXTURE_DIMENSION_2D, 1, 1)
expect(texture.valid).to_equal(true)
expect(texture.format).to_equal(GPU_TEXTURE_FORMAT_DEPTH24_PLUS_STENCIL8)
```

</details>

#### creates WebGPU texture views through canvas wrappers

1. var ctx = canvas get context webgpu
   - Expected: ctx.request_device() is true
   - Expected: view.valid is true
   - Expected: view.texture_id equals `texture.id`
   - Expected: view.dimension equals `WEBGPU_TEXTURE_DIMENSION_3D`
   - Expected: ctx.gpu.resources.texture_views.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ctx = canvas_get_context_webgpu(320, 240, true)
expect(ctx.request_device()).to_equal(true)
val texture = ctx.create_texture_with_dimension("volume", 8, 8, 4, GPU_TEXTURE_FORMAT_RGBA8_UNORM, WEBGPU_TEXTURE_USAGE_COPY_DST, WEBGPU_TEXTURE_DIMENSION_3D)
val view = ctx.create_texture_view("volume-view", texture.id, "", WEBGPU_TEXTURE_DIMENSION_3D, 0, 1, 0, 4)
expect(view.valid).to_equal(true)
expect(view.texture_id).to_equal(texture.id)
expect(view.dimension).to_equal(WEBGPU_TEXTURE_DIMENSION_3D)
expect(ctx.gpu.resources.texture_views.len()).to_equal(1)
```

</details>

#### creates descriptor-complete WebGPU samplers through canvas wrappers

1. var ctx = canvas get context webgpu
   - Expected: ctx.request_device() is true
   - Expected: sampler.valid is true
   - Expected: sampler.address_mode_w equals `clamp-to-edge`
   - Expected: sampler.mipmap_filter equals `linear`
   - Expected: sampler.compare equals `less-equal`
   - Expected: sampler.max_anisotropy equals `4`
   - Expected: ctx.gpu.resources.samplers.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ctx = canvas_get_context_webgpu(320, 240, true)
expect(ctx.request_device()).to_equal(true)
val sampler = ctx.create_sampler_with_descriptor("shadow", "repeat", "mirror-repeat", "clamp-to-edge", "linear", "linear", "linear", 1.0, 8.0, "less-equal", 4)
expect(sampler.valid).to_equal(true)
expect(sampler.address_mode_w).to_equal("clamp-to-edge")
expect(sampler.mipmap_filter).to_equal("linear")
expect(sampler.compare).to_equal("less-equal")
expect(sampler.max_anisotropy).to_equal(4)
expect(ctx.gpu.resources.samplers.len()).to_equal(1)
```

</details>

#### creates WebGPU bind group resources through canvas wrappers

1. var ctx = canvas get context webgpu
   - Expected: ctx.request_device() is true
2. GPUBindGroupLayoutEntry buffer
3. GPUBindGroupEntry buffer
   - Expected: layout.valid is true
   - Expected: bind_group.valid is true
   - Expected: ctx.gpu.resources.bind_group_layouts.len() equals `1`
   - Expected: ctx.gpu.resources.bind_groups.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ctx = canvas_get_context_webgpu(320, 240, true)
expect(ctx.request_device()).to_equal(true)
val buffer = ctx.create_buffer("uniforms", 256, WEBGPU_BUFFER_USAGE_UNIFORM)
val layout = ctx.create_bind_group_layout("material", [
    GPUBindGroupLayoutEntry.buffer(0, WEBGPU_SHADER_STAGE_VERTEX)
])
val bind_group = ctx.create_bind_group("material-0", layout.id, [
    GPUBindGroupEntry.buffer(0, buffer.id)
])
expect(layout.valid).to_equal(true)
expect(bind_group.valid).to_equal(true)
expect(ctx.gpu.resources.bind_group_layouts.len()).to_equal(1)
expect(ctx.gpu.resources.bind_groups.len()).to_equal(1)
```

</details>

#### executes secure canvas WebGPU compute upload through software executor

1. var ctx = canvas get context webgpu
   - Expected: ctx.request_device() is true
   - Expected: ctx.configure() is true
   - Expected: gpu_ctx.queue_write_buffer(buffer.id, 0, 32) is true
2. var encoder = gpu ctx create command encoder
   - Expected: encoder.begin_compute_pass() is true
   - Expected: encoder.set_pipeline(cp.id) is true
   - Expected: encoder.dispatch_workgroups(4, 1, 1) is true
   - Expected: encoder.end_compute_pass() is true
   - Expected: gpu_ctx.queue_submit([command_buffer]) is true
   - Expected: result.valid is true
   - Expected: result.queue_write_count equals `1`
   - Expected: result.buffer_state_count equals `1`
   - Expected: result.buffer_checksum equals `33`
   - Expected: result.compute_pass_count equals `1`
   - Expected: result.dispatched_workgroups equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ctx = canvas_get_context_webgpu(320, 240, true)
expect(ctx.request_device()).to_equal(true)
expect(ctx.configure()).to_equal(true)
var gpu_ctx: WebGPUContext = ctx.gpu
var resources = gpu_ctx.resources
val buffer = resources.create_buffer("storage", 64, WEBGPU_BUFFER_USAGE_COPY_DST)
gpu_ctx.resources = resources
val cs = ctx.create_shader_module("cs", "@compute @workgroup_size(1) fn main() { }")
val cp = ctx.create_compute_pipeline(cs)
expect(gpu_ctx.queue_write_buffer(buffer.id, 0, 32)).to_equal(true)
var encoder = gpu_ctx.create_command_encoder("canvas-compute")
expect(encoder.begin_compute_pass()).to_equal(true)
expect(encoder.set_pipeline(cp.id)).to_equal(true)
expect(encoder.dispatch_workgroups(4, 1, 1)).to_equal(true)
expect(encoder.end_compute_pass()).to_equal(true)
val command_buffer = encoder.finish("canvas-compute-commands")
expect(gpu_ctx.queue_submit([command_buffer])).to_equal(true)
val result = webgpu_software_execute_queue(gpu_ctx.queue)
expect(result.valid).to_equal(true)
expect(result.queue_write_count).to_equal(1)
expect(result.buffer_state_count).to_equal(1)
expect(result.buffer_checksum).to_equal(33)
expect(result.compute_pass_count).to_equal(1)
expect(result.dispatched_workgroups).to_equal(4)
```

</details>

#### destroys secure canvas WebGPU context resources and queue state

1. var ctx = canvas get context webgpu
   - Expected: ctx.request_device() is true
   - Expected: ctx.configure() is true
   - Expected: gpu_ctx.queue_write_buffer(buffer.id, 0, 32) is true
   - Expected: ctx.gpu.resources.resource_count() equals `1`
   - Expected: ctx.gpu.queue.write_count() equals `1`
   - Expected: ctx.destroy() is true
   - Expected: ctx.gpu.device_ready is false
   - Expected: ctx.gpu.device_lost is true
   - Expected: ctx.gpu.resources.resource_count() equals `0`
   - Expected: ctx.gpu.queue.write_count() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ctx = canvas_get_context_webgpu(320, 240, true)
expect(ctx.request_device()).to_equal(true)
expect(ctx.configure()).to_equal(true)
var gpu_ctx: WebGPUContext = ctx.gpu
var resources = gpu_ctx.resources
val buffer = resources.create_buffer("upload", 64, WEBGPU_BUFFER_USAGE_COPY_DST)
gpu_ctx.resources = resources
expect(gpu_ctx.queue_write_buffer(buffer.id, 0, 32)).to_equal(true)
ctx.gpu = gpu_ctx
expect(ctx.gpu.resources.resource_count()).to_equal(1)
expect(ctx.gpu.queue.write_count()).to_equal(1)
expect(ctx.destroy()).to_equal(true)
expect(ctx.gpu.device_ready).to_equal(false)
expect(ctx.gpu.device_lost).to_equal(true)
expect(ctx.gpu.resources.resource_count()).to_equal(0)
expect(ctx.gpu.queue.write_count()).to_equal(0)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 71 |
| Active scenarios | 71 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

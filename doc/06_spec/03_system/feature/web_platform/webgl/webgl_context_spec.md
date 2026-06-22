# Webgl Context Specification

> <details>

<!-- sdn-diagram:id=webgl_context_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=webgl_context_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

webgl_context_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=webgl_context_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 97 | 97 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Webgl Context Specification

## Scenarios

### Browser WebGL context

### context names

#### recognizes WebGL context names case-insensitively

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(webgl_is_supported_context_name("webgl")).to_equal(true)
expect(webgl_is_supported_context_name("WEBGL")).to_equal(true)
expect(webgl_is_supported_context_name("experimental-webgl")).to_equal(true)
expect(webgl_is_supported_context_name("WebGL2")).to_equal(true)
```

</details>

#### rejects unknown context names

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(webgl_is_supported_context_name("bitmaprenderer")).to_equal(false)
```

</details>

#### maps context names to versions

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(webgl_context_version_for_name("webgl")).to_equal(1)
expect(webgl_context_version_for_name("experimental-webgl")).to_equal(1)
expect(webgl_context_version_for_name("webgl2")).to_equal(2)
expect(webgl_context_version_for_name("2d")).to_equal(0)
```

</details>

#### reports drawing buffer dimensions

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ctx = webgl_create_context(1, 640, 480)
expect(ctx.drawing_buffer_width()).to_equal(640)
expect(ctx.drawing_buffer_height()).to_equal(480)
```

</details>

#### reports context attributes

1. var ctx = webgl create context
   - Expected: attrs.valid is true
   - Expected: attrs.alpha is true
   - Expected: attrs.depth is true
   - Expected: attrs.stencil is false
   - Expected: attrs.antialias is true
   - Expected: attrs.premultiplied_alpha is true
   - Expected: attrs.preserve_drawing_buffer is false
   - Expected: attrs.power_preference equals `default`
   - Expected: attrs.fail_if_major_performance_caveat is false
   - Expected: ctx.get_error() equals `WEBGL_NO_ERROR`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ctx = webgl_create_context(1, 640, 480)
val attrs = ctx.get_context_attributes()
expect(attrs.valid).to_equal(true)
expect(attrs.alpha).to_equal(true)
expect(attrs.depth).to_equal(true)
expect(attrs.stencil).to_equal(false)
expect(attrs.antialias).to_equal(true)
expect(attrs.premultiplied_alpha).to_equal(true)
expect(attrs.preserve_drawing_buffer).to_equal(false)
expect(attrs.power_preference).to_equal("default")
expect(attrs.fail_if_major_performance_caveat).to_equal(false)
expect(ctx.get_error()).to_equal(WEBGL_NO_ERROR)
```

</details>

#### returns invalid context attributes while context is lost

1. var ctx = webgl create context
2. ctx lose context
   - Expected: attrs.valid is false
   - Expected: attrs.error equals `context lost`
   - Expected: ctx.get_error() equals `WEBGL_CONTEXT_LOST_WEBGL`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ctx = webgl_create_context(1, 320, 240)
ctx.lose_context()
val attrs = ctx.get_context_attributes()
expect(attrs.valid).to_equal(false)
expect(attrs.error).to_equal("context lost")
expect(ctx.get_error()).to_equal(WEBGL_CONTEXT_LOST_WEBGL)
```

</details>

### error state and context loss

#### starts with no error

1. var ctx = webgl create context
   - Expected: ctx.get_error() equals `WEBGL_NO_ERROR`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ctx = webgl_create_context(1, 320, 240)
expect(ctx.get_error()).to_equal(WEBGL_NO_ERROR)
```

</details>

#### returns and clears invalid enum

1. var ctx = webgl create context
   - Expected: shader.valid is false
   - Expected: ctx.get_error() equals `WEBGL_INVALID_ENUM`
   - Expected: ctx.get_error() equals `WEBGL_NO_ERROR`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ctx = webgl_create_context(1, 320, 240)
val shader = ctx.create_shader(999)
expect(shader.valid).to_equal(false)
expect(ctx.get_error()).to_equal(WEBGL_INVALID_ENUM)
expect(ctx.get_error()).to_equal(WEBGL_NO_ERROR)
```

</details>

#### reports context lost and blocks resources while lost

1. var ctx = webgl create context
2. ctx lose context
   - Expected: ctx.is_available() is false
   - Expected: ctx.get_error() equals `WEBGL_CONTEXT_LOST_WEBGL`
   - Expected: buffer.valid is false
   - Expected: ctx.get_error() equals `WEBGL_CONTEXT_LOST_WEBGL`
3. ctx restore context
   - Expected: ctx.is_available() is true
   - Expected: ctx.get_error() equals `WEBGL_NO_ERROR`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ctx = webgl_create_context(1, 320, 240)
ctx.lose_context()
expect(ctx.is_available()).to_equal(false)
expect(ctx.get_error()).to_equal(WEBGL_CONTEXT_LOST_WEBGL)
val buffer = ctx.create_buffer()
expect(buffer.valid).to_equal(false)
expect(ctx.get_error()).to_equal(WEBGL_CONTEXT_LOST_WEBGL)
ctx.restore_context()
expect(ctx.is_available()).to_equal(true)
expect(ctx.get_error()).to_equal(WEBGL_NO_ERROR)
```

</details>

### resources

#### allocates deterministic buffer and texture ids

1. var ctx = webgl create context
   - Expected: b1.id equals `1`
   - Expected: b2.id equals `2`
   - Expected: t1.id equals `1`
   - Expected: f1.id equals `1`
   - Expected: r1.id equals `1`
   - Expected: ctx.buffers.len() equals `2`
   - Expected: ctx.textures.len() equals `1`
   - Expected: ctx.framebuffers.len() equals `1`
   - Expected: ctx.renderbuffers.len() equals `1`
   - Expected: ctx.is_buffer(b1.id) is true
   - Expected: ctx.is_texture(t1.id) is true
   - Expected: ctx.is_framebuffer(f1.id) is true
   - Expected: ctx.is_renderbuffer(r1.id) is true
   - Expected: ctx.is_buffer(99) is false
   - Expected: ctx.is_texture(99) is false
   - Expected: ctx.is_framebuffer(99) is false
   - Expected: ctx.is_renderbuffer(99) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ctx = webgl_create_context(2, 640, 480)
val b1 = ctx.create_buffer()
val b2 = ctx.create_buffer()
val t1 = ctx.create_texture()
val f1 = ctx.create_framebuffer()
val r1 = ctx.create_renderbuffer()
expect(b1.id).to_equal(1)
expect(b2.id).to_equal(2)
expect(t1.id).to_equal(1)
expect(f1.id).to_equal(1)
expect(r1.id).to_equal(1)
expect(ctx.buffers.len()).to_equal(2)
expect(ctx.textures.len()).to_equal(1)
expect(ctx.framebuffers.len()).to_equal(1)
expect(ctx.renderbuffers.len()).to_equal(1)
expect(ctx.is_buffer(b1.id)).to_equal(true)
expect(ctx.is_texture(t1.id)).to_equal(true)
expect(ctx.is_framebuffer(f1.id)).to_equal(true)
expect(ctx.is_renderbuffer(r1.id)).to_equal(true)
expect(ctx.is_buffer(99)).to_equal(false)
expect(ctx.is_texture(99)).to_equal(false)
expect(ctx.is_framebuffer(99)).to_equal(false)
expect(ctx.is_renderbuffer(99)).to_equal(false)
```

</details>

#### returns false for resource probes while context is lost

1. var ctx = webgl create context
2. ctx lose context
   - Expected: ctx.is_buffer(buffer.id) is false
   - Expected: ctx.is_texture(texture.id) is false
   - Expected: ctx.is_framebuffer(framebuffer.id) is false
   - Expected: ctx.is_renderbuffer(renderbuffer.id) is false
   - Expected: ctx.get_error() equals `WEBGL_CONTEXT_LOST_WEBGL`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ctx = webgl_create_context(1, 320, 240)
val buffer = ctx.create_buffer()
val texture = ctx.create_texture()
val framebuffer = ctx.create_framebuffer()
val renderbuffer = ctx.create_renderbuffer()
ctx.lose_context()
expect(ctx.is_buffer(buffer.id)).to_equal(false)
expect(ctx.is_texture(texture.id)).to_equal(false)
expect(ctx.is_framebuffer(framebuffer.id)).to_equal(false)
expect(ctx.is_renderbuffer(renderbuffer.id)).to_equal(false)
expect(ctx.get_error()).to_equal(WEBGL_CONTEXT_LOST_WEBGL)
```

</details>

#### deletes resources and clears bindings and attachments

1. var ctx = webgl create context
   - Expected: ctx.bind_buffer(WEBGL_ARRAY_BUFFER, buffer.id) is true
   - Expected: ctx.buffer_data_size(WEBGL_ARRAY_BUFFER, 16, WEBGL_STATIC_DRAW) is true
   - Expected: ctx.enable_vertex_attrib_array(0) is true
   - Expected: ctx.vertex_attrib_pointer(0, 4, WEBGL_FLOAT, false, 0, 0) is true
   - Expected: ctx.bind_texture(WEBGL_TEXTURE_2D, texture.id) is true
   - Expected: ctx.tex_image_2d(WEBGL_TEXTURE_2D, 0, WEBGL_RGBA, 1, 1, 0, WEBGL_RGBA, WEBGL_UNSIGNED_BYTE, []) is true
   - Expected: ctx.bind_framebuffer(WEBGL_FRAMEBUFFER, framebuffer.id) is true
   - Expected: ctx.framebuffer_texture_2d(WEBGL_FRAMEBUFFER, WEBGL_COLOR_ATTACHMENT0, WEBGL_TEXTURE_2D, texture.id, 0) is true
   - Expected: ctx.bind_renderbuffer(WEBGL_RENDERBUFFER, renderbuffer.id) is true
   - Expected: ctx.renderbuffer_storage(WEBGL_RENDERBUFFER, WEBGL_DEPTH_COMPONENT16, 1, 1) is true
   - Expected: ctx.framebuffer_renderbuffer(WEBGL_FRAMEBUFFER, WEBGL_DEPTH_ATTACHMENT, WEBGL_RENDERBUFFER, renderbuffer.id) is true
   - Expected: ctx.delete_buffer(buffer.id) is true
   - Expected: ctx.is_buffer(buffer.id) is false
   - Expected: ctx.bound_array_buffer equals `-1`
   - Expected: ctx.vertex_attribs[0].buffer_id equals `-1`
   - Expected: ctx.bind_buffer(WEBGL_ARRAY_BUFFER, buffer.id) is false
   - Expected: ctx.get_error() equals `WEBGL_INVALID_VALUE`
   - Expected: ctx.delete_texture(texture.id) is true
   - Expected: ctx.is_texture(texture.id) is false
   - Expected: ctx.bound_texture_2d equals `-1`
   - Expected: ctx.framebuffers[0].color_texture_id equals `-1`
   - Expected: ctx.delete_renderbuffer(renderbuffer.id) is true
   - Expected: ctx.is_renderbuffer(renderbuffer.id) is false
   - Expected: ctx.bound_renderbuffer equals `-1`
   - Expected: ctx.framebuffers[0].depth_renderbuffer_id equals `-1`
   - Expected: ctx.delete_framebuffer(framebuffer.id) is true
   - Expected: ctx.is_framebuffer(framebuffer.id) is false
   - Expected: ctx.bound_framebuffer equals `-1`
   - Expected: ctx.delete_framebuffer(framebuffer.id) is false
   - Expected: ctx.get_error() equals `WEBGL_INVALID_VALUE`


<details>
<summary>Executable SSpec</summary>

Runnable source: 35 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ctx = webgl_create_context(1, 320, 240)
val buffer = ctx.create_buffer()
val texture = ctx.create_texture()
val framebuffer = ctx.create_framebuffer()
val renderbuffer = ctx.create_renderbuffer()
expect(ctx.bind_buffer(WEBGL_ARRAY_BUFFER, buffer.id)).to_equal(true)
expect(ctx.buffer_data_size(WEBGL_ARRAY_BUFFER, 16, WEBGL_STATIC_DRAW)).to_equal(true)
expect(ctx.enable_vertex_attrib_array(0)).to_equal(true)
expect(ctx.vertex_attrib_pointer(0, 4, WEBGL_FLOAT, false, 0, 0)).to_equal(true)
expect(ctx.bind_texture(WEBGL_TEXTURE_2D, texture.id)).to_equal(true)
expect(ctx.tex_image_2d(WEBGL_TEXTURE_2D, 0, WEBGL_RGBA, 1, 1, 0, WEBGL_RGBA, WEBGL_UNSIGNED_BYTE, [])).to_equal(true)
expect(ctx.bind_framebuffer(WEBGL_FRAMEBUFFER, framebuffer.id)).to_equal(true)
expect(ctx.framebuffer_texture_2d(WEBGL_FRAMEBUFFER, WEBGL_COLOR_ATTACHMENT0, WEBGL_TEXTURE_2D, texture.id, 0)).to_equal(true)
expect(ctx.bind_renderbuffer(WEBGL_RENDERBUFFER, renderbuffer.id)).to_equal(true)
expect(ctx.renderbuffer_storage(WEBGL_RENDERBUFFER, WEBGL_DEPTH_COMPONENT16, 1, 1)).to_equal(true)
expect(ctx.framebuffer_renderbuffer(WEBGL_FRAMEBUFFER, WEBGL_DEPTH_ATTACHMENT, WEBGL_RENDERBUFFER, renderbuffer.id)).to_equal(true)
expect(ctx.delete_buffer(buffer.id)).to_equal(true)
expect(ctx.is_buffer(buffer.id)).to_equal(false)
expect(ctx.bound_array_buffer).to_equal(-1)
expect(ctx.vertex_attribs[0].buffer_id).to_equal(-1)
expect(ctx.bind_buffer(WEBGL_ARRAY_BUFFER, buffer.id)).to_equal(false)
expect(ctx.get_error()).to_equal(WEBGL_INVALID_VALUE)
expect(ctx.delete_texture(texture.id)).to_equal(true)
expect(ctx.is_texture(texture.id)).to_equal(false)
expect(ctx.bound_texture_2d).to_equal(-1)
expect(ctx.framebuffers[0].color_texture_id).to_equal(-1)
expect(ctx.delete_renderbuffer(renderbuffer.id)).to_equal(true)
expect(ctx.is_renderbuffer(renderbuffer.id)).to_equal(false)
expect(ctx.bound_renderbuffer).to_equal(-1)
expect(ctx.framebuffers[0].depth_renderbuffer_id).to_equal(-1)
expect(ctx.delete_framebuffer(framebuffer.id)).to_equal(true)
expect(ctx.is_framebuffer(framebuffer.id)).to_equal(false)
expect(ctx.bound_framebuffer).to_equal(-1)
expect(ctx.delete_framebuffer(framebuffer.id)).to_equal(false)
expect(ctx.get_error()).to_equal(WEBGL_INVALID_VALUE)
```

</details>

#### does not consume shader ids for invalid shader types

1. var ctx = webgl create context
   - Expected: bad.valid is false
   - Expected: good.id equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ctx = webgl_create_context(1, 320, 240)
val bad = ctx.create_shader(999)
val good = ctx.create_shader(WEBGL_VERTEX_SHADER)
expect(bad.valid).to_equal(false)
expect(good.id).to_equal(1)
```

</details>

### render command recording

#### initializes viewport and clear state

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ctx = webgl_create_context(1, 320, 240)
expect(ctx.viewport_x).to_equal(0)
expect(ctx.viewport_y).to_equal(0)
expect(ctx.viewport_width).to_equal(320)
expect(ctx.viewport_height).to_equal(240)
expect(ctx.clear_alpha).to_equal(0.0)
expect(ctx.render_commands.len()).to_equal(0)
```

</details>

#### records viewport clear color and clear commands

1. var ctx = webgl create context
   - Expected: ctx.viewport(4, 8, 160, 120) is true
   - Expected: ctx.clear_color(0.1, 0.2, 0.3, 1.0) is true
   - Expected: ctx.clear(WEBGL_COLOR_BUFFER_BIT) is true
   - Expected: ctx.viewport_x equals `4`
   - Expected: ctx.viewport_height equals `120`
   - Expected: ctx.clear_blue equals `0.3`
   - Expected: ctx.render_commands.len() equals `3`
   - Expected: ctx.render_commands[0].kind equals `WEBGL_RENDER_COMMAND_VIEWPORT`
   - Expected: ctx.render_commands[1].kind equals `WEBGL_RENDER_COMMAND_CLEAR_COLOR`
   - Expected: ctx.render_commands[2].kind equals `WEBGL_RENDER_COMMAND_CLEAR`
   - Expected: ctx.render_commands[2].mask equals `WEBGL_COLOR_BUFFER_BIT`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ctx = webgl_create_context(1, 320, 240)
expect(ctx.viewport(4, 8, 160, 120)).to_equal(true)
expect(ctx.clear_color(0.1, 0.2, 0.3, 1.0)).to_equal(true)
expect(ctx.clear(WEBGL_COLOR_BUFFER_BIT)).to_equal(true)
expect(ctx.viewport_x).to_equal(4)
expect(ctx.viewport_height).to_equal(120)
expect(ctx.clear_blue).to_equal(0.3)
expect(ctx.render_commands.len()).to_equal(3)
expect(ctx.render_commands[0].kind).to_equal(WEBGL_RENDER_COMMAND_VIEWPORT)
expect(ctx.render_commands[1].kind).to_equal(WEBGL_RENDER_COMMAND_CLEAR_COLOR)
expect(ctx.render_commands[2].kind).to_equal(WEBGL_RENDER_COMMAND_CLEAR)
expect(ctx.render_commands[2].mask).to_equal(WEBGL_COLOR_BUFFER_BIT)
```

</details>

#### clamps clear color components to the WebGL range

1. var ctx = webgl create context
   - Expected: ctx.clear_color(1.5, -0.5, 2.0, -1.0) is true
   - Expected: color.float_values[0] equals `1.0`
   - Expected: color.float_values[1] equals `0.0`
   - Expected: color.float_values[2] equals `1.0`
   - Expected: color.float_values[3] equals `0.0`
   - Expected: ctx.render_commands[0].red equals `1.0`
   - Expected: ctx.render_commands[0].green equals `0.0`
   - Expected: ctx.get_error() equals `WEBGL_NO_ERROR`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ctx = webgl_create_context(1, 320, 240)
expect(ctx.clear_color(1.5, -0.5, 2.0, -1.0)).to_equal(true)
val color = ctx.get_parameter(WEBGL_COLOR_CLEAR_VALUE)
expect(color.float_values[0]).to_equal(1.0)
expect(color.float_values[1]).to_equal(0.0)
expect(color.float_values[2]).to_equal(1.0)
expect(color.float_values[3]).to_equal(0.0)
expect(ctx.render_commands[0].red).to_equal(1.0)
expect(ctx.render_commands[0].green).to_equal(0.0)
expect(ctx.get_error()).to_equal(WEBGL_NO_ERROR)
```

</details>

#### tracks depth and stencil clear state

1. var ctx = webgl create context
   - Expected: ctx.clear_depth_value equals `1.0`
   - Expected: ctx.depth_range_near equals `0.0`
   - Expected: ctx.depth_range_far equals `1.0`
   - Expected: ctx.clear_stencil_value equals `0`
   - Expected: ctx.clear_depth(1.4) is true
   - Expected: ctx.clear_stencil(7) is true
   - Expected: ctx.clear_depth_value equals `1.0`
   - Expected: ctx.depth_range(-0.2, 1.4) is true
   - Expected: ctx.depth_range_near equals `0.0`
   - Expected: ctx.depth_range_far equals `1.0`
   - Expected: ctx.depth_range(0.25, 0.75) is true
   - Expected: ctx.depth_range_near equals `0.25`
   - Expected: ctx.depth_range_far equals `0.75`
   - Expected: ctx.clear_stencil_value equals `7`
   - Expected: ctx.clear_depth(-0.4) is true
   - Expected: ctx.clear_depth_value equals `0.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ctx = webgl_create_context(1, 320, 240)
expect(ctx.clear_depth_value).to_equal(1.0)
expect(ctx.depth_range_near).to_equal(0.0)
expect(ctx.depth_range_far).to_equal(1.0)
expect(ctx.clear_stencil_value).to_equal(0)
expect(ctx.clear_depth(1.4)).to_equal(true)
expect(ctx.clear_stencil(7)).to_equal(true)
expect(ctx.clear_depth_value).to_equal(1.0)
expect(ctx.depth_range(-0.2, 1.4)).to_equal(true)
expect(ctx.depth_range_near).to_equal(0.0)
expect(ctx.depth_range_far).to_equal(1.0)
expect(ctx.depth_range(0.25, 0.75)).to_equal(true)
expect(ctx.depth_range_near).to_equal(0.25)
expect(ctx.depth_range_far).to_equal(0.75)
expect(ctx.clear_stencil_value).to_equal(7)
expect(ctx.clear_depth(-0.4)).to_equal(true)
expect(ctx.clear_depth_value).to_equal(0.0)
```

</details>

#### records combined color depth and stencil clear masks

1. var ctx = webgl create context
   - Expected: ctx.clear(mask) is true
   - Expected: ctx.render_commands.len() equals `1`
   - Expected: ctx.render_commands[0].kind equals `WEBGL_RENDER_COMMAND_CLEAR`
   - Expected: ctx.render_commands[0].mask equals `mask`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ctx = webgl_create_context(1, 320, 240)
val mask = WEBGL_COLOR_BUFFER_BIT + WEBGL_DEPTH_BUFFER_BIT + WEBGL_STENCIL_BUFFER_BIT
expect(ctx.clear(mask)).to_equal(true)
expect(ctx.render_commands.len()).to_equal(1)
expect(ctx.render_commands[0].kind).to_equal(WEBGL_RENDER_COMMAND_CLEAR)
expect(ctx.render_commands[0].mask).to_equal(mask)
```

</details>

#### records scissor commands for backend clipping

1. var ctx = webgl create context
   - Expected: ctx.scissor(2, 4, 80, 60) is true
   - Expected: ctx.render_commands.len() equals `1`
   - Expected: ctx.render_commands[0].kind equals `WEBGL_RENDER_COMMAND_SCISSOR`
   - Expected: ctx.render_commands[0].x equals `2`
   - Expected: ctx.render_commands[0].y equals `4`
   - Expected: ctx.render_commands[0].width equals `80`
   - Expected: ctx.render_commands[0].height equals `60`
   - Expected: ctx.get_parameter(WEBGL_SCISSOR_BOX).int_values[2] equals `80`
   - Expected: ctx.get_error() equals `WEBGL_NO_ERROR`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ctx = webgl_create_context(1, 320, 240)
expect(ctx.scissor(2, 4, 80, 60)).to_equal(true)
expect(ctx.render_commands.len()).to_equal(1)
expect(ctx.render_commands[0].kind).to_equal(WEBGL_RENDER_COMMAND_SCISSOR)
expect(ctx.render_commands[0].x).to_equal(2)
expect(ctx.render_commands[0].y).to_equal(4)
expect(ctx.render_commands[0].width).to_equal(80)
expect(ctx.render_commands[0].height).to_equal(60)
expect(ctx.get_parameter(WEBGL_SCISSOR_BOX).int_values[2]).to_equal(80)
expect(ctx.get_error()).to_equal(WEBGL_NO_ERROR)
```

</details>

#### records draw-state commands for backend replay

1. var ctx = webgl create context
   - Expected: ctx.line_width(2.0) is true
   - Expected: ctx.depth_func(WEBGL_LEQUAL) is true
   - Expected: ctx.cull_face(WEBGL_FRONT) is true
   - Expected: ctx.front_face(WEBGL_CW) is true
   - Expected: ctx.render_commands.len() equals `4`
   - Expected: ctx.render_commands[0].kind equals `WEBGL_RENDER_COMMAND_LINE_WIDTH`
   - Expected: ctx.render_commands[0].red equals `2.0`
   - Expected: ctx.render_commands[1].kind equals `WEBGL_RENDER_COMMAND_DEPTH_FUNC`
   - Expected: ctx.render_commands[1].mode equals `WEBGL_LEQUAL`
   - Expected: ctx.render_commands[2].kind equals `WEBGL_RENDER_COMMAND_CULL_FACE`
   - Expected: ctx.render_commands[2].mode equals `WEBGL_FRONT`
   - Expected: ctx.render_commands[3].kind equals `WEBGL_RENDER_COMMAND_FRONT_FACE`
   - Expected: ctx.render_commands[3].mode equals `WEBGL_CW`
   - Expected: ctx.get_error() equals `WEBGL_NO_ERROR`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ctx = webgl_create_context(1, 320, 240)
expect(ctx.line_width(2.0)).to_equal(true)
expect(ctx.depth_func(WEBGL_LEQUAL)).to_equal(true)
expect(ctx.cull_face(WEBGL_FRONT)).to_equal(true)
expect(ctx.front_face(WEBGL_CW)).to_equal(true)
expect(ctx.render_commands.len()).to_equal(4)
expect(ctx.render_commands[0].kind).to_equal(WEBGL_RENDER_COMMAND_LINE_WIDTH)
expect(ctx.render_commands[0].red).to_equal(2.0)
expect(ctx.render_commands[1].kind).to_equal(WEBGL_RENDER_COMMAND_DEPTH_FUNC)
expect(ctx.render_commands[1].mode).to_equal(WEBGL_LEQUAL)
expect(ctx.render_commands[2].kind).to_equal(WEBGL_RENDER_COMMAND_CULL_FACE)
expect(ctx.render_commands[2].mode).to_equal(WEBGL_FRONT)
expect(ctx.render_commands[3].kind).to_equal(WEBGL_RENDER_COMMAND_FRONT_FACE)
expect(ctx.render_commands[3].mode).to_equal(WEBGL_CW)
expect(ctx.get_error()).to_equal(WEBGL_NO_ERROR)
```

</details>

#### records capability commands for backend replay

1. var ctx = webgl create context
   - Expected: ctx.enable(WEBGL_BLEND) is true
   - Expected: ctx.enable(WEBGL_DEPTH_TEST) is true
   - Expected: ctx.disable(WEBGL_DITHER) is true
   - Expected: ctx.render_commands.len() equals `3`
   - Expected: ctx.render_commands[0].kind equals `WEBGL_RENDER_COMMAND_CAPABILITY`
   - Expected: ctx.render_commands[0].target equals `WEBGL_BLEND`
   - Expected: ctx.render_commands[0].mask equals `1`
   - Expected: ctx.render_commands[1].target equals `WEBGL_DEPTH_TEST`
   - Expected: ctx.render_commands[1].mask equals `1`
   - Expected: ctx.render_commands[2].target equals `WEBGL_DITHER`
   - Expected: ctx.render_commands[2].mask equals `0`
   - Expected: ctx.enable(999) is false
   - Expected: ctx.get_error() equals `WEBGL_INVALID_ENUM`
   - Expected: ctx.render_commands.len() equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ctx = webgl_create_context(1, 320, 240)
expect(ctx.enable(WEBGL_BLEND)).to_equal(true)
expect(ctx.enable(WEBGL_DEPTH_TEST)).to_equal(true)
expect(ctx.disable(WEBGL_DITHER)).to_equal(true)
expect(ctx.render_commands.len()).to_equal(3)
expect(ctx.render_commands[0].kind).to_equal(WEBGL_RENDER_COMMAND_CAPABILITY)
expect(ctx.render_commands[0].target).to_equal(WEBGL_BLEND)
expect(ctx.render_commands[0].mask).to_equal(1)
expect(ctx.render_commands[1].target).to_equal(WEBGL_DEPTH_TEST)
expect(ctx.render_commands[1].mask).to_equal(1)
expect(ctx.render_commands[2].target).to_equal(WEBGL_DITHER)
expect(ctx.render_commands[2].mask).to_equal(0)
expect(ctx.enable(999)).to_equal(false)
expect(ctx.get_error()).to_equal(WEBGL_INVALID_ENUM)
expect(ctx.render_commands.len()).to_equal(3)
```

</details>

#### records blend-state commands for backend replay

1. var ctx = webgl create context
   - Expected: ctx.blend_color(-1.0, 0.25, 0.75, 2.0) is true
   - Expected: ctx.blend_func_separate(WEBGL_SRC_ALPHA, WEBGL_ONE_MINUS_SRC_ALPHA, WEBGL_ONE, WEBGL_ZERO) is true
   - Expected: ctx.blend_equation_separate(WEBGL_FUNC_ADD, WEBGL_FUNC_SUBTRACT) is true
   - Expected: ctx.render_commands.len() equals `3`
   - Expected: ctx.render_commands[0].kind equals `WEBGL_RENDER_COMMAND_BLEND_COLOR`
   - Expected: ctx.render_commands[0].red equals `0.0`
   - Expected: ctx.render_commands[0].green equals `0.25`
   - Expected: ctx.render_commands[0].blue equals `0.75`
   - Expected: ctx.render_commands[0].alpha equals `1.0`
   - Expected: ctx.render_commands[1].kind equals `WEBGL_RENDER_COMMAND_BLEND_FUNC_SEPARATE`
   - Expected: ctx.render_commands[1].target equals `WEBGL_SRC_ALPHA`
   - Expected: ctx.render_commands[1].buffer_id equals `WEBGL_ONE_MINUS_SRC_ALPHA`
   - Expected: ctx.render_commands[1].texture_id equals `WEBGL_ONE`
   - Expected: ctx.render_commands[1].mode equals `WEBGL_ZERO`
   - Expected: ctx.render_commands[2].kind equals `WEBGL_RENDER_COMMAND_BLEND_EQUATION_SEPARATE`
   - Expected: ctx.render_commands[2].target equals `WEBGL_FUNC_ADD`
   - Expected: ctx.render_commands[2].mode equals `WEBGL_FUNC_SUBTRACT`
   - Expected: ctx.get_error() equals `WEBGL_NO_ERROR`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ctx = webgl_create_context(1, 320, 240)
expect(ctx.blend_color(-1.0, 0.25, 0.75, 2.0)).to_equal(true)
expect(ctx.blend_func_separate(WEBGL_SRC_ALPHA, WEBGL_ONE_MINUS_SRC_ALPHA, WEBGL_ONE, WEBGL_ZERO)).to_equal(true)
expect(ctx.blend_equation_separate(WEBGL_FUNC_ADD, WEBGL_FUNC_SUBTRACT)).to_equal(true)
expect(ctx.render_commands.len()).to_equal(3)
expect(ctx.render_commands[0].kind).to_equal(WEBGL_RENDER_COMMAND_BLEND_COLOR)
expect(ctx.render_commands[0].red).to_equal(0.0)
expect(ctx.render_commands[0].green).to_equal(0.25)
expect(ctx.render_commands[0].blue).to_equal(0.75)
expect(ctx.render_commands[0].alpha).to_equal(1.0)
expect(ctx.render_commands[1].kind).to_equal(WEBGL_RENDER_COMMAND_BLEND_FUNC_SEPARATE)
expect(ctx.render_commands[1].target).to_equal(WEBGL_SRC_ALPHA)
expect(ctx.render_commands[1].buffer_id).to_equal(WEBGL_ONE_MINUS_SRC_ALPHA)
expect(ctx.render_commands[1].texture_id).to_equal(WEBGL_ONE)
expect(ctx.render_commands[1].mode).to_equal(WEBGL_ZERO)
expect(ctx.render_commands[2].kind).to_equal(WEBGL_RENDER_COMMAND_BLEND_EQUATION_SEPARATE)
expect(ctx.render_commands[2].target).to_equal(WEBGL_FUNC_ADD)
expect(ctx.render_commands[2].mode).to_equal(WEBGL_FUNC_SUBTRACT)
expect(ctx.get_error()).to_equal(WEBGL_NO_ERROR)
```

</details>

#### records polygon offset and sample coverage commands for backend replay

1. var ctx = webgl create context
   - Expected: ctx.polygon_offset(1.25, -2.5) is true
   - Expected: ctx.sample_coverage(1.5, true) is true
   - Expected: ctx.render_commands.len() equals `2`
   - Expected: ctx.render_commands[0].kind equals `WEBGL_RENDER_COMMAND_POLYGON_OFFSET`
   - Expected: ctx.render_commands[0].red equals `1.25`
   - Expected: ctx.render_commands[0].green equals `-2.5`
   - Expected: ctx.render_commands[1].kind equals `WEBGL_RENDER_COMMAND_SAMPLE_COVERAGE`
   - Expected: ctx.render_commands[1].red equals `1.0`
   - Expected: ctx.render_commands[1].mask equals `1`
   - Expected: ctx.get_error() equals `WEBGL_NO_ERROR`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ctx = webgl_create_context(1, 320, 240)
expect(ctx.polygon_offset(1.25, -2.5)).to_equal(true)
expect(ctx.sample_coverage(1.5, true)).to_equal(true)
expect(ctx.render_commands.len()).to_equal(2)
expect(ctx.render_commands[0].kind).to_equal(WEBGL_RENDER_COMMAND_POLYGON_OFFSET)
expect(ctx.render_commands[0].red).to_equal(1.25)
expect(ctx.render_commands[0].green).to_equal(-2.5)
expect(ctx.render_commands[1].kind).to_equal(WEBGL_RENDER_COMMAND_SAMPLE_COVERAGE)
expect(ctx.render_commands[1].red).to_equal(1.0)
expect(ctx.render_commands[1].mask).to_equal(1)
expect(ctx.get_error()).to_equal(WEBGL_NO_ERROR)
```

</details>

#### records clear and write-mask commands for backend replay

1. var ctx = webgl create context
   - Expected: ctx.clear_depth(1.5) is true
   - Expected: ctx.depth_range(-0.2, 0.8) is true
   - Expected: ctx.clear_stencil(7) is true
   - Expected: ctx.color_mask(true, false, true, false) is true
   - Expected: ctx.depth_mask(false) is true
   - Expected: ctx.stencil_mask(15) is true
   - Expected: ctx.stencil_mask_separate(WEBGL_BACK, 9) is true
   - Expected: ctx.render_commands.len() equals `7`
   - Expected: ctx.render_commands[0].kind equals `WEBGL_RENDER_COMMAND_CLEAR_DEPTH`
   - Expected: ctx.render_commands[0].red equals `1.0`
   - Expected: ctx.render_commands[1].kind equals `WEBGL_RENDER_COMMAND_DEPTH_RANGE`
   - Expected: ctx.render_commands[1].red equals `0.0`
   - Expected: ctx.render_commands[1].green equals `0.8`
   - Expected: ctx.render_commands[2].kind equals `WEBGL_RENDER_COMMAND_CLEAR_STENCIL`
   - Expected: ctx.render_commands[2].mask equals `7`
   - Expected: ctx.render_commands[3].kind equals `WEBGL_RENDER_COMMAND_COLOR_MASK`
   - Expected: ctx.render_commands[3].x equals `1`
   - Expected: ctx.render_commands[3].y equals `0`
   - Expected: ctx.render_commands[3].width equals `1`
   - Expected: ctx.render_commands[3].height equals `0`
   - Expected: ctx.render_commands[4].kind equals `WEBGL_RENDER_COMMAND_DEPTH_MASK`
   - Expected: ctx.render_commands[4].mask equals `0`
   - Expected: ctx.render_commands[5].kind equals `WEBGL_RENDER_COMMAND_STENCIL_MASK`
   - Expected: ctx.render_commands[5].mask equals `15`
   - Expected: ctx.render_commands[6].kind equals `WEBGL_RENDER_COMMAND_STENCIL_MASK_SEPARATE`
   - Expected: ctx.render_commands[6].target equals `WEBGL_BACK`
   - Expected: ctx.render_commands[6].mask equals `9`
   - Expected: ctx.get_error() equals `WEBGL_NO_ERROR`


<details>
<summary>Executable SSpec</summary>

Runnable source: 29 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ctx = webgl_create_context(1, 320, 240)
expect(ctx.clear_depth(1.5)).to_equal(true)
expect(ctx.depth_range(-0.2, 0.8)).to_equal(true)
expect(ctx.clear_stencil(7)).to_equal(true)
expect(ctx.color_mask(true, false, true, false)).to_equal(true)
expect(ctx.depth_mask(false)).to_equal(true)
expect(ctx.stencil_mask(15)).to_equal(true)
expect(ctx.stencil_mask_separate(WEBGL_BACK, 9)).to_equal(true)
expect(ctx.render_commands.len()).to_equal(7)
expect(ctx.render_commands[0].kind).to_equal(WEBGL_RENDER_COMMAND_CLEAR_DEPTH)
expect(ctx.render_commands[0].red).to_equal(1.0)
expect(ctx.render_commands[1].kind).to_equal(WEBGL_RENDER_COMMAND_DEPTH_RANGE)
expect(ctx.render_commands[1].red).to_equal(0.0)
expect(ctx.render_commands[1].green).to_equal(0.8)
expect(ctx.render_commands[2].kind).to_equal(WEBGL_RENDER_COMMAND_CLEAR_STENCIL)
expect(ctx.render_commands[2].mask).to_equal(7)
expect(ctx.render_commands[3].kind).to_equal(WEBGL_RENDER_COMMAND_COLOR_MASK)
expect(ctx.render_commands[3].x).to_equal(1)
expect(ctx.render_commands[3].y).to_equal(0)
expect(ctx.render_commands[3].width).to_equal(1)
expect(ctx.render_commands[3].height).to_equal(0)
expect(ctx.render_commands[4].kind).to_equal(WEBGL_RENDER_COMMAND_DEPTH_MASK)
expect(ctx.render_commands[4].mask).to_equal(0)
expect(ctx.render_commands[5].kind).to_equal(WEBGL_RENDER_COMMAND_STENCIL_MASK)
expect(ctx.render_commands[5].mask).to_equal(15)
expect(ctx.render_commands[6].kind).to_equal(WEBGL_RENDER_COMMAND_STENCIL_MASK_SEPARATE)
expect(ctx.render_commands[6].target).to_equal(WEBGL_BACK)
expect(ctx.render_commands[6].mask).to_equal(9)
expect(ctx.get_error()).to_equal(WEBGL_NO_ERROR)
```

</details>

#### records stencil test commands for backend replay

1. var ctx = webgl create context
   - Expected: ctx.stencil_func(WEBGL_EQUAL, 3, 15) is true
   - Expected: ctx.stencil_op(WEBGL_KEEP, WEBGL_REPLACE, WEBGL_INCR_WRAP) is true
   - Expected: ctx.render_commands.len() equals `2`
   - Expected: ctx.render_commands[0].kind equals `WEBGL_RENDER_COMMAND_STENCIL_FUNC`
   - Expected: ctx.render_commands[0].target equals `WEBGL_EQUAL`
   - Expected: ctx.render_commands[0].mode equals `3`
   - Expected: ctx.render_commands[0].mask equals `15`
   - Expected: ctx.render_commands[1].kind equals `WEBGL_RENDER_COMMAND_STENCIL_OP`
   - Expected: ctx.render_commands[1].target equals `WEBGL_KEEP`
   - Expected: ctx.render_commands[1].mode equals `WEBGL_REPLACE`
   - Expected: ctx.render_commands[1].element_type equals `WEBGL_INCR_WRAP`
   - Expected: ctx.get_error() equals `WEBGL_NO_ERROR`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ctx = webgl_create_context(1, 320, 240)
expect(ctx.stencil_func(WEBGL_EQUAL, 3, 15)).to_equal(true)
expect(ctx.stencil_op(WEBGL_KEEP, WEBGL_REPLACE, WEBGL_INCR_WRAP)).to_equal(true)
expect(ctx.render_commands.len()).to_equal(2)
expect(ctx.render_commands[0].kind).to_equal(WEBGL_RENDER_COMMAND_STENCIL_FUNC)
expect(ctx.render_commands[0].target).to_equal(WEBGL_EQUAL)
expect(ctx.render_commands[0].mode).to_equal(3)
expect(ctx.render_commands[0].mask).to_equal(15)
expect(ctx.render_commands[1].kind).to_equal(WEBGL_RENDER_COMMAND_STENCIL_OP)
expect(ctx.render_commands[1].target).to_equal(WEBGL_KEEP)
expect(ctx.render_commands[1].mode).to_equal(WEBGL_REPLACE)
expect(ctx.render_commands[1].element_type).to_equal(WEBGL_INCR_WRAP)
expect(ctx.get_error()).to_equal(WEBGL_NO_ERROR)
```

</details>

#### rejects invalid render state without recording commands

1. var ctx = webgl create context
   - Expected: ctx.viewport(0, 0, -1, 10) is false
   - Expected: ctx.get_error() equals `WEBGL_INVALID_VALUE`
   - Expected: ctx.scissor(0, 0, 8, -1) is false
   - Expected: ctx.get_error() equals `WEBGL_INVALID_VALUE`
   - Expected: ctx.clear(0) is false
   - Expected: ctx.get_error() equals `WEBGL_INVALID_VALUE`
   - Expected: ctx.clear(1) is false
   - Expected: ctx.get_error() equals `WEBGL_INVALID_VALUE`
   - Expected: ctx.render_commands.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ctx = webgl_create_context(1, 320, 240)
expect(ctx.viewport(0, 0, -1, 10)).to_equal(false)
expect(ctx.get_error()).to_equal(WEBGL_INVALID_VALUE)
expect(ctx.scissor(0, 0, 8, -1)).to_equal(false)
expect(ctx.get_error()).to_equal(WEBGL_INVALID_VALUE)
expect(ctx.clear(0)).to_equal(false)
expect(ctx.get_error()).to_equal(WEBGL_INVALID_VALUE)
expect(ctx.clear(1)).to_equal(false)
expect(ctx.get_error()).to_equal(WEBGL_INVALID_VALUE)
expect(ctx.render_commands.len()).to_equal(0)
```

</details>

### render state

#### tracks enable and disable capabilities

1. var ctx = webgl create context
   - Expected: ctx.is_enabled(WEBGL_BLEND) is false
   - Expected: ctx.is_enabled(WEBGL_DITHER) is true
   - Expected: ctx.enable(WEBGL_BLEND) is true
   - Expected: ctx.enable(WEBGL_DEPTH_TEST) is true
   - Expected: ctx.enable(WEBGL_POLYGON_OFFSET_FILL) is true
   - Expected: ctx.enable(WEBGL_SAMPLE_ALPHA_TO_COVERAGE) is true
   - Expected: ctx.enable(WEBGL_SAMPLE_COVERAGE) is true
   - Expected: ctx.enable(WEBGL_CULL_FACE) is true
   - Expected: ctx.enable(WEBGL_SCISSOR_TEST) is true
   - Expected: ctx.enable(WEBGL_STENCIL_TEST) is true
   - Expected: ctx.is_enabled(WEBGL_BLEND) is true
   - Expected: ctx.is_enabled(WEBGL_DEPTH_TEST) is true
   - Expected: ctx.is_enabled(WEBGL_POLYGON_OFFSET_FILL) is true
   - Expected: ctx.is_enabled(WEBGL_SAMPLE_ALPHA_TO_COVERAGE) is true
   - Expected: ctx.is_enabled(WEBGL_SAMPLE_COVERAGE) is true
   - Expected: ctx.is_enabled(WEBGL_STENCIL_TEST) is true
   - Expected: ctx.disable(WEBGL_BLEND) is true
   - Expected: ctx.is_enabled(WEBGL_BLEND) is false
   - Expected: ctx.disable(WEBGL_DITHER) is true
   - Expected: ctx.is_enabled(WEBGL_DITHER) is false
   - Expected: ctx.enable(999) is false
   - Expected: ctx.get_error() equals `WEBGL_INVALID_ENUM`


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ctx = webgl_create_context(1, 320, 240)
expect(ctx.is_enabled(WEBGL_BLEND)).to_equal(false)
expect(ctx.is_enabled(WEBGL_DITHER)).to_equal(true)
expect(ctx.enable(WEBGL_BLEND)).to_equal(true)
expect(ctx.enable(WEBGL_DEPTH_TEST)).to_equal(true)
expect(ctx.enable(WEBGL_POLYGON_OFFSET_FILL)).to_equal(true)
expect(ctx.enable(WEBGL_SAMPLE_ALPHA_TO_COVERAGE)).to_equal(true)
expect(ctx.enable(WEBGL_SAMPLE_COVERAGE)).to_equal(true)
expect(ctx.enable(WEBGL_CULL_FACE)).to_equal(true)
expect(ctx.enable(WEBGL_SCISSOR_TEST)).to_equal(true)
expect(ctx.enable(WEBGL_STENCIL_TEST)).to_equal(true)
expect(ctx.is_enabled(WEBGL_BLEND)).to_equal(true)
expect(ctx.is_enabled(WEBGL_DEPTH_TEST)).to_equal(true)
expect(ctx.is_enabled(WEBGL_POLYGON_OFFSET_FILL)).to_equal(true)
expect(ctx.is_enabled(WEBGL_SAMPLE_ALPHA_TO_COVERAGE)).to_equal(true)
expect(ctx.is_enabled(WEBGL_SAMPLE_COVERAGE)).to_equal(true)
expect(ctx.is_enabled(WEBGL_STENCIL_TEST)).to_equal(true)
expect(ctx.disable(WEBGL_BLEND)).to_equal(true)
expect(ctx.is_enabled(WEBGL_BLEND)).to_equal(false)
expect(ctx.disable(WEBGL_DITHER)).to_equal(true)
expect(ctx.is_enabled(WEBGL_DITHER)).to_equal(false)
expect(ctx.enable(999)).to_equal(false)
expect(ctx.get_error()).to_equal(WEBGL_INVALID_ENUM)
```

</details>

#### tracks depth cull blend and scissor state

1. var ctx = webgl create context
   - Expected: ctx.depth_func_value equals `WEBGL_LESS`
   - Expected: ctx.cull_face_mode equals `WEBGL_BACK`
   - Expected: ctx.front_face_mode equals `WEBGL_CCW`
   - Expected: ctx.polygon_offset_factor equals `0.0`
   - Expected: ctx.polygon_offset_units equals `0.0`
   - Expected: ctx.sample_coverage_value equals `1.0`
   - Expected: ctx.sample_coverage_invert is false
   - Expected: ctx.blend_color_red equals `0.0`
   - Expected: ctx.blend_color_alpha equals `0.0`
   - Expected: ctx.line_width_value equals `1.0`
   - Expected: ctx.blend_src_factor equals `WEBGL_ONE`
   - Expected: ctx.dither_enabled is true
   - Expected: ctx.blend_dst_factor equals `WEBGL_ZERO`
   - Expected: ctx.blend_equation_rgb equals `WEBGL_FUNC_ADD`
   - Expected: ctx.blend_equation_alpha equals `WEBGL_FUNC_ADD`
   - Expected: ctx.stencil_func_value equals `WEBGL_ALWAYS`
   - Expected: ctx.stencil_ref_value equals `0`
   - Expected: ctx.stencil_value_mask equals `-1`
   - Expected: ctx.stencil_back_func_value equals `WEBGL_ALWAYS`
   - Expected: ctx.stencil_back_ref_value equals `0`
   - Expected: ctx.stencil_back_value_mask equals `-1`
   - Expected: ctx.stencil_fail_op equals `WEBGL_KEEP`
   - Expected: ctx.stencil_zfail_op equals `WEBGL_KEEP`
   - Expected: ctx.stencil_zpass_op equals `WEBGL_KEEP`
   - Expected: ctx.stencil_back_fail_op equals `WEBGL_KEEP`
   - Expected: ctx.stencil_back_zfail_op equals `WEBGL_KEEP`
   - Expected: ctx.stencil_back_zpass_op equals `WEBGL_KEEP`
   - Expected: ctx.scissor_width equals `320`
   - Expected: ctx.depth_func(WEBGL_LEQUAL) is true
   - Expected: ctx.stencil_func(WEBGL_EQUAL, 3, 15) is true
   - Expected: ctx.stencil_op(WEBGL_KEEP, WEBGL_REPLACE, WEBGL_INCR_WRAP) is true
   - Expected: ctx.cull_face(WEBGL_FRONT_AND_BACK) is true
   - Expected: ctx.front_face(WEBGL_CW) is true
   - Expected: ctx.polygon_offset(1.25, -2.5) is true
   - Expected: ctx.sample_coverage(0.5, true) is true
   - Expected: ctx.blend_color(-1.0, 0.25, 0.75, 2.0) is true
   - Expected: ctx.line_width(2.0) is true
   - Expected: ctx.blend_func(WEBGL_SRC_ALPHA, WEBGL_ONE_MINUS_SRC_ALPHA) is true
   - Expected: ctx.blend_equation(WEBGL_FUNC_SUBTRACT) is true
   - Expected: ctx.scissor(4, 8, 100, 50) is true
   - Expected: ctx.depth_func_value equals `WEBGL_LEQUAL`
   - Expected: ctx.cull_face_mode equals `WEBGL_FRONT_AND_BACK`
   - Expected: ctx.front_face_mode equals `WEBGL_CW`
   - Expected: ctx.polygon_offset_factor equals `1.25`
   - Expected: ctx.polygon_offset_units equals `-2.5`
   - Expected: ctx.sample_coverage_value equals `0.5`
   - Expected: ctx.sample_coverage_invert is true
   - Expected: ctx.blend_color_red equals `0.0`
   - Expected: ctx.blend_color_green equals `0.25`
   - Expected: ctx.blend_color_blue equals `0.75`
   - Expected: ctx.blend_color_alpha equals `1.0`
   - Expected: ctx.line_width_value equals `2.0`
   - Expected: ctx.blend_src_factor equals `WEBGL_SRC_ALPHA`
   - Expected: ctx.blend_dst_factor equals `WEBGL_ONE_MINUS_SRC_ALPHA`
   - Expected: ctx.blend_src_alpha_factor equals `WEBGL_SRC_ALPHA`
   - Expected: ctx.blend_dst_alpha_factor equals `WEBGL_ONE_MINUS_SRC_ALPHA`
   - Expected: ctx.blend_equation_rgb equals `WEBGL_FUNC_SUBTRACT`
   - Expected: ctx.blend_equation_alpha equals `WEBGL_FUNC_SUBTRACT`
   - Expected: ctx.stencil_func_value equals `WEBGL_EQUAL`
   - Expected: ctx.stencil_ref_value equals `3`
   - Expected: ctx.stencil_value_mask equals `15`
   - Expected: ctx.stencil_back_func_value equals `WEBGL_EQUAL`
   - Expected: ctx.stencil_back_ref_value equals `3`
   - Expected: ctx.stencil_back_value_mask equals `15`
   - Expected: ctx.stencil_fail_op equals `WEBGL_KEEP`
   - Expected: ctx.stencil_zfail_op equals `WEBGL_REPLACE`
   - Expected: ctx.stencil_zpass_op equals `WEBGL_INCR_WRAP`
   - Expected: ctx.stencil_back_fail_op equals `WEBGL_KEEP`
   - Expected: ctx.stencil_back_zfail_op equals `WEBGL_REPLACE`
   - Expected: ctx.stencil_back_zpass_op equals `WEBGL_INCR_WRAP`
   - Expected: ctx.scissor_x equals `4`
   - Expected: ctx.scissor_height equals `50`


<details>
<summary>Executable SSpec</summary>

Runnable source: 73 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ctx = webgl_create_context(1, 320, 240)
expect(ctx.depth_func_value).to_equal(WEBGL_LESS)
expect(ctx.cull_face_mode).to_equal(WEBGL_BACK)
expect(ctx.front_face_mode).to_equal(WEBGL_CCW)
expect(ctx.polygon_offset_factor).to_equal(0.0)
expect(ctx.polygon_offset_units).to_equal(0.0)
expect(ctx.sample_coverage_value).to_equal(1.0)
expect(ctx.sample_coverage_invert).to_equal(false)
expect(ctx.blend_color_red).to_equal(0.0)
expect(ctx.blend_color_alpha).to_equal(0.0)
expect(ctx.line_width_value).to_equal(1.0)
expect(ctx.blend_src_factor).to_equal(WEBGL_ONE)
expect(ctx.dither_enabled).to_equal(true)
expect(ctx.blend_dst_factor).to_equal(WEBGL_ZERO)
expect(ctx.blend_equation_rgb).to_equal(WEBGL_FUNC_ADD)
expect(ctx.blend_equation_alpha).to_equal(WEBGL_FUNC_ADD)
expect(ctx.stencil_func_value).to_equal(WEBGL_ALWAYS)
expect(ctx.stencil_ref_value).to_equal(0)
expect(ctx.stencil_value_mask).to_equal(-1)
expect(ctx.stencil_back_func_value).to_equal(WEBGL_ALWAYS)
expect(ctx.stencil_back_ref_value).to_equal(0)
expect(ctx.stencil_back_value_mask).to_equal(-1)
expect(ctx.stencil_fail_op).to_equal(WEBGL_KEEP)
expect(ctx.stencil_zfail_op).to_equal(WEBGL_KEEP)
expect(ctx.stencil_zpass_op).to_equal(WEBGL_KEEP)
expect(ctx.stencil_back_fail_op).to_equal(WEBGL_KEEP)
expect(ctx.stencil_back_zfail_op).to_equal(WEBGL_KEEP)
expect(ctx.stencil_back_zpass_op).to_equal(WEBGL_KEEP)
expect(ctx.scissor_width).to_equal(320)
expect(ctx.depth_func(WEBGL_LEQUAL)).to_equal(true)
expect(ctx.stencil_func(WEBGL_EQUAL, 3, 15)).to_equal(true)
expect(ctx.stencil_op(WEBGL_KEEP, WEBGL_REPLACE, WEBGL_INCR_WRAP)).to_equal(true)
expect(ctx.cull_face(WEBGL_FRONT_AND_BACK)).to_equal(true)
expect(ctx.front_face(WEBGL_CW)).to_equal(true)
expect(ctx.polygon_offset(1.25, -2.5)).to_equal(true)
expect(ctx.sample_coverage(0.5, true)).to_equal(true)
expect(ctx.blend_color(-1.0, 0.25, 0.75, 2.0)).to_equal(true)
expect(ctx.line_width(2.0)).to_equal(true)
expect(ctx.blend_func(WEBGL_SRC_ALPHA, WEBGL_ONE_MINUS_SRC_ALPHA)).to_equal(true)
expect(ctx.blend_equation(WEBGL_FUNC_SUBTRACT)).to_equal(true)
expect(ctx.scissor(4, 8, 100, 50)).to_equal(true)
expect(ctx.depth_func_value).to_equal(WEBGL_LEQUAL)
expect(ctx.cull_face_mode).to_equal(WEBGL_FRONT_AND_BACK)
expect(ctx.front_face_mode).to_equal(WEBGL_CW)
expect(ctx.polygon_offset_factor).to_equal(1.25)
expect(ctx.polygon_offset_units).to_equal(-2.5)
expect(ctx.sample_coverage_value).to_equal(0.5)
expect(ctx.sample_coverage_invert).to_equal(true)
expect(ctx.blend_color_red).to_equal(0.0)
expect(ctx.blend_color_green).to_equal(0.25)
expect(ctx.blend_color_blue).to_equal(0.75)
expect(ctx.blend_color_alpha).to_equal(1.0)
expect(ctx.line_width_value).to_equal(2.0)
expect(ctx.blend_src_factor).to_equal(WEBGL_SRC_ALPHA)
expect(ctx.blend_dst_factor).to_equal(WEBGL_ONE_MINUS_SRC_ALPHA)
expect(ctx.blend_src_alpha_factor).to_equal(WEBGL_SRC_ALPHA)
expect(ctx.blend_dst_alpha_factor).to_equal(WEBGL_ONE_MINUS_SRC_ALPHA)
expect(ctx.blend_equation_rgb).to_equal(WEBGL_FUNC_SUBTRACT)
expect(ctx.blend_equation_alpha).to_equal(WEBGL_FUNC_SUBTRACT)
expect(ctx.stencil_func_value).to_equal(WEBGL_EQUAL)
expect(ctx.stencil_ref_value).to_equal(3)
expect(ctx.stencil_value_mask).to_equal(15)
expect(ctx.stencil_back_func_value).to_equal(WEBGL_EQUAL)
expect(ctx.stencil_back_ref_value).to_equal(3)
expect(ctx.stencil_back_value_mask).to_equal(15)
expect(ctx.stencil_fail_op).to_equal(WEBGL_KEEP)
expect(ctx.stencil_zfail_op).to_equal(WEBGL_REPLACE)
expect(ctx.stencil_zpass_op).to_equal(WEBGL_INCR_WRAP)
expect(ctx.stencil_back_fail_op).to_equal(WEBGL_KEEP)
expect(ctx.stencil_back_zfail_op).to_equal(WEBGL_REPLACE)
expect(ctx.stencil_back_zpass_op).to_equal(WEBGL_INCR_WRAP)
expect(ctx.scissor_x).to_equal(4)
expect(ctx.scissor_height).to_equal(50)
```

</details>

#### tracks separate front and back stencil state

1. var ctx = webgl create context
   - Expected: ctx.stencil_func_separate(WEBGL_BACK, WEBGL_EQUAL, 4, 31) is true
   - Expected: ctx.stencil_func_value equals `WEBGL_ALWAYS`
   - Expected: ctx.stencil_back_func_value equals `WEBGL_EQUAL`
   - Expected: ctx.stencil_back_ref_value equals `4`
   - Expected: ctx.stencil_back_value_mask equals `31`
   - Expected: ctx.stencil_op_separate(WEBGL_FRONT, WEBGL_REPLACE, WEBGL_KEEP, WEBGL_INCR_WRAP) is true
   - Expected: ctx.stencil_fail_op equals `WEBGL_REPLACE`
   - Expected: ctx.stencil_zpass_op equals `WEBGL_INCR_WRAP`
   - Expected: ctx.stencil_back_fail_op equals `WEBGL_KEEP`
   - Expected: ctx.render_commands[0].kind equals `WEBGL_RENDER_COMMAND_STENCIL_FUNC_SEPARATE`
   - Expected: ctx.render_commands[0].target equals `WEBGL_BACK`
   - Expected: ctx.render_commands[0].mode equals `WEBGL_EQUAL`
   - Expected: ctx.render_commands[0].first equals `4`
   - Expected: ctx.render_commands[0].mask equals `31`
   - Expected: ctx.render_commands[1].kind equals `WEBGL_RENDER_COMMAND_STENCIL_OP_SEPARATE`
   - Expected: ctx.render_commands[1].target equals `WEBGL_FRONT`
   - Expected: ctx.render_commands[1].mode equals `WEBGL_REPLACE`
   - Expected: ctx.render_commands[1].first equals `WEBGL_KEEP`
   - Expected: ctx.render_commands[1].element_type equals `WEBGL_INCR_WRAP`
   - Expected: ctx.stencil_func_separate(WEBGL_FRONT_AND_BACK, WEBGL_ALWAYS, 1, 7) is true
   - Expected: ctx.stencil_func_value equals `WEBGL_ALWAYS`
   - Expected: ctx.stencil_back_func_value equals `WEBGL_ALWAYS`
   - Expected: ctx.stencil_back_ref_value equals `1`
   - Expected: ctx.get_parameter(WEBGL_STENCIL_BACK_FUNC).int_value equals `WEBGL_ALWAYS`
   - Expected: ctx.get_parameter(WEBGL_STENCIL_BACK_REF).int_value equals `1`
   - Expected: ctx.get_parameter(WEBGL_STENCIL_BACK_VALUE_MASK).int_value equals `7`


<details>
<summary>Executable SSpec</summary>

Runnable source: 27 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ctx = webgl_create_context(1, 320, 240)
expect(ctx.stencil_func_separate(WEBGL_BACK, WEBGL_EQUAL, 4, 31)).to_equal(true)
expect(ctx.stencil_func_value).to_equal(WEBGL_ALWAYS)
expect(ctx.stencil_back_func_value).to_equal(WEBGL_EQUAL)
expect(ctx.stencil_back_ref_value).to_equal(4)
expect(ctx.stencil_back_value_mask).to_equal(31)
expect(ctx.stencil_op_separate(WEBGL_FRONT, WEBGL_REPLACE, WEBGL_KEEP, WEBGL_INCR_WRAP)).to_equal(true)
expect(ctx.stencil_fail_op).to_equal(WEBGL_REPLACE)
expect(ctx.stencil_zpass_op).to_equal(WEBGL_INCR_WRAP)
expect(ctx.stencil_back_fail_op).to_equal(WEBGL_KEEP)
expect(ctx.render_commands[0].kind).to_equal(WEBGL_RENDER_COMMAND_STENCIL_FUNC_SEPARATE)
expect(ctx.render_commands[0].target).to_equal(WEBGL_BACK)
expect(ctx.render_commands[0].mode).to_equal(WEBGL_EQUAL)
expect(ctx.render_commands[0].first).to_equal(4)
expect(ctx.render_commands[0].mask).to_equal(31)
expect(ctx.render_commands[1].kind).to_equal(WEBGL_RENDER_COMMAND_STENCIL_OP_SEPARATE)
expect(ctx.render_commands[1].target).to_equal(WEBGL_FRONT)
expect(ctx.render_commands[1].mode).to_equal(WEBGL_REPLACE)
expect(ctx.render_commands[1].first).to_equal(WEBGL_KEEP)
expect(ctx.render_commands[1].element_type).to_equal(WEBGL_INCR_WRAP)
expect(ctx.stencil_func_separate(WEBGL_FRONT_AND_BACK, WEBGL_ALWAYS, 1, 7)).to_equal(true)
expect(ctx.stencil_func_value).to_equal(WEBGL_ALWAYS)
expect(ctx.stencil_back_func_value).to_equal(WEBGL_ALWAYS)
expect(ctx.stencil_back_ref_value).to_equal(1)
expect(ctx.get_parameter(WEBGL_STENCIL_BACK_FUNC).int_value).to_equal(WEBGL_ALWAYS)
expect(ctx.get_parameter(WEBGL_STENCIL_BACK_REF).int_value).to_equal(1)
expect(ctx.get_parameter(WEBGL_STENCIL_BACK_VALUE_MASK).int_value).to_equal(7)
```

</details>

#### validates render state enums and dimensions

1. var ctx = webgl create context
   - Expected: ctx.depth_func(999) is false
   - Expected: ctx.get_error() equals `WEBGL_INVALID_ENUM`
   - Expected: ctx.cull_face(999) is false
   - Expected: ctx.get_error() equals `WEBGL_INVALID_ENUM`
   - Expected: ctx.front_face(WEBGL_FRONT) is false
   - Expected: ctx.get_error() equals `WEBGL_INVALID_ENUM`
   - Expected: ctx.line_width(0.0) is false
   - Expected: ctx.get_error() equals `WEBGL_INVALID_VALUE`
   - Expected: ctx.blend_func(WEBGL_SRC_ALPHA, 999) is false
   - Expected: ctx.get_error() equals `WEBGL_INVALID_ENUM`
   - Expected: ctx.blend_func_separate(WEBGL_SRC_ALPHA, WEBGL_ONE_MINUS_SRC_ALPHA, 999, WEBGL_ZERO) is false
   - Expected: ctx.get_error() equals `WEBGL_INVALID_ENUM`
   - Expected: ctx.blend_equation(999) is false
   - Expected: ctx.get_error() equals `WEBGL_INVALID_ENUM`
   - Expected: ctx.blend_equation_separate(WEBGL_FUNC_ADD, 999) is false
   - Expected: ctx.get_error() equals `WEBGL_INVALID_ENUM`
   - Expected: ctx.stencil_func(999, 0, 255) is false
   - Expected: ctx.get_error() equals `WEBGL_INVALID_ENUM`
   - Expected: ctx.stencil_func(WEBGL_ALWAYS, -1, 255) is false
   - Expected: ctx.get_error() equals `WEBGL_INVALID_VALUE`
   - Expected: ctx.stencil_func(WEBGL_ALWAYS, 0, -1) is false
   - Expected: ctx.get_error() equals `WEBGL_INVALID_VALUE`
   - Expected: ctx.stencil_op(WEBGL_KEEP, 999, WEBGL_KEEP) is false
   - Expected: ctx.get_error() equals `WEBGL_INVALID_ENUM`
   - Expected: ctx.stencil_func_separate(999, WEBGL_ALWAYS, 0, 255) is false
   - Expected: ctx.get_error() equals `WEBGL_INVALID_ENUM`
   - Expected: ctx.stencil_func_separate(WEBGL_BACK, WEBGL_ALWAYS, -1, 255) is false
   - Expected: ctx.get_error() equals `WEBGL_INVALID_VALUE`
   - Expected: ctx.stencil_op_separate(WEBGL_BACK, WEBGL_KEEP, 999, WEBGL_KEEP) is false
   - Expected: ctx.get_error() equals `WEBGL_INVALID_ENUM`
   - Expected: ctx.scissor(0, 0, -1, 10) is false
   - Expected: ctx.get_error() equals `WEBGL_INVALID_VALUE`


<details>
<summary>Executable SSpec</summary>

Runnable source: 33 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ctx = webgl_create_context(1, 320, 240)
expect(ctx.depth_func(999)).to_equal(false)
expect(ctx.get_error()).to_equal(WEBGL_INVALID_ENUM)
expect(ctx.cull_face(999)).to_equal(false)
expect(ctx.get_error()).to_equal(WEBGL_INVALID_ENUM)
expect(ctx.front_face(WEBGL_FRONT)).to_equal(false)
expect(ctx.get_error()).to_equal(WEBGL_INVALID_ENUM)
expect(ctx.line_width(0.0)).to_equal(false)
expect(ctx.get_error()).to_equal(WEBGL_INVALID_VALUE)
expect(ctx.blend_func(WEBGL_SRC_ALPHA, 999)).to_equal(false)
expect(ctx.get_error()).to_equal(WEBGL_INVALID_ENUM)
expect(ctx.blend_func_separate(WEBGL_SRC_ALPHA, WEBGL_ONE_MINUS_SRC_ALPHA, 999, WEBGL_ZERO)).to_equal(false)
expect(ctx.get_error()).to_equal(WEBGL_INVALID_ENUM)
expect(ctx.blend_equation(999)).to_equal(false)
expect(ctx.get_error()).to_equal(WEBGL_INVALID_ENUM)
expect(ctx.blend_equation_separate(WEBGL_FUNC_ADD, 999)).to_equal(false)
expect(ctx.get_error()).to_equal(WEBGL_INVALID_ENUM)
expect(ctx.stencil_func(999, 0, 255)).to_equal(false)
expect(ctx.get_error()).to_equal(WEBGL_INVALID_ENUM)
expect(ctx.stencil_func(WEBGL_ALWAYS, -1, 255)).to_equal(false)
expect(ctx.get_error()).to_equal(WEBGL_INVALID_VALUE)
expect(ctx.stencil_func(WEBGL_ALWAYS, 0, -1)).to_equal(false)
expect(ctx.get_error()).to_equal(WEBGL_INVALID_VALUE)
expect(ctx.stencil_op(WEBGL_KEEP, 999, WEBGL_KEEP)).to_equal(false)
expect(ctx.get_error()).to_equal(WEBGL_INVALID_ENUM)
expect(ctx.stencil_func_separate(999, WEBGL_ALWAYS, 0, 255)).to_equal(false)
expect(ctx.get_error()).to_equal(WEBGL_INVALID_ENUM)
expect(ctx.stencil_func_separate(WEBGL_BACK, WEBGL_ALWAYS, -1, 255)).to_equal(false)
expect(ctx.get_error()).to_equal(WEBGL_INVALID_VALUE)
expect(ctx.stencil_op_separate(WEBGL_BACK, WEBGL_KEEP, 999, WEBGL_KEEP)).to_equal(false)
expect(ctx.get_error()).to_equal(WEBGL_INVALID_ENUM)
expect(ctx.scissor(0, 0, -1, 10)).to_equal(false)
expect(ctx.get_error()).to_equal(WEBGL_INVALID_VALUE)
```

</details>

#### reports render state through get parameter

1. var ctx = webgl create context
   - Expected: ctx.get_parameter(WEBGL_VIEWPORT).int_values[2] equals `320`
   - Expected: ctx.get_parameter(WEBGL_SCISSOR_BOX).int_values[3] equals `240`
   - Expected: ctx.get_parameter(WEBGL_COLOR_CLEAR_VALUE).float_values[0] equals `0.0`
   - Expected: ctx.get_parameter(WEBGL_LINE_WIDTH).float_value equals `1.0`
   - Expected: ctx.get_parameter(WEBGL_ALIASED_LINE_WIDTH_RANGE).float_values[0] equals `1.0`
   - Expected: ctx.get_parameter(WEBGL_ALIASED_LINE_WIDTH_RANGE).float_values[1] equals `1.0`
   - Expected: ctx.get_parameter(WEBGL_DEPTH_CLEAR_VALUE).float_value equals `1.0`
   - Expected: ctx.get_parameter(WEBGL_DEPTH_RANGE).float_values[0] equals `0.0`
   - Expected: ctx.get_parameter(WEBGL_DEPTH_RANGE).float_values[1] equals `1.0`
   - Expected: ctx.get_parameter(WEBGL_STENCIL_CLEAR_VALUE).int_value equals `0`
   - Expected: ctx.get_parameter(WEBGL_BLEND).bool_value is false
   - Expected: ctx.get_parameter(WEBGL_DITHER).bool_value is true
   - Expected: ctx.get_parameter(WEBGL_POLYGON_OFFSET_FILL).bool_value is false
   - Expected: ctx.get_parameter(WEBGL_POLYGON_OFFSET_FACTOR).float_value equals `0.0`
   - Expected: ctx.get_parameter(WEBGL_POLYGON_OFFSET_UNITS).float_value equals `0.0`
   - Expected: ctx.get_parameter(WEBGL_SAMPLE_COVERAGE_VALUE).float_value equals `1.0`
   - Expected: ctx.get_parameter(WEBGL_SAMPLE_COVERAGE_INVERT).bool_value is false
   - Expected: ctx.get_parameter(WEBGL_BLEND_COLOR).float_values[0] equals `0.0`
   - Expected: ctx.get_parameter(WEBGL_BLEND_COLOR).float_values[3] equals `0.0`
   - Expected: ctx.get_parameter(WEBGL_STENCIL_TEST).bool_value is false
   - Expected: ctx.get_parameter(WEBGL_STENCIL_FUNC).int_value equals `WEBGL_ALWAYS`
   - Expected: ctx.get_parameter(WEBGL_STENCIL_REF).int_value equals `0`
   - Expected: ctx.get_parameter(WEBGL_STENCIL_VALUE_MASK).int_value equals `-1`
   - Expected: ctx.get_parameter(WEBGL_STENCIL_FAIL).int_value equals `WEBGL_KEEP`
   - Expected: ctx.get_parameter(WEBGL_STENCIL_PASS_DEPTH_FAIL).int_value equals `WEBGL_KEEP`
   - Expected: ctx.get_parameter(WEBGL_STENCIL_PASS_DEPTH_PASS).int_value equals `WEBGL_KEEP`
   - Expected: ctx.clear_color(0.25, 0.5, 0.75, 1.0) is true
   - Expected: ctx.line_width(3.0) is true
   - Expected: ctx.clear_depth(0.4) is true
   - Expected: ctx.depth_range(0.2, 0.8) is true
   - Expected: ctx.clear_stencil(9) is true
   - Expected: ctx.enable(WEBGL_BLEND) is true
   - Expected: ctx.enable(WEBGL_POLYGON_OFFSET_FILL) is true
   - Expected: ctx.enable(WEBGL_SAMPLE_COVERAGE) is true
   - Expected: ctx.enable(WEBGL_STENCIL_TEST) is true
   - Expected: ctx.depth_func(WEBGL_LEQUAL) is true
   - Expected: ctx.stencil_func(WEBGL_EQUAL, 2, 7) is true
   - Expected: ctx.stencil_op(WEBGL_REPLACE, WEBGL_KEEP, WEBGL_INCR_WRAP) is true
   - Expected: ctx.cull_face(WEBGL_FRONT_AND_BACK) is true
   - Expected: ctx.blend_func(WEBGL_SRC_ALPHA, WEBGL_ONE_MINUS_SRC_ALPHA) is true
   - Expected: ctx.blend_color(0.1, 0.2, 0.3, 0.4) is true
   - Expected: ctx.blend_equation_separate(WEBGL_FUNC_REVERSE_SUBTRACT, WEBGL_MAX) is true
   - Expected: ctx.scissor(4, 8, 100, 50) is true
   - Expected: ctx.get_parameter(WEBGL_COLOR_CLEAR_VALUE).float_values[0] equals `0.25`
   - Expected: ctx.get_parameter(WEBGL_COLOR_CLEAR_VALUE).float_values[3] equals `1.0`
   - Expected: ctx.get_parameter(WEBGL_LINE_WIDTH).float_value equals `3.0`
   - Expected: ctx.get_parameter(WEBGL_DEPTH_CLEAR_VALUE).float_value equals `0.4`
   - Expected: ctx.get_parameter(WEBGL_DEPTH_RANGE).float_values[0] equals `0.2`
   - Expected: ctx.get_parameter(WEBGL_DEPTH_RANGE).float_values[1] equals `0.8`
   - Expected: ctx.get_parameter(WEBGL_STENCIL_CLEAR_VALUE).int_value equals `9`
   - Expected: ctx.get_parameter(WEBGL_BLEND).bool_value is true
   - Expected: ctx.disable(WEBGL_DITHER) is true
   - Expected: ctx.get_parameter(WEBGL_DITHER).bool_value is false
   - Expected: ctx.get_parameter(WEBGL_POLYGON_OFFSET_FILL).bool_value is true
   - Expected: ctx.get_parameter(WEBGL_STENCIL_TEST).bool_value is true
   - Expected: ctx.get_parameter(WEBGL_DEPTH_FUNC).int_value equals `WEBGL_LEQUAL`
   - Expected: ctx.get_parameter(WEBGL_STENCIL_FUNC).int_value equals `WEBGL_EQUAL`
   - Expected: ctx.get_parameter(WEBGL_STENCIL_REF).int_value equals `2`
   - Expected: ctx.get_parameter(WEBGL_STENCIL_VALUE_MASK).int_value equals `7`
   - Expected: ctx.get_parameter(WEBGL_STENCIL_FAIL).int_value equals `WEBGL_REPLACE`
   - Expected: ctx.get_parameter(WEBGL_STENCIL_PASS_DEPTH_FAIL).int_value equals `WEBGL_KEEP`
   - Expected: ctx.get_parameter(WEBGL_STENCIL_PASS_DEPTH_PASS).int_value equals `WEBGL_INCR_WRAP`
   - Expected: ctx.get_parameter(WEBGL_CULL_FACE_MODE).int_value equals `WEBGL_FRONT_AND_BACK`
   - Expected: ctx.get_parameter(WEBGL_BLEND_SRC_RGB).int_value equals `WEBGL_SRC_ALPHA`
   - Expected: ctx.get_parameter(WEBGL_BLEND_DST_RGB).int_value equals `WEBGL_ONE_MINUS_SRC_ALPHA`
   - Expected: ctx.get_parameter(WEBGL_BLEND_SRC_ALPHA).int_value equals `WEBGL_SRC_ALPHA`
   - Expected: ctx.get_parameter(WEBGL_BLEND_DST_ALPHA).int_value equals `WEBGL_ONE_MINUS_SRC_ALPHA`
   - Expected: ctx.get_parameter(WEBGL_BLEND_EQUATION).int_value equals `WEBGL_FUNC_REVERSE_SUBTRACT`
   - Expected: ctx.get_parameter(WEBGL_BLEND_EQUATION_RGB).int_value equals `WEBGL_FUNC_REVERSE_SUBTRACT`
   - Expected: ctx.get_parameter(WEBGL_BLEND_EQUATION_ALPHA).int_value equals `WEBGL_MAX`
   - Expected: ctx.get_parameter(WEBGL_SCISSOR_BOX).int_values[0] equals `4`
   - Expected: ctx.get_parameter(WEBGL_FRONT_FACE).int_value equals `WEBGL_CCW`
   - Expected: ctx.front_face(WEBGL_CW) is true
   - Expected: ctx.polygon_offset(-1.5, 4.0) is true
   - Expected: ctx.sample_coverage(1.5, true) is true
   - Expected: ctx.get_parameter(WEBGL_FRONT_FACE).int_value equals `WEBGL_CW`
   - Expected: ctx.get_parameter(WEBGL_POLYGON_OFFSET_FACTOR).float_value equals `-1.5`
   - Expected: ctx.get_parameter(WEBGL_POLYGON_OFFSET_UNITS).float_value equals `4.0`
   - Expected: ctx.get_parameter(WEBGL_SAMPLE_COVERAGE).bool_value is true
   - Expected: ctx.get_parameter(WEBGL_SAMPLE_COVERAGE_VALUE).float_value equals `1.0`
   - Expected: ctx.get_parameter(WEBGL_SAMPLE_COVERAGE_INVERT).bool_value is true
   - Expected: ctx.get_parameter(WEBGL_BLEND_COLOR).float_values[2] equals `0.3`
   - Expected: ctx.blend_func(WEBGL_CONSTANT_COLOR, WEBGL_ONE_MINUS_SRC_ALPHA) is true
   - Expected: ctx.get_parameter(WEBGL_BLEND_SRC_RGB).int_value equals `WEBGL_CONSTANT_COLOR`
   - Expected: ctx.get_parameter(WEBGL_BLEND_DST_RGB).int_value equals `WEBGL_ONE_MINUS_SRC_ALPHA`
   - Expected: ctx.get_parameter(999).int_value equals `0`
   - Expected: ctx.get_error() equals `WEBGL_INVALID_ENUM`


<details>
<summary>Executable SSpec</summary>

Runnable source: 88 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ctx = webgl_create_context(1, 320, 240)
expect(ctx.get_parameter(WEBGL_VIEWPORT).int_values[2]).to_equal(320)
expect(ctx.get_parameter(WEBGL_SCISSOR_BOX).int_values[3]).to_equal(240)
expect(ctx.get_parameter(WEBGL_COLOR_CLEAR_VALUE).float_values[0]).to_equal(0.0)
expect(ctx.get_parameter(WEBGL_LINE_WIDTH).float_value).to_equal(1.0)
expect(ctx.get_parameter(WEBGL_ALIASED_LINE_WIDTH_RANGE).float_values[0]).to_equal(1.0)
expect(ctx.get_parameter(WEBGL_ALIASED_LINE_WIDTH_RANGE).float_values[1]).to_equal(1.0)
expect(ctx.get_parameter(WEBGL_DEPTH_CLEAR_VALUE).float_value).to_equal(1.0)
expect(ctx.get_parameter(WEBGL_DEPTH_RANGE).float_values[0]).to_equal(0.0)
expect(ctx.get_parameter(WEBGL_DEPTH_RANGE).float_values[1]).to_equal(1.0)
expect(ctx.get_parameter(WEBGL_STENCIL_CLEAR_VALUE).int_value).to_equal(0)
expect(ctx.get_parameter(WEBGL_BLEND).bool_value).to_equal(false)
expect(ctx.get_parameter(WEBGL_DITHER).bool_value).to_equal(true)
expect(ctx.get_parameter(WEBGL_POLYGON_OFFSET_FILL).bool_value).to_equal(false)
expect(ctx.get_parameter(WEBGL_POLYGON_OFFSET_FACTOR).float_value).to_equal(0.0)
expect(ctx.get_parameter(WEBGL_POLYGON_OFFSET_UNITS).float_value).to_equal(0.0)
expect(ctx.get_parameter(WEBGL_SAMPLE_COVERAGE_VALUE).float_value).to_equal(1.0)
expect(ctx.get_parameter(WEBGL_SAMPLE_COVERAGE_INVERT).bool_value).to_equal(false)
expect(ctx.get_parameter(WEBGL_BLEND_COLOR).float_values[0]).to_equal(0.0)
expect(ctx.get_parameter(WEBGL_BLEND_COLOR).float_values[3]).to_equal(0.0)
expect(ctx.get_parameter(WEBGL_STENCIL_TEST).bool_value).to_equal(false)
expect(ctx.get_parameter(WEBGL_STENCIL_FUNC).int_value).to_equal(WEBGL_ALWAYS)
expect(ctx.get_parameter(WEBGL_STENCIL_REF).int_value).to_equal(0)
expect(ctx.get_parameter(WEBGL_STENCIL_VALUE_MASK).int_value).to_equal(-1)
expect(ctx.get_parameter(WEBGL_STENCIL_FAIL).int_value).to_equal(WEBGL_KEEP)
expect(ctx.get_parameter(WEBGL_STENCIL_PASS_DEPTH_FAIL).int_value).to_equal(WEBGL_KEEP)
expect(ctx.get_parameter(WEBGL_STENCIL_PASS_DEPTH_PASS).int_value).to_equal(WEBGL_KEEP)
expect(ctx.clear_color(0.25, 0.5, 0.75, 1.0)).to_equal(true)
expect(ctx.line_width(3.0)).to_equal(true)
expect(ctx.clear_depth(0.4)).to_equal(true)
expect(ctx.depth_range(0.2, 0.8)).to_equal(true)
expect(ctx.clear_stencil(9)).to_equal(true)
expect(ctx.enable(WEBGL_BLEND)).to_equal(true)
expect(ctx.enable(WEBGL_POLYGON_OFFSET_FILL)).to_equal(true)
expect(ctx.enable(WEBGL_SAMPLE_COVERAGE)).to_equal(true)
expect(ctx.enable(WEBGL_STENCIL_TEST)).to_equal(true)
expect(ctx.depth_func(WEBGL_LEQUAL)).to_equal(true)
expect(ctx.stencil_func(WEBGL_EQUAL, 2, 7)).to_equal(true)
expect(ctx.stencil_op(WEBGL_REPLACE, WEBGL_KEEP, WEBGL_INCR_WRAP)).to_equal(true)
expect(ctx.cull_face(WEBGL_FRONT_AND_BACK)).to_equal(true)
expect(ctx.blend_func(WEBGL_SRC_ALPHA, WEBGL_ONE_MINUS_SRC_ALPHA)).to_equal(true)
expect(ctx.blend_color(0.1, 0.2, 0.3, 0.4)).to_equal(true)
expect(ctx.blend_equation_separate(WEBGL_FUNC_REVERSE_SUBTRACT, WEBGL_MAX)).to_equal(true)
expect(ctx.scissor(4, 8, 100, 50)).to_equal(true)
expect(ctx.get_parameter(WEBGL_COLOR_CLEAR_VALUE).float_values[0]).to_equal(0.25)
expect(ctx.get_parameter(WEBGL_COLOR_CLEAR_VALUE).float_values[3]).to_equal(1.0)
expect(ctx.get_parameter(WEBGL_LINE_WIDTH).float_value).to_equal(3.0)
expect(ctx.get_parameter(WEBGL_DEPTH_CLEAR_VALUE).float_value).to_equal(0.4)
expect(ctx.get_parameter(WEBGL_DEPTH_RANGE).float_values[0]).to_equal(0.2)
expect(ctx.get_parameter(WEBGL_DEPTH_RANGE).float_values[1]).to_equal(0.8)
expect(ctx.get_parameter(WEBGL_STENCIL_CLEAR_VALUE).int_value).to_equal(9)
expect(ctx.get_parameter(WEBGL_BLEND).bool_value).to_equal(true)
expect(ctx.disable(WEBGL_DITHER)).to_equal(true)
expect(ctx.get_parameter(WEBGL_DITHER).bool_value).to_equal(false)
expect(ctx.get_parameter(WEBGL_POLYGON_OFFSET_FILL).bool_value).to_equal(true)
expect(ctx.get_parameter(WEBGL_STENCIL_TEST).bool_value).to_equal(true)
expect(ctx.get_parameter(WEBGL_DEPTH_FUNC).int_value).to_equal(WEBGL_LEQUAL)
expect(ctx.get_parameter(WEBGL_STENCIL_FUNC).int_value).to_equal(WEBGL_EQUAL)
expect(ctx.get_parameter(WEBGL_STENCIL_REF).int_value).to_equal(2)
expect(ctx.get_parameter(WEBGL_STENCIL_VALUE_MASK).int_value).to_equal(7)
expect(ctx.get_parameter(WEBGL_STENCIL_FAIL).int_value).to_equal(WEBGL_REPLACE)
expect(ctx.get_parameter(WEBGL_STENCIL_PASS_DEPTH_FAIL).int_value).to_equal(WEBGL_KEEP)
expect(ctx.get_parameter(WEBGL_STENCIL_PASS_DEPTH_PASS).int_value).to_equal(WEBGL_INCR_WRAP)
expect(ctx.get_parameter(WEBGL_CULL_FACE_MODE).int_value).to_equal(WEBGL_FRONT_AND_BACK)
expect(ctx.get_parameter(WEBGL_BLEND_SRC_RGB).int_value).to_equal(WEBGL_SRC_ALPHA)
expect(ctx.get_parameter(WEBGL_BLEND_DST_RGB).int_value).to_equal(WEBGL_ONE_MINUS_SRC_ALPHA)
expect(ctx.get_parameter(WEBGL_BLEND_SRC_ALPHA).int_value).to_equal(WEBGL_SRC_ALPHA)
expect(ctx.get_parameter(WEBGL_BLEND_DST_ALPHA).int_value).to_equal(WEBGL_ONE_MINUS_SRC_ALPHA)
expect(ctx.get_parameter(WEBGL_BLEND_EQUATION).int_value).to_equal(WEBGL_FUNC_REVERSE_SUBTRACT)
expect(ctx.get_parameter(WEBGL_BLEND_EQUATION_RGB).int_value).to_equal(WEBGL_FUNC_REVERSE_SUBTRACT)
expect(ctx.get_parameter(WEBGL_BLEND_EQUATION_ALPHA).int_value).to_equal(WEBGL_MAX)
expect(ctx.get_parameter(WEBGL_SCISSOR_BOX).int_values[0]).to_equal(4)
expect(ctx.get_parameter(WEBGL_FRONT_FACE).int_value).to_equal(WEBGL_CCW)
expect(ctx.front_face(WEBGL_CW)).to_equal(true)
expect(ctx.polygon_offset(-1.5, 4.0)).to_equal(true)
expect(ctx.sample_coverage(1.5, true)).to_equal(true)
expect(ctx.get_parameter(WEBGL_FRONT_FACE).int_value).to_equal(WEBGL_CW)
expect(ctx.get_parameter(WEBGL_POLYGON_OFFSET_FACTOR).float_value).to_equal(-1.5)
expect(ctx.get_parameter(WEBGL_POLYGON_OFFSET_UNITS).float_value).to_equal(4.0)
expect(ctx.get_parameter(WEBGL_SAMPLE_COVERAGE).bool_value).to_equal(true)
expect(ctx.get_parameter(WEBGL_SAMPLE_COVERAGE_VALUE).float_value).to_equal(1.0)
expect(ctx.get_parameter(WEBGL_SAMPLE_COVERAGE_INVERT).bool_value).to_equal(true)
expect(ctx.get_parameter(WEBGL_BLEND_COLOR).float_values[2]).to_equal(0.3)
expect(ctx.blend_func(WEBGL_CONSTANT_COLOR, WEBGL_ONE_MINUS_SRC_ALPHA)).to_equal(true)
expect(ctx.get_parameter(WEBGL_BLEND_SRC_RGB).int_value).to_equal(WEBGL_CONSTANT_COLOR)
expect(ctx.get_parameter(WEBGL_BLEND_DST_RGB).int_value).to_equal(WEBGL_ONE_MINUS_SRC_ALPHA)
expect(ctx.get_parameter(999).int_value).to_equal(0)
expect(ctx.get_error()).to_equal(WEBGL_INVALID_ENUM)
```

</details>

#### reports deterministic implementation limits and bit depths

1. var ctx = webgl create context
   - Expected: ctx.get_parameter(WEBGL_VENDOR).text_value equals `Simple Browser`
   - Expected: ctx.get_parameter(WEBGL_RENDERER).text_value equals `Simple Browser WebGL`
   - Expected: ctx.get_parameter(WEBGL_VERSION).text_value equals `WebGL 1.0 Simple Browser`
   - Expected: ctx.get_parameter(WEBGL_SHADING_LANGUAGE_VERSION).text_value equals `WebGL GLSL ES 1.00 Simple Browser`
   - Expected: ctx.get_parameter(WEBGL_MAX_TEXTURE_SIZE).int_value equals `4096`
   - Expected: ctx.get_parameter(WEBGL_MAX_CUBE_MAP_TEXTURE_SIZE).int_value equals `4096`
   - Expected: ctx.get_parameter(WEBGL_MAX_RENDERBUFFER_SIZE).int_value equals `4096`
   - Expected: ctx.get_parameter(WEBGL_MAX_VIEWPORT_DIMS).int_values[0] equals `4096`
   - Expected: ctx.get_parameter(WEBGL_MAX_VIEWPORT_DIMS).int_values[1] equals `4096`
   - Expected: ctx.get_parameter(WEBGL_MAX_TEXTURE_IMAGE_UNITS).int_value equals `8`
   - Expected: ctx.get_parameter(WEBGL_MAX_VERTEX_TEXTURE_IMAGE_UNITS).int_value equals `8`
   - Expected: ctx.get_parameter(WEBGL_MAX_VERTEX_UNIFORM_VECTORS).int_value equals `128`
   - Expected: ctx.get_parameter(WEBGL_MAX_FRAGMENT_UNIFORM_VECTORS).int_value equals `64`
   - Expected: ctx.get_parameter(WEBGL_MAX_VARYING_VECTORS).int_value equals `8`
   - Expected: ctx.get_parameter(WEBGL_NUM_COMPRESSED_TEXTURE_FORMATS).int_value equals `0`
   - Expected: ctx.get_parameter(WEBGL_COMPRESSED_TEXTURE_FORMATS).int_values.len() equals `0`
   - Expected: ctx.get_parameter(WEBGL_SUBPIXEL_BITS).int_value equals `4`
   - Expected: ctx.get_parameter(WEBGL_RED_BITS).int_value equals `8`
   - Expected: ctx.get_parameter(WEBGL_GREEN_BITS).int_value equals `8`
   - Expected: ctx.get_parameter(WEBGL_BLUE_BITS).int_value equals `8`
   - Expected: ctx.get_parameter(WEBGL_ALPHA_BITS).int_value equals `8`
   - Expected: ctx.get_parameter(WEBGL_DEPTH_BITS).int_value equals `24`
   - Expected: ctx.get_parameter(WEBGL_STENCIL_BITS).int_value equals `8`
   - Expected: ctx2.get_parameter(WEBGL_VERSION).text_value equals `WebGL 2.0 Simple Browser`
   - Expected: ctx2.get_parameter(WEBGL_SHADING_LANGUAGE_VERSION).text_value equals `WebGL GLSL ES 3.00 Simple Browser`
   - Expected: ctx.get_error() equals `WEBGL_NO_ERROR`


<details>
<summary>Executable SSpec</summary>

Runnable source: 28 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ctx = webgl_create_context(1, 320, 240)
expect(ctx.get_parameter(WEBGL_VENDOR).text_value).to_equal("Simple Browser")
expect(ctx.get_parameter(WEBGL_RENDERER).text_value).to_equal("Simple Browser WebGL")
expect(ctx.get_parameter(WEBGL_VERSION).text_value).to_equal("WebGL 1.0 Simple Browser")
expect(ctx.get_parameter(WEBGL_SHADING_LANGUAGE_VERSION).text_value).to_equal("WebGL GLSL ES 1.00 Simple Browser")
expect(ctx.get_parameter(WEBGL_MAX_TEXTURE_SIZE).int_value).to_equal(4096)
expect(ctx.get_parameter(WEBGL_MAX_CUBE_MAP_TEXTURE_SIZE).int_value).to_equal(4096)
expect(ctx.get_parameter(WEBGL_MAX_RENDERBUFFER_SIZE).int_value).to_equal(4096)
expect(ctx.get_parameter(WEBGL_MAX_VIEWPORT_DIMS).int_values[0]).to_equal(4096)
expect(ctx.get_parameter(WEBGL_MAX_VIEWPORT_DIMS).int_values[1]).to_equal(4096)
expect(ctx.get_parameter(WEBGL_MAX_TEXTURE_IMAGE_UNITS).int_value).to_equal(8)
expect(ctx.get_parameter(WEBGL_MAX_VERTEX_TEXTURE_IMAGE_UNITS).int_value).to_equal(8)
expect(ctx.get_parameter(WEBGL_MAX_VERTEX_UNIFORM_VECTORS).int_value).to_equal(128)
expect(ctx.get_parameter(WEBGL_MAX_FRAGMENT_UNIFORM_VECTORS).int_value).to_equal(64)
expect(ctx.get_parameter(WEBGL_MAX_VARYING_VECTORS).int_value).to_equal(8)
expect(ctx.get_parameter(WEBGL_NUM_COMPRESSED_TEXTURE_FORMATS).int_value).to_equal(0)
expect(ctx.get_parameter(WEBGL_COMPRESSED_TEXTURE_FORMATS).int_values.len()).to_equal(0)
expect(ctx.get_parameter(WEBGL_SUBPIXEL_BITS).int_value).to_equal(4)
expect(ctx.get_parameter(WEBGL_RED_BITS).int_value).to_equal(8)
expect(ctx.get_parameter(WEBGL_GREEN_BITS).int_value).to_equal(8)
expect(ctx.get_parameter(WEBGL_BLUE_BITS).int_value).to_equal(8)
expect(ctx.get_parameter(WEBGL_ALPHA_BITS).int_value).to_equal(8)
expect(ctx.get_parameter(WEBGL_DEPTH_BITS).int_value).to_equal(24)
expect(ctx.get_parameter(WEBGL_STENCIL_BITS).int_value).to_equal(8)
val ctx2 = webgl_create_context(2, 320, 240)
expect(ctx2.get_parameter(WEBGL_VERSION).text_value).to_equal("WebGL 2.0 Simple Browser")
expect(ctx2.get_parameter(WEBGL_SHADING_LANGUAGE_VERSION).text_value).to_equal("WebGL GLSL ES 3.00 Simple Browser")
expect(ctx.get_error()).to_equal(WEBGL_NO_ERROR)
```

</details>

#### tracks color depth and stencil write masks

1. var ctx = webgl create context
   - Expected: ctx.color_mask_red is true
   - Expected: ctx.color_mask_green is true
   - Expected: ctx.color_mask_blue is true
   - Expected: ctx.color_mask_alpha is true
   - Expected: ctx.depth_mask_enabled is true
   - Expected: ctx.stencil_write_mask_value equals `-1`
   - Expected: ctx.stencil_back_write_mask_value equals `-1`
   - Expected: ctx.color_mask(true, false, true, false) is true
   - Expected: ctx.depth_mask(false) is true
   - Expected: ctx.stencil_mask(15) is true
   - Expected: ctx.color_mask_green is false
   - Expected: ctx.color_mask_alpha is false
   - Expected: ctx.depth_mask_enabled is false
   - Expected: ctx.stencil_write_mask_value equals `15`
   - Expected: ctx.stencil_back_write_mask_value equals `15`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ctx = webgl_create_context(1, 320, 240)
expect(ctx.color_mask_red).to_equal(true)
expect(ctx.color_mask_green).to_equal(true)
expect(ctx.color_mask_blue).to_equal(true)
expect(ctx.color_mask_alpha).to_equal(true)
expect(ctx.depth_mask_enabled).to_equal(true)
expect(ctx.stencil_write_mask_value).to_equal(-1)
expect(ctx.stencil_back_write_mask_value).to_equal(-1)
expect(ctx.color_mask(true, false, true, false)).to_equal(true)
expect(ctx.depth_mask(false)).to_equal(true)
expect(ctx.stencil_mask(15)).to_equal(true)
expect(ctx.color_mask_green).to_equal(false)
expect(ctx.color_mask_alpha).to_equal(false)
expect(ctx.depth_mask_enabled).to_equal(false)
expect(ctx.stencil_write_mask_value).to_equal(15)
expect(ctx.stencil_back_write_mask_value).to_equal(15)
```

</details>

#### tracks separate front and back stencil write masks

1. var ctx = webgl create context
   - Expected: ctx.stencil_mask_separate(WEBGL_FRONT, 3) is true
   - Expected: ctx.stencil_write_mask_value equals `3`
   - Expected: ctx.stencil_back_write_mask_value equals `-1`
   - Expected: ctx.stencil_mask_separate(WEBGL_BACK, 12) is true
   - Expected: ctx.stencil_write_mask_value equals `3`
   - Expected: ctx.stencil_back_write_mask_value equals `12`
   - Expected: ctx.stencil_mask_separate(WEBGL_FRONT_AND_BACK, 7) is true
   - Expected: ctx.stencil_write_mask_value equals `7`
   - Expected: ctx.stencil_back_write_mask_value equals `7`
   - Expected: ctx.stencil_mask_separate(999, 1) is false
   - Expected: ctx.get_error() equals `WEBGL_INVALID_ENUM`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ctx = webgl_create_context(1, 320, 240)
expect(ctx.stencil_mask_separate(WEBGL_FRONT, 3)).to_equal(true)
expect(ctx.stencil_write_mask_value).to_equal(3)
expect(ctx.stencil_back_write_mask_value).to_equal(-1)
expect(ctx.stencil_mask_separate(WEBGL_BACK, 12)).to_equal(true)
expect(ctx.stencil_write_mask_value).to_equal(3)
expect(ctx.stencil_back_write_mask_value).to_equal(12)
expect(ctx.stencil_mask_separate(WEBGL_FRONT_AND_BACK, 7)).to_equal(true)
expect(ctx.stencil_write_mask_value).to_equal(7)
expect(ctx.stencil_back_write_mask_value).to_equal(7)
expect(ctx.stencil_mask_separate(999, 1)).to_equal(false)
expect(ctx.get_error()).to_equal(WEBGL_INVALID_ENUM)
```

</details>

#### reports write masks through get parameter

1. var ctx = webgl create context
   - Expected: ctx.color_mask(false, true, false, true) is true
   - Expected: ctx.depth_mask(false) is true
   - Expected: ctx.stencil_mask(255) is true
   - Expected: ctx.stencil_mask_separate(WEBGL_BACK, 127) is true
   - Expected: ctx.get_parameter(WEBGL_COLOR_WRITEMASK).bool_values[0] is false
   - Expected: ctx.get_parameter(WEBGL_COLOR_WRITEMASK).bool_values[1] is true
   - Expected: ctx.get_parameter(WEBGL_COLOR_WRITEMASK).bool_values[2] is false
   - Expected: ctx.get_parameter(WEBGL_COLOR_WRITEMASK).bool_values[3] is true
   - Expected: ctx.get_parameter(WEBGL_DEPTH_WRITEMASK).bool_value is false
   - Expected: ctx.get_parameter(WEBGL_STENCIL_WRITEMASK).int_value equals `255`
   - Expected: ctx.get_parameter(WEBGL_STENCIL_BACK_WRITEMASK).int_value equals `127`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ctx = webgl_create_context(1, 320, 240)
expect(ctx.color_mask(false, true, false, true)).to_equal(true)
expect(ctx.depth_mask(false)).to_equal(true)
expect(ctx.stencil_mask(255)).to_equal(true)
expect(ctx.stencil_mask_separate(WEBGL_BACK, 127)).to_equal(true)
expect(ctx.get_parameter(WEBGL_COLOR_WRITEMASK).bool_values[0]).to_equal(false)
expect(ctx.get_parameter(WEBGL_COLOR_WRITEMASK).bool_values[1]).to_equal(true)
expect(ctx.get_parameter(WEBGL_COLOR_WRITEMASK).bool_values[2]).to_equal(false)
expect(ctx.get_parameter(WEBGL_COLOR_WRITEMASK).bool_values[3]).to_equal(true)
expect(ctx.get_parameter(WEBGL_DEPTH_WRITEMASK).bool_value).to_equal(false)
expect(ctx.get_parameter(WEBGL_STENCIL_WRITEMASK).int_value).to_equal(255)
expect(ctx.get_parameter(WEBGL_STENCIL_BACK_WRITEMASK).int_value).to_equal(127)
```

</details>

#### supports minimum blend equation mode

1. var ctx = webgl create context
   - Expected: ctx.blend_equation(WEBGL_MIN) is true
   - Expected: ctx.blend_equation_rgb equals `WEBGL_MIN`
   - Expected: ctx.blend_equation_alpha equals `WEBGL_MIN`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ctx = webgl_create_context(1, 320, 240)
expect(ctx.blend_equation(WEBGL_MIN)).to_equal(true)
expect(ctx.blend_equation_rgb).to_equal(WEBGL_MIN)
expect(ctx.blend_equation_alpha).to_equal(WEBGL_MIN)
```

</details>

#### tracks separate blend factors for rgb and alpha

1. var ctx = webgl create context
   - Expected: ctx.get_parameter(WEBGL_BLEND_SRC_ALPHA).int_value equals `WEBGL_ONE`
   - Expected: ctx.get_parameter(WEBGL_BLEND_DST_ALPHA).int_value equals `WEBGL_ZERO`
   - Expected: ctx.blend_func_separate(WEBGL_SRC_ALPHA, WEBGL_ONE_MINUS_SRC_ALPHA, WEBGL_ONE, WEBGL_ZERO) is true
   - Expected: ctx.blend_src_factor equals `WEBGL_SRC_ALPHA`
   - Expected: ctx.blend_dst_factor equals `WEBGL_ONE_MINUS_SRC_ALPHA`
   - Expected: ctx.blend_src_alpha_factor equals `WEBGL_ONE`
   - Expected: ctx.blend_dst_alpha_factor equals `WEBGL_ZERO`
   - Expected: ctx.get_parameter(WEBGL_BLEND_SRC_RGB).int_value equals `WEBGL_SRC_ALPHA`
   - Expected: ctx.get_parameter(WEBGL_BLEND_DST_RGB).int_value equals `WEBGL_ONE_MINUS_SRC_ALPHA`
   - Expected: ctx.get_parameter(WEBGL_BLEND_SRC_ALPHA).int_value equals `WEBGL_ONE`
   - Expected: ctx.get_parameter(WEBGL_BLEND_DST_ALPHA).int_value equals `WEBGL_ZERO`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ctx = webgl_create_context(1, 320, 240)
expect(ctx.get_parameter(WEBGL_BLEND_SRC_ALPHA).int_value).to_equal(WEBGL_ONE)
expect(ctx.get_parameter(WEBGL_BLEND_DST_ALPHA).int_value).to_equal(WEBGL_ZERO)
expect(ctx.blend_func_separate(WEBGL_SRC_ALPHA, WEBGL_ONE_MINUS_SRC_ALPHA, WEBGL_ONE, WEBGL_ZERO)).to_equal(true)
expect(ctx.blend_src_factor).to_equal(WEBGL_SRC_ALPHA)
expect(ctx.blend_dst_factor).to_equal(WEBGL_ONE_MINUS_SRC_ALPHA)
expect(ctx.blend_src_alpha_factor).to_equal(WEBGL_ONE)
expect(ctx.blend_dst_alpha_factor).to_equal(WEBGL_ZERO)
expect(ctx.get_parameter(WEBGL_BLEND_SRC_RGB).int_value).to_equal(WEBGL_SRC_ALPHA)
expect(ctx.get_parameter(WEBGL_BLEND_DST_RGB).int_value).to_equal(WEBGL_ONE_MINUS_SRC_ALPHA)
expect(ctx.get_parameter(WEBGL_BLEND_SRC_ALPHA).int_value).to_equal(WEBGL_ONE)
expect(ctx.get_parameter(WEBGL_BLEND_DST_ALPHA).int_value).to_equal(WEBGL_ZERO)
```

</details>

#### rejects mixed constant color and alpha blend factors without mutating state

1. var ctx = webgl create context
   - Expected: ctx.blend_func(WEBGL_SRC_ALPHA, WEBGL_ONE_MINUS_SRC_ALPHA) is true
   - Expected: ctx.blend_func(WEBGL_CONSTANT_COLOR, WEBGL_ONE_MINUS_CONSTANT_ALPHA) is false
   - Expected: ctx.get_error() equals `WEBGL_INVALID_OPERATION`
   - Expected: ctx.get_parameter(WEBGL_BLEND_SRC_RGB).int_value equals `WEBGL_SRC_ALPHA`
   - Expected: ctx.get_parameter(WEBGL_BLEND_DST_RGB).int_value equals `WEBGL_ONE_MINUS_SRC_ALPHA`
   - Expected: ctx.blend_func_separate(WEBGL_ONE, WEBGL_ONE_MINUS_CONSTANT_COLOR, WEBGL_CONSTANT_ALPHA, WEBGL_ZERO) is false
   - Expected: ctx.get_error() equals `WEBGL_INVALID_OPERATION`
   - Expected: ctx.get_parameter(WEBGL_BLEND_SRC_RGB).int_value equals `WEBGL_SRC_ALPHA`
   - Expected: ctx.get_parameter(WEBGL_BLEND_DST_RGB).int_value equals `WEBGL_ONE_MINUS_SRC_ALPHA`
   - Expected: ctx.get_parameter(WEBGL_BLEND_SRC_ALPHA).int_value equals `WEBGL_SRC_ALPHA`
   - Expected: ctx.get_parameter(WEBGL_BLEND_DST_ALPHA).int_value equals `WEBGL_ONE_MINUS_SRC_ALPHA`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ctx = webgl_create_context(1, 320, 240)
expect(ctx.blend_func(WEBGL_SRC_ALPHA, WEBGL_ONE_MINUS_SRC_ALPHA)).to_equal(true)
expect(ctx.blend_func(WEBGL_CONSTANT_COLOR, WEBGL_ONE_MINUS_CONSTANT_ALPHA)).to_equal(false)
expect(ctx.get_error()).to_equal(WEBGL_INVALID_OPERATION)
expect(ctx.get_parameter(WEBGL_BLEND_SRC_RGB).int_value).to_equal(WEBGL_SRC_ALPHA)
expect(ctx.get_parameter(WEBGL_BLEND_DST_RGB).int_value).to_equal(WEBGL_ONE_MINUS_SRC_ALPHA)
expect(ctx.blend_func_separate(WEBGL_ONE, WEBGL_ONE_MINUS_CONSTANT_COLOR, WEBGL_CONSTANT_ALPHA, WEBGL_ZERO)).to_equal(false)
expect(ctx.get_error()).to_equal(WEBGL_INVALID_OPERATION)
expect(ctx.get_parameter(WEBGL_BLEND_SRC_RGB).int_value).to_equal(WEBGL_SRC_ALPHA)
expect(ctx.get_parameter(WEBGL_BLEND_DST_RGB).int_value).to_equal(WEBGL_ONE_MINUS_SRC_ALPHA)
expect(ctx.get_parameter(WEBGL_BLEND_SRC_ALPHA).int_value).to_equal(WEBGL_SRC_ALPHA)
expect(ctx.get_parameter(WEBGL_BLEND_DST_ALPHA).int_value).to_equal(WEBGL_ONE_MINUS_SRC_ALPHA)
```

</details>

### textures

#### binds texture 2d and records rgba uploads

1. var ctx = webgl create context
   - Expected: ctx.bind_texture(WEBGL_TEXTURE_2D, texture.id) is true
   - Expected: ctx.tex_image_2d(WEBGL_TEXTURE_2D, 0, WEBGL_RGBA, 1, 2, 0, WEBGL_RGBA, WEBGL_UNSIGNED_BYTE, pixels) is true
   - Expected: ctx.bound_texture_2d equals `texture.id`
   - Expected: ctx.textures[0].target equals `WEBGL_TEXTURE_2D`
   - Expected: ctx.textures[0].width equals `1`
   - Expected: ctx.textures[0].height equals `2`
   - Expected: ctx.textures[0].initialized is true
   - Expected: ctx.textures[0].pixels.len() equals `8`
   - Expected: ctx.textures[0].pixels[6] equals `7`
   - Expected: ctx.render_commands[0].kind equals `WEBGL_RENDER_COMMAND_BIND_TEXTURE`
   - Expected: ctx.render_commands[0].texture_id equals `texture.id`
   - Expected: ctx.render_commands[1].kind equals `WEBGL_RENDER_COMMAND_TEX_IMAGE_2D`
   - Expected: ctx.render_commands[1].target equals `WEBGL_TEXTURE_2D`
   - Expected: ctx.render_commands[1].mode equals `0`
   - Expected: ctx.render_commands[1].mask equals `WEBGL_RGBA`
   - Expected: ctx.render_commands[1].width equals `1`
   - Expected: ctx.render_commands[1].height equals `2`
   - Expected: ctx.render_commands[1].element_type equals `WEBGL_RGBA`
   - Expected: ctx.render_commands[1].offset equals `WEBGL_UNSIGNED_BYTE`


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ctx = webgl_create_context(1, 320, 240)
val texture = ctx.create_texture()
expect(ctx.bind_texture(WEBGL_TEXTURE_2D, texture.id)).to_equal(true)
val pixels: [u8] = [1, 2, 3, 4, 5, 6, 7, 8]
expect(ctx.tex_image_2d(WEBGL_TEXTURE_2D, 0, WEBGL_RGBA, 1, 2, 0, WEBGL_RGBA, WEBGL_UNSIGNED_BYTE, pixels)).to_equal(true)
expect(ctx.bound_texture_2d).to_equal(texture.id)
expect(ctx.textures[0].target).to_equal(WEBGL_TEXTURE_2D)
expect(ctx.textures[0].width).to_equal(1)
expect(ctx.textures[0].height).to_equal(2)
expect(ctx.textures[0].initialized).to_equal(true)
expect(ctx.textures[0].pixels.len()).to_equal(8)
expect(ctx.textures[0].pixels[6]).to_equal(7)
expect(ctx.render_commands[0].kind).to_equal(WEBGL_RENDER_COMMAND_BIND_TEXTURE)
expect(ctx.render_commands[0].texture_id).to_equal(texture.id)
expect(ctx.render_commands[1].kind).to_equal(WEBGL_RENDER_COMMAND_TEX_IMAGE_2D)
expect(ctx.render_commands[1].target).to_equal(WEBGL_TEXTURE_2D)
expect(ctx.render_commands[1].mode).to_equal(0)
expect(ctx.render_commands[1].mask).to_equal(WEBGL_RGBA)
expect(ctx.render_commands[1].width).to_equal(1)
expect(ctx.render_commands[1].height).to_equal(2)
expect(ctx.render_commands[1].element_type).to_equal(WEBGL_RGBA)
expect(ctx.render_commands[1].offset).to_equal(WEBGL_UNSIGNED_BYTE)
```

</details>

#### allocates zero-filled texture storage when upload data is empty

1. var ctx = webgl create context
2. ctx bind texture
   - Expected: ctx.tex_image_2d(WEBGL_TEXTURE_2D, 0, WEBGL_RGBA, 2, 1, 0, WEBGL_RGBA, WEBGL_UNSIGNED_BYTE, []) is true
   - Expected: ctx.textures[0].pixels.len() equals `8`
   - Expected: ctx.textures[0].pixels[7] equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ctx = webgl_create_context(1, 320, 240)
val texture = ctx.create_texture()
ctx.bind_texture(WEBGL_TEXTURE_2D, texture.id)
expect(ctx.tex_image_2d(WEBGL_TEXTURE_2D, 0, WEBGL_RGBA, 2, 1, 0, WEBGL_RGBA, WEBGL_UNSIGNED_BYTE, [])).to_equal(true)
expect(ctx.textures[0].pixels.len()).to_equal(8)
expect(ctx.textures[0].pixels[7]).to_equal(0)
```

</details>

#### honors unpack alignment for rgb upload byte counts

1. var ctx = webgl create context
2. ctx bind texture
   - Expected: ctx.tex_image_2d(WEBGL_TEXTURE_2D, 0, WEBGL_RGB, 1, 2, 0, WEBGL_RGB, WEBGL_UNSIGNED_BYTE, padded) is true
   - Expected: ctx.textures[0].pixels.len() equals `8`
   - Expected: ctx.pixel_store_i(WEBGL_UNPACK_ALIGNMENT, 1) is true
   - Expected: ctx.tex_image_2d(WEBGL_TEXTURE_2D, 0, WEBGL_RGB, 1, 2, 0, WEBGL_RGB, WEBGL_UNSIGNED_BYTE, tight) is true
   - Expected: ctx.textures[0].pixels.len() equals `6`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ctx = webgl_create_context(1, 320, 240)
val texture = ctx.create_texture()
ctx.bind_texture(WEBGL_TEXTURE_2D, texture.id)
val padded: [u8] = [1, 2, 3, 0, 4, 5, 6, 0]
expect(ctx.tex_image_2d(WEBGL_TEXTURE_2D, 0, WEBGL_RGB, 1, 2, 0, WEBGL_RGB, WEBGL_UNSIGNED_BYTE, padded)).to_equal(true)
expect(ctx.textures[0].pixels.len()).to_equal(8)
expect(ctx.pixel_store_i(WEBGL_UNPACK_ALIGNMENT, 1)).to_equal(true)
val tight: [u8] = [7, 8, 9, 10, 11, 12]
expect(ctx.tex_image_2d(WEBGL_TEXTURE_2D, 0, WEBGL_RGB, 1, 2, 0, WEBGL_RGB, WEBGL_UNSIGNED_BYTE, tight)).to_equal(true)
expect(ctx.textures[0].pixels.len()).to_equal(6)
```

</details>

#### updates initialized texture regions with sub image data

1. var ctx = webgl create context
2. ctx bind texture
3. ctx tex image 2d
   - Expected: ctx.tex_sub_image_2d(WEBGL_TEXTURE_2D, 0, 1, 0, 1, 1, WEBGL_RGBA, WEBGL_UNSIGNED_BYTE, sub) is true
   - Expected: ctx.textures[0].pixels[0] equals `0`
   - Expected: ctx.textures[0].pixels[4] equals `9`
   - Expected: ctx.textures[0].pixels[7] equals `6`
   - Expected: ctx.render_commands[2].kind equals `WEBGL_RENDER_COMMAND_TEX_SUB_IMAGE_2D`
   - Expected: ctx.render_commands[2].x equals `1`
   - Expected: ctx.render_commands[2].y equals `0`
   - Expected: ctx.render_commands[2].width equals `1`
   - Expected: ctx.render_commands[2].height equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ctx = webgl_create_context(1, 320, 240)
val texture = ctx.create_texture()
ctx.bind_texture(WEBGL_TEXTURE_2D, texture.id)
ctx.tex_image_2d(WEBGL_TEXTURE_2D, 0, WEBGL_RGBA, 2, 1, 0, WEBGL_RGBA, WEBGL_UNSIGNED_BYTE, [])
val sub: [u8] = [9, 8, 7, 6]
expect(ctx.tex_sub_image_2d(WEBGL_TEXTURE_2D, 0, 1, 0, 1, 1, WEBGL_RGBA, WEBGL_UNSIGNED_BYTE, sub)).to_equal(true)
expect(ctx.textures[0].pixels[0]).to_equal(0)
expect(ctx.textures[0].pixels[4]).to_equal(9)
expect(ctx.textures[0].pixels[7]).to_equal(6)
expect(ctx.render_commands[2].kind).to_equal(WEBGL_RENDER_COMMAND_TEX_SUB_IMAGE_2D)
expect(ctx.render_commands[2].x).to_equal(1)
expect(ctx.render_commands[2].y).to_equal(0)
expect(ctx.render_commands[2].width).to_equal(1)
expect(ctx.render_commands[2].height).to_equal(1)
```

</details>

#### validates texture upload errors without mutating existing storage

1. var ctx = webgl create context
   - Expected: ctx.tex_image_2d(WEBGL_TEXTURE_2D, 0, WEBGL_RGBA, 1, 1, 0, WEBGL_RGBA, WEBGL_UNSIGNED_BYTE, []) is false
   - Expected: ctx.get_error() equals `WEBGL_INVALID_OPERATION`
   - Expected: ctx.bind_texture(999, texture.id) is false
   - Expected: ctx.get_error() equals `WEBGL_INVALID_ENUM`
   - Expected: ctx.bind_texture(WEBGL_TEXTURE_2D, 99) is false
   - Expected: ctx.get_error() equals `WEBGL_INVALID_VALUE`
   - Expected: ctx.bind_texture(WEBGL_TEXTURE_2D, texture.id) is true
   - Expected: ctx.tex_image_2d(WEBGL_TEXTURE_2D, 1, WEBGL_RGBA, 1, 1, 0, WEBGL_RGBA, WEBGL_UNSIGNED_BYTE, []) is false
   - Expected: ctx.get_error() equals `WEBGL_INVALID_VALUE`
   - Expected: ctx.tex_image_2d(WEBGL_TEXTURE_2D, 0, WEBGL_RGBA, 1, 1, 0, WEBGL_RGBA, WEBGL_UNSIGNED_BYTE, short_pixels) is false
   - Expected: ctx.get_error() equals `WEBGL_INVALID_OPERATION`
   - Expected: ctx.textures[0].initialized is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ctx = webgl_create_context(1, 320, 240)
val texture = ctx.create_texture()
expect(ctx.tex_image_2d(WEBGL_TEXTURE_2D, 0, WEBGL_RGBA, 1, 1, 0, WEBGL_RGBA, WEBGL_UNSIGNED_BYTE, [])).to_equal(false)
expect(ctx.get_error()).to_equal(WEBGL_INVALID_OPERATION)
expect(ctx.bind_texture(999, texture.id)).to_equal(false)
expect(ctx.get_error()).to_equal(WEBGL_INVALID_ENUM)
expect(ctx.bind_texture(WEBGL_TEXTURE_2D, 99)).to_equal(false)
expect(ctx.get_error()).to_equal(WEBGL_INVALID_VALUE)
expect(ctx.bind_texture(WEBGL_TEXTURE_2D, texture.id)).to_equal(true)
expect(ctx.tex_image_2d(WEBGL_TEXTURE_2D, 1, WEBGL_RGBA, 1, 1, 0, WEBGL_RGBA, WEBGL_UNSIGNED_BYTE, [])).to_equal(false)
expect(ctx.get_error()).to_equal(WEBGL_INVALID_VALUE)
val short_pixels: [u8] = [1, 2, 3]
expect(ctx.tex_image_2d(WEBGL_TEXTURE_2D, 0, WEBGL_RGBA, 1, 1, 0, WEBGL_RGBA, WEBGL_UNSIGNED_BYTE, short_pixels)).to_equal(false)
expect(ctx.get_error()).to_equal(WEBGL_INVALID_OPERATION)
expect(ctx.textures[0].initialized).to_equal(false)
```

</details>

#### rejects oversized texture upload byte counts before allocation

1. var ctx = webgl create context
   - Expected: ctx.bind_texture(WEBGL_TEXTURE_2D, texture.id) is true
   - Expected: ctx.tex_image_2d(WEBGL_TEXTURE_2D, 0, WEBGL_RGBA, 600000000, 2, 0, WEBGL_RGBA, WEBGL_UNSIGNED_BYTE, []) is false
   - Expected: ctx.get_error() equals `WEBGL_INVALID_VALUE`
   - Expected: ctx.textures[0].initialized is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ctx = webgl_create_context(1, 320, 240)
val texture = ctx.create_texture()
expect(ctx.bind_texture(WEBGL_TEXTURE_2D, texture.id)).to_equal(true)
expect(ctx.tex_image_2d(WEBGL_TEXTURE_2D, 0, WEBGL_RGBA, 600000000, 2, 0, WEBGL_RGBA, WEBGL_UNSIGNED_BYTE, [])).to_equal(false)
expect(ctx.get_error()).to_equal(WEBGL_INVALID_VALUE)
expect(ctx.textures[0].initialized).to_equal(false)
```

</details>

#### reports overflowing texture byte calculations

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(webgl_required_texture_bytes_safe(600000000, 2, 4, 4)).to_equal(-1)
expect(webgl_required_texture_bytes_safe(1, 2, 3, 4)).to_equal(8)
```

</details>

#### tracks pixel store boolean flags and rejects bad alignment

1. var ctx = webgl create context
   - Expected: ctx.get_parameter(WEBGL_PACK_ALIGNMENT).int_value equals `4`
   - Expected: ctx.get_parameter(WEBGL_UNPACK_ALIGNMENT).int_value equals `4`
   - Expected: ctx.pixel_store_i(WEBGL_PACK_ALIGNMENT, 1) is true
   - Expected: ctx.pack_alignment equals `1`
   - Expected: ctx.get_parameter(WEBGL_PACK_ALIGNMENT).int_value equals `1`
   - Expected: ctx.pixel_store_i(WEBGL_UNPACK_FLIP_Y_WEBGL, 1) is true
   - Expected: ctx.unpack_flip_y is true
   - Expected: ctx.pixel_store_i(WEBGL_UNPACK_PREMULTIPLY_ALPHA_WEBGL, 0) is true
   - Expected: ctx.unpack_premultiply_alpha is false
   - Expected: ctx.pixel_store_i(WEBGL_UNPACK_ALIGNMENT, 8) is true
   - Expected: ctx.get_parameter(WEBGL_UNPACK_ALIGNMENT).int_value equals `8`
   - Expected: ctx.render_commands[0].kind equals `WEBGL_RENDER_COMMAND_PIXEL_STORE`
   - Expected: ctx.render_commands[0].target equals `WEBGL_PACK_ALIGNMENT`
   - Expected: ctx.render_commands[0].mask equals `1`
   - Expected: ctx.render_commands[1].target equals `WEBGL_UNPACK_FLIP_Y_WEBGL`
   - Expected: ctx.render_commands[1].mask equals `1`
   - Expected: ctx.render_commands[2].target equals `WEBGL_UNPACK_PREMULTIPLY_ALPHA_WEBGL`
   - Expected: ctx.render_commands[2].mask equals `0`
   - Expected: ctx.render_commands[3].target equals `WEBGL_UNPACK_ALIGNMENT`
   - Expected: ctx.render_commands[3].mask equals `8`
   - Expected: ctx.pixel_store_i(WEBGL_PACK_ALIGNMENT, 3) is false
   - Expected: ctx.get_error() equals `WEBGL_INVALID_VALUE`
   - Expected: ctx.pixel_store_i(WEBGL_UNPACK_ALIGNMENT, 3) is false
   - Expected: ctx.get_error() equals `WEBGL_INVALID_VALUE`


<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ctx = webgl_create_context(1, 320, 240)
expect(ctx.get_parameter(WEBGL_PACK_ALIGNMENT).int_value).to_equal(4)
expect(ctx.get_parameter(WEBGL_UNPACK_ALIGNMENT).int_value).to_equal(4)
expect(ctx.pixel_store_i(WEBGL_PACK_ALIGNMENT, 1)).to_equal(true)
expect(ctx.pack_alignment).to_equal(1)
expect(ctx.get_parameter(WEBGL_PACK_ALIGNMENT).int_value).to_equal(1)
expect(ctx.pixel_store_i(WEBGL_UNPACK_FLIP_Y_WEBGL, 1)).to_equal(true)
expect(ctx.unpack_flip_y).to_equal(true)
expect(ctx.pixel_store_i(WEBGL_UNPACK_PREMULTIPLY_ALPHA_WEBGL, 0)).to_equal(true)
expect(ctx.unpack_premultiply_alpha).to_equal(false)
expect(ctx.pixel_store_i(WEBGL_UNPACK_ALIGNMENT, 8)).to_equal(true)
expect(ctx.get_parameter(WEBGL_UNPACK_ALIGNMENT).int_value).to_equal(8)
expect(ctx.render_commands[0].kind).to_equal(WEBGL_RENDER_COMMAND_PIXEL_STORE)
expect(ctx.render_commands[0].target).to_equal(WEBGL_PACK_ALIGNMENT)
expect(ctx.render_commands[0].mask).to_equal(1)
expect(ctx.render_commands[1].target).to_equal(WEBGL_UNPACK_FLIP_Y_WEBGL)
expect(ctx.render_commands[1].mask).to_equal(1)
expect(ctx.render_commands[2].target).to_equal(WEBGL_UNPACK_PREMULTIPLY_ALPHA_WEBGL)
expect(ctx.render_commands[2].mask).to_equal(0)
expect(ctx.render_commands[3].target).to_equal(WEBGL_UNPACK_ALIGNMENT)
expect(ctx.render_commands[3].mask).to_equal(8)
expect(ctx.pixel_store_i(WEBGL_PACK_ALIGNMENT, 3)).to_equal(false)
expect(ctx.get_error()).to_equal(WEBGL_INVALID_VALUE)
expect(ctx.pixel_store_i(WEBGL_UNPACK_ALIGNMENT, 3)).to_equal(false)
expect(ctx.get_error()).to_equal(WEBGL_INVALID_VALUE)
```

</details>

#### returns deterministic pixel readback bytes

1. var ctx = webgl create context
   - Expected: ctx.pixel_store_i(WEBGL_PACK_ALIGNMENT, 4) is true
   - Expected: rgba.len() equals `8`
   - Expected: rgba[7] equals `0`
   - Expected: ctx.render_commands[1].kind equals `WEBGL_RENDER_COMMAND_READ_PIXELS`
   - Expected: ctx.render_commands[1].x equals `0`
   - Expected: ctx.render_commands[1].width equals `2`
   - Expected: ctx.render_commands[1].height equals `1`
   - Expected: ctx.render_commands[1].target equals `WEBGL_RGBA`
   - Expected: ctx.render_commands[1].element_type equals `WEBGL_UNSIGNED_BYTE`
   - Expected: rgb.len() equals `8`
   - Expected: ctx.render_commands[2].kind equals `WEBGL_RENDER_COMMAND_READ_PIXELS`
   - Expected: ctx.render_commands[2].target equals `WEBGL_RGB`
   - Expected: ctx.pixel_store_i(WEBGL_PACK_ALIGNMENT, 1) is true
   - Expected: ctx.read_pixels(0, 0, 1, 2, WEBGL_RGB, WEBGL_UNSIGNED_BYTE).len() equals `6`
   - Expected: ctx.render_commands[4].kind equals `WEBGL_RENDER_COMMAND_READ_PIXELS`
   - Expected: ctx.get_error() equals `WEBGL_NO_ERROR`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ctx = webgl_create_context(1, 320, 240)
expect(ctx.pixel_store_i(WEBGL_PACK_ALIGNMENT, 4)).to_equal(true)
val rgba = ctx.read_pixels(0, 0, 2, 1, WEBGL_RGBA, WEBGL_UNSIGNED_BYTE)
expect(rgba.len()).to_equal(8)
expect(rgba[7]).to_equal(0)
expect(ctx.render_commands[1].kind).to_equal(WEBGL_RENDER_COMMAND_READ_PIXELS)
expect(ctx.render_commands[1].x).to_equal(0)
expect(ctx.render_commands[1].width).to_equal(2)
expect(ctx.render_commands[1].height).to_equal(1)
expect(ctx.render_commands[1].target).to_equal(WEBGL_RGBA)
expect(ctx.render_commands[1].element_type).to_equal(WEBGL_UNSIGNED_BYTE)
val rgb = ctx.read_pixels(0, 0, 1, 2, WEBGL_RGB, WEBGL_UNSIGNED_BYTE)
expect(rgb.len()).to_equal(8)
expect(ctx.render_commands[2].kind).to_equal(WEBGL_RENDER_COMMAND_READ_PIXELS)
expect(ctx.render_commands[2].target).to_equal(WEBGL_RGB)
expect(ctx.pixel_store_i(WEBGL_PACK_ALIGNMENT, 1)).to_equal(true)
expect(ctx.read_pixels(0, 0, 1, 2, WEBGL_RGB, WEBGL_UNSIGNED_BYTE).len()).to_equal(6)
expect(ctx.render_commands[4].kind).to_equal(WEBGL_RENDER_COMMAND_READ_PIXELS)
expect(ctx.get_error()).to_equal(WEBGL_NO_ERROR)
```

</details>

#### validates pixel readback errors

1. var ctx = webgl create context
   - Expected: ctx.read_pixels(-1, 0, 1, 1, WEBGL_RGBA, WEBGL_UNSIGNED_BYTE).len() equals `0`
   - Expected: ctx.get_error() equals `WEBGL_INVALID_VALUE`
   - Expected: ctx.read_pixels(0, 0, 1, 1, 999, WEBGL_UNSIGNED_BYTE).len() equals `0`
   - Expected: ctx.get_error() equals `WEBGL_INVALID_ENUM`
   - Expected: ctx.bind_framebuffer(WEBGL_FRAMEBUFFER, framebuffer.id) is true
   - Expected: ctx.read_pixels(0, 0, 1, 1, WEBGL_RGBA, WEBGL_UNSIGNED_BYTE).len() equals `0`
   - Expected: ctx.get_error() equals `WEBGL_INVALID_FRAMEBUFFER_OPERATION`
2. ctx lose context
   - Expected: ctx.read_pixels(0, 0, 1, 1, WEBGL_RGBA, WEBGL_UNSIGNED_BYTE).len() equals `0`
   - Expected: ctx.get_error() equals `WEBGL_CONTEXT_LOST_WEBGL`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ctx = webgl_create_context(1, 320, 240)
expect(ctx.read_pixels(-1, 0, 1, 1, WEBGL_RGBA, WEBGL_UNSIGNED_BYTE).len()).to_equal(0)
expect(ctx.get_error()).to_equal(WEBGL_INVALID_VALUE)
expect(ctx.read_pixels(0, 0, 1, 1, 999, WEBGL_UNSIGNED_BYTE).len()).to_equal(0)
expect(ctx.get_error()).to_equal(WEBGL_INVALID_ENUM)
val framebuffer = ctx.create_framebuffer()
expect(ctx.bind_framebuffer(WEBGL_FRAMEBUFFER, framebuffer.id)).to_equal(true)
expect(ctx.read_pixels(0, 0, 1, 1, WEBGL_RGBA, WEBGL_UNSIGNED_BYTE).len()).to_equal(0)
expect(ctx.get_error()).to_equal(WEBGL_INVALID_FRAMEBUFFER_OPERATION)
ctx.lose_context()
expect(ctx.read_pixels(0, 0, 1, 1, WEBGL_RGBA, WEBGL_UNSIGNED_BYTE).len()).to_equal(0)
expect(ctx.get_error()).to_equal(WEBGL_CONTEXT_LOST_WEBGL)
```

</details>

#### tracks texture filtering and wrapping parameters

1. var ctx = webgl create context
   - Expected: texture.min_filter equals `WEBGL_LINEAR_MIPMAP_LINEAR`
   - Expected: texture.mag_filter equals `WEBGL_LINEAR`
   - Expected: texture.wrap_s equals `WEBGL_REPEAT`
   - Expected: ctx.tex_parameter_i(WEBGL_TEXTURE_2D, WEBGL_TEXTURE_MIN_FILTER, WEBGL_NEAREST) is false
   - Expected: ctx.get_error() equals `WEBGL_INVALID_OPERATION`
   - Expected: ctx.bind_texture(WEBGL_TEXTURE_2D, texture.id) is true
   - Expected: ctx.tex_parameter_i(WEBGL_TEXTURE_2D, WEBGL_TEXTURE_MIN_FILTER, WEBGL_NEAREST) is true
   - Expected: ctx.tex_parameter_i(WEBGL_TEXTURE_2D, WEBGL_TEXTURE_MAG_FILTER, WEBGL_LINEAR) is true
   - Expected: ctx.tex_parameter_i(WEBGL_TEXTURE_2D, WEBGL_TEXTURE_WRAP_S, WEBGL_CLAMP_TO_EDGE) is true
   - Expected: ctx.tex_parameter_i(WEBGL_TEXTURE_2D, WEBGL_TEXTURE_WRAP_T, WEBGL_REPEAT) is true
   - Expected: ctx.textures[0].min_filter equals `WEBGL_NEAREST`
   - Expected: ctx.textures[0].wrap_s equals `WEBGL_CLAMP_TO_EDGE`
   - Expected: ctx.render_commands[1].kind equals `WEBGL_RENDER_COMMAND_TEX_PARAMETER`
   - Expected: ctx.render_commands[1].mode equals `WEBGL_TEXTURE_MIN_FILTER`
   - Expected: ctx.render_commands[1].element_type equals `WEBGL_NEAREST`
   - Expected: ctx.render_commands[4].kind equals `WEBGL_RENDER_COMMAND_TEX_PARAMETER`
   - Expected: ctx.render_commands[4].mode equals `WEBGL_TEXTURE_WRAP_T`
   - Expected: ctx.render_commands[4].element_type equals `WEBGL_REPEAT`
   - Expected: ctx.get_tex_parameter(WEBGL_TEXTURE_2D, WEBGL_TEXTURE_MIN_FILTER).int_value equals `WEBGL_NEAREST`
   - Expected: ctx.get_tex_parameter(WEBGL_TEXTURE_2D, WEBGL_TEXTURE_MAG_FILTER).int_value equals `WEBGL_LINEAR`
   - Expected: ctx.get_tex_parameter(WEBGL_TEXTURE_2D, WEBGL_TEXTURE_WRAP_S).int_value equals `WEBGL_CLAMP_TO_EDGE`
   - Expected: ctx.get_tex_parameter(WEBGL_TEXTURE_2D, WEBGL_TEXTURE_WRAP_T).int_value equals `WEBGL_REPEAT`
   - Expected: ctx.tex_parameter_i(WEBGL_TEXTURE_2D, WEBGL_TEXTURE_MAG_FILTER, WEBGL_LINEAR_MIPMAP_LINEAR) is false
   - Expected: ctx.get_error() equals `WEBGL_INVALID_ENUM`
   - Expected: ctx.tex_parameter_i(WEBGL_TEXTURE_2D, 999, WEBGL_LINEAR) is false
   - Expected: ctx.get_error() equals `WEBGL_INVALID_ENUM`
   - Expected: ctx.get_tex_parameter(WEBGL_TEXTURE_2D, 999).int_value equals `0`
   - Expected: ctx.get_error() equals `WEBGL_INVALID_ENUM`
   - Expected: ctx.bind_texture(WEBGL_TEXTURE_2D, -1) is true
   - Expected: ctx.get_tex_parameter(WEBGL_TEXTURE_2D, WEBGL_TEXTURE_MIN_FILTER).int_value equals `0`
   - Expected: ctx.get_error() equals `WEBGL_INVALID_OPERATION`


<details>
<summary>Executable SSpec</summary>

Runnable source: 33 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ctx = webgl_create_context(1, 320, 240)
val texture = ctx.create_texture()
expect(texture.min_filter).to_equal(WEBGL_LINEAR_MIPMAP_LINEAR)
expect(texture.mag_filter).to_equal(WEBGL_LINEAR)
expect(texture.wrap_s).to_equal(WEBGL_REPEAT)
expect(ctx.tex_parameter_i(WEBGL_TEXTURE_2D, WEBGL_TEXTURE_MIN_FILTER, WEBGL_NEAREST)).to_equal(false)
expect(ctx.get_error()).to_equal(WEBGL_INVALID_OPERATION)
expect(ctx.bind_texture(WEBGL_TEXTURE_2D, texture.id)).to_equal(true)
expect(ctx.tex_parameter_i(WEBGL_TEXTURE_2D, WEBGL_TEXTURE_MIN_FILTER, WEBGL_NEAREST)).to_equal(true)
expect(ctx.tex_parameter_i(WEBGL_TEXTURE_2D, WEBGL_TEXTURE_MAG_FILTER, WEBGL_LINEAR)).to_equal(true)
expect(ctx.tex_parameter_i(WEBGL_TEXTURE_2D, WEBGL_TEXTURE_WRAP_S, WEBGL_CLAMP_TO_EDGE)).to_equal(true)
expect(ctx.tex_parameter_i(WEBGL_TEXTURE_2D, WEBGL_TEXTURE_WRAP_T, WEBGL_REPEAT)).to_equal(true)
expect(ctx.textures[0].min_filter).to_equal(WEBGL_NEAREST)
expect(ctx.textures[0].wrap_s).to_equal(WEBGL_CLAMP_TO_EDGE)
expect(ctx.render_commands[1].kind).to_equal(WEBGL_RENDER_COMMAND_TEX_PARAMETER)
expect(ctx.render_commands[1].mode).to_equal(WEBGL_TEXTURE_MIN_FILTER)
expect(ctx.render_commands[1].element_type).to_equal(WEBGL_NEAREST)
expect(ctx.render_commands[4].kind).to_equal(WEBGL_RENDER_COMMAND_TEX_PARAMETER)
expect(ctx.render_commands[4].mode).to_equal(WEBGL_TEXTURE_WRAP_T)
expect(ctx.render_commands[4].element_type).to_equal(WEBGL_REPEAT)
expect(ctx.get_tex_parameter(WEBGL_TEXTURE_2D, WEBGL_TEXTURE_MIN_FILTER).int_value).to_equal(WEBGL_NEAREST)
expect(ctx.get_tex_parameter(WEBGL_TEXTURE_2D, WEBGL_TEXTURE_MAG_FILTER).int_value).to_equal(WEBGL_LINEAR)
expect(ctx.get_tex_parameter(WEBGL_TEXTURE_2D, WEBGL_TEXTURE_WRAP_S).int_value).to_equal(WEBGL_CLAMP_TO_EDGE)
expect(ctx.get_tex_parameter(WEBGL_TEXTURE_2D, WEBGL_TEXTURE_WRAP_T).int_value).to_equal(WEBGL_REPEAT)
expect(ctx.tex_parameter_i(WEBGL_TEXTURE_2D, WEBGL_TEXTURE_MAG_FILTER, WEBGL_LINEAR_MIPMAP_LINEAR)).to_equal(false)
expect(ctx.get_error()).to_equal(WEBGL_INVALID_ENUM)
expect(ctx.tex_parameter_i(WEBGL_TEXTURE_2D, 999, WEBGL_LINEAR)).to_equal(false)
expect(ctx.get_error()).to_equal(WEBGL_INVALID_ENUM)
expect(ctx.get_tex_parameter(WEBGL_TEXTURE_2D, 999).int_value).to_equal(0)
expect(ctx.get_error()).to_equal(WEBGL_INVALID_ENUM)
expect(ctx.bind_texture(WEBGL_TEXTURE_2D, -1)).to_equal(true)
expect(ctx.get_tex_parameter(WEBGL_TEXTURE_2D, WEBGL_TEXTURE_MIN_FILTER).int_value).to_equal(0)
expect(ctx.get_error()).to_equal(WEBGL_INVALID_OPERATION)
```

</details>

#### tracks active texture units and per-unit texture bindings

1. var ctx = webgl create context
   - Expected: ctx.active_texture_unit equals `0`
   - Expected: ctx.texture_units.len() equals `WEBGL_MAX_COMBINED_TEXTURE_IMAGE_UNITS`
   - Expected: ctx.get_parameter(WEBGL_ACTIVE_TEXTURE).int_value equals `WEBGL_TEXTURE0`
   - Expected: ctx.get_parameter(WEBGL_MAX_COMBINED_TEXTURE_IMAGE_UNITS).int_value equals `WEBGL_MAX_COMBINED_TEXTURE_IMAGE_UNITS`
   - Expected: ctx.bind_texture(WEBGL_TEXTURE_2D, first.id) is true
   - Expected: ctx.texture_units[0].texture_2d_id equals `first.id`
   - Expected: ctx.get_parameter(WEBGL_TEXTURE_BINDING_2D).int_value equals `first.id`
   - Expected: ctx.active_texture(WEBGL_TEXTURE0 + 1) is true
   - Expected: ctx.get_parameter(WEBGL_ACTIVE_TEXTURE).int_value equals `WEBGL_TEXTURE0 + 1`
   - Expected: ctx.bound_texture_2d equals `-1`
   - Expected: ctx.bind_texture(WEBGL_TEXTURE_2D, second.id) is true
   - Expected: ctx.texture_units[1].texture_2d_id equals `second.id`
   - Expected: ctx.active_texture(WEBGL_TEXTURE0) is true
   - Expected: ctx.bound_texture_2d equals `first.id`
   - Expected: ctx.bind_texture(WEBGL_TEXTURE_2D, -1) is true
   - Expected: ctx.texture_units[0].texture_2d_id equals `-1`
   - Expected: ctx.texture_units[1].texture_2d_id equals `second.id`
   - Expected: ctx.render_commands[1].kind equals `WEBGL_RENDER_COMMAND_ACTIVE_TEXTURE`
   - Expected: ctx.render_commands[1].target equals `WEBGL_TEXTURE0 + 1`
   - Expected: ctx.render_commands[2].kind equals `WEBGL_RENDER_COMMAND_BIND_TEXTURE`
   - Expected: ctx.render_commands[3].kind equals `WEBGL_RENDER_COMMAND_ACTIVE_TEXTURE`
   - Expected: ctx.render_commands[3].target equals `WEBGL_TEXTURE0`
   - Expected: ctx.active_texture(WEBGL_TEXTURE0 + WEBGL_MAX_COMBINED_TEXTURE_IMAGE_UNITS) is false
   - Expected: ctx.get_error() equals `WEBGL_INVALID_ENUM`


<details>
<summary>Executable SSpec</summary>

Runnable source: 27 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ctx = webgl_create_context(1, 320, 240)
val first = ctx.create_texture()
val second = ctx.create_texture()
expect(ctx.active_texture_unit).to_equal(0)
expect(ctx.texture_units.len()).to_equal(WEBGL_MAX_COMBINED_TEXTURE_IMAGE_UNITS)
expect(ctx.get_parameter(WEBGL_ACTIVE_TEXTURE).int_value).to_equal(WEBGL_TEXTURE0)
expect(ctx.get_parameter(WEBGL_MAX_COMBINED_TEXTURE_IMAGE_UNITS).int_value).to_equal(WEBGL_MAX_COMBINED_TEXTURE_IMAGE_UNITS)
expect(ctx.bind_texture(WEBGL_TEXTURE_2D, first.id)).to_equal(true)
expect(ctx.texture_units[0].texture_2d_id).to_equal(first.id)
expect(ctx.get_parameter(WEBGL_TEXTURE_BINDING_2D).int_value).to_equal(first.id)
expect(ctx.active_texture(WEBGL_TEXTURE0 + 1)).to_equal(true)
expect(ctx.get_parameter(WEBGL_ACTIVE_TEXTURE).int_value).to_equal(WEBGL_TEXTURE0 + 1)
expect(ctx.bound_texture_2d).to_equal(-1)
expect(ctx.bind_texture(WEBGL_TEXTURE_2D, second.id)).to_equal(true)
expect(ctx.texture_units[1].texture_2d_id).to_equal(second.id)
expect(ctx.active_texture(WEBGL_TEXTURE0)).to_equal(true)
expect(ctx.bound_texture_2d).to_equal(first.id)
expect(ctx.bind_texture(WEBGL_TEXTURE_2D, -1)).to_equal(true)
expect(ctx.texture_units[0].texture_2d_id).to_equal(-1)
expect(ctx.texture_units[1].texture_2d_id).to_equal(second.id)
expect(ctx.render_commands[1].kind).to_equal(WEBGL_RENDER_COMMAND_ACTIVE_TEXTURE)
expect(ctx.render_commands[1].target).to_equal(WEBGL_TEXTURE0 + 1)
expect(ctx.render_commands[2].kind).to_equal(WEBGL_RENDER_COMMAND_BIND_TEXTURE)
expect(ctx.render_commands[3].kind).to_equal(WEBGL_RENDER_COMMAND_ACTIVE_TEXTURE)
expect(ctx.render_commands[3].target).to_equal(WEBGL_TEXTURE0)
expect(ctx.active_texture(WEBGL_TEXTURE0 + WEBGL_MAX_COMBINED_TEXTURE_IMAGE_UNITS)).to_equal(false)
expect(ctx.get_error()).to_equal(WEBGL_INVALID_ENUM)
```

</details>

#### generates mipmaps for initialized power-of-two textures

1. var ctx = webgl create context
   - Expected: ctx.bind_texture(WEBGL_TEXTURE_2D, texture.id) is true
   - Expected: ctx.generate_mipmap(WEBGL_TEXTURE_2D) is false
   - Expected: ctx.get_error() equals `WEBGL_INVALID_OPERATION`
   - Expected: ctx.tex_image_2d(WEBGL_TEXTURE_2D, 0, WEBGL_RGBA, 3, 2, 0, WEBGL_RGBA, WEBGL_UNSIGNED_BYTE, []) is true
   - Expected: ctx.generate_mipmap(WEBGL_TEXTURE_2D) is false
   - Expected: ctx.get_error() equals `WEBGL_INVALID_OPERATION`
   - Expected: ctx.tex_image_2d(WEBGL_TEXTURE_2D, 0, WEBGL_RGBA, 4, 2, 0, WEBGL_RGBA, WEBGL_UNSIGNED_BYTE, []) is true
   - Expected: ctx.generate_mipmap(WEBGL_TEXTURE_2D) is true
   - Expected: ctx.textures[0].mipmap_generated is true
   - Expected: ctx.render_commands[3].kind equals `WEBGL_RENDER_COMMAND_GENERATE_MIPMAP`
   - Expected: ctx.render_commands[3].target equals `WEBGL_TEXTURE_2D`
   - Expected: ctx.tex_image_2d(WEBGL_TEXTURE_2D, 0, WEBGL_RGBA, 4, 4, 0, WEBGL_RGBA, WEBGL_UNSIGNED_BYTE, []) is true
   - Expected: ctx.textures[0].mipmap_generated is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ctx = webgl_create_context(1, 320, 240)
val texture = ctx.create_texture()
expect(ctx.bind_texture(WEBGL_TEXTURE_2D, texture.id)).to_equal(true)
expect(ctx.generate_mipmap(WEBGL_TEXTURE_2D)).to_equal(false)
expect(ctx.get_error()).to_equal(WEBGL_INVALID_OPERATION)
expect(ctx.tex_image_2d(WEBGL_TEXTURE_2D, 0, WEBGL_RGBA, 3, 2, 0, WEBGL_RGBA, WEBGL_UNSIGNED_BYTE, [])).to_equal(true)
expect(ctx.generate_mipmap(WEBGL_TEXTURE_2D)).to_equal(false)
expect(ctx.get_error()).to_equal(WEBGL_INVALID_OPERATION)
expect(ctx.tex_image_2d(WEBGL_TEXTURE_2D, 0, WEBGL_RGBA, 4, 2, 0, WEBGL_RGBA, WEBGL_UNSIGNED_BYTE, [])).to_equal(true)
expect(ctx.generate_mipmap(WEBGL_TEXTURE_2D)).to_equal(true)
expect(ctx.textures[0].mipmap_generated).to_equal(true)
expect(ctx.render_commands[3].kind).to_equal(WEBGL_RENDER_COMMAND_GENERATE_MIPMAP)
expect(ctx.render_commands[3].target).to_equal(WEBGL_TEXTURE_2D)
expect(ctx.tex_image_2d(WEBGL_TEXTURE_2D, 0, WEBGL_RGBA, 4, 4, 0, WEBGL_RGBA, WEBGL_UNSIGNED_BYTE, [])).to_equal(true)
expect(ctx.textures[0].mipmap_generated).to_equal(false)
```

</details>

#### blocks texture operations while context is lost

1. var ctx = webgl create context
2. ctx lose context
   - Expected: ctx.bind_texture(WEBGL_TEXTURE_2D, 1) is false
   - Expected: ctx.get_error() equals `WEBGL_CONTEXT_LOST_WEBGL`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ctx = webgl_create_context(1, 320, 240)
ctx.lose_context()
expect(ctx.bind_texture(WEBGL_TEXTURE_2D, 1)).to_equal(false)
expect(ctx.get_error()).to_equal(WEBGL_CONTEXT_LOST_WEBGL)
```

</details>

### framebuffers

#### binds framebuffers and reports default framebuffer complete

1. var ctx = webgl create context
   - Expected: ctx.check_framebuffer_status(WEBGL_FRAMEBUFFER) equals `WEBGL_FRAMEBUFFER_COMPLETE`
   - Expected: ctx.bind_framebuffer(WEBGL_FRAMEBUFFER, framebuffer.id) is true
   - Expected: ctx.bound_framebuffer equals `framebuffer.id`
   - Expected: ctx.render_commands[0].kind equals `WEBGL_RENDER_COMMAND_BIND_FRAMEBUFFER`
   - Expected: ctx.render_commands[0].target equals `WEBGL_FRAMEBUFFER`
   - Expected: ctx.render_commands[0].texture_id equals `framebuffer.id`
   - Expected: ctx.get_parameter(WEBGL_FRAMEBUFFER_BINDING).int_value equals `framebuffer.id`
   - Expected: ctx.check_framebuffer_status(WEBGL_FRAMEBUFFER) equals `WEBGL_FRAMEBUFFER_INCOMPLETE_MISSING_ATTACHMENT`
   - Expected: ctx.bind_framebuffer(WEBGL_FRAMEBUFFER, -1) is true
   - Expected: ctx.bound_framebuffer equals `-1`
   - Expected: ctx.check_framebuffer_status(WEBGL_FRAMEBUFFER) equals `WEBGL_FRAMEBUFFER_COMPLETE`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ctx = webgl_create_context(1, 320, 240)
expect(ctx.check_framebuffer_status(WEBGL_FRAMEBUFFER)).to_equal(WEBGL_FRAMEBUFFER_COMPLETE)
val framebuffer = ctx.create_framebuffer()
expect(ctx.bind_framebuffer(WEBGL_FRAMEBUFFER, framebuffer.id)).to_equal(true)
expect(ctx.bound_framebuffer).to_equal(framebuffer.id)
expect(ctx.render_commands[0].kind).to_equal(WEBGL_RENDER_COMMAND_BIND_FRAMEBUFFER)
expect(ctx.render_commands[0].target).to_equal(WEBGL_FRAMEBUFFER)
expect(ctx.render_commands[0].texture_id).to_equal(framebuffer.id)
expect(ctx.get_parameter(WEBGL_FRAMEBUFFER_BINDING).int_value).to_equal(framebuffer.id)
expect(ctx.check_framebuffer_status(WEBGL_FRAMEBUFFER)).to_equal(WEBGL_FRAMEBUFFER_INCOMPLETE_MISSING_ATTACHMENT)
expect(ctx.bind_framebuffer(WEBGL_FRAMEBUFFER, -1)).to_equal(true)
expect(ctx.bound_framebuffer).to_equal(-1)
expect(ctx.check_framebuffer_status(WEBGL_FRAMEBUFFER)).to_equal(WEBGL_FRAMEBUFFER_COMPLETE)
```

</details>

#### attaches initialized color textures and checks completeness

1. var ctx = webgl create context
   - Expected: ctx.bind_framebuffer(WEBGL_FRAMEBUFFER, framebuffer.id) is true
   - Expected: ctx.framebuffer_texture_2d(WEBGL_FRAMEBUFFER, WEBGL_COLOR_ATTACHMENT0, WEBGL_TEXTURE_2D, texture.id, 0) is false
   - Expected: ctx.get_error() equals `WEBGL_INVALID_OPERATION`
   - Expected: ctx.bind_texture(WEBGL_TEXTURE_2D, texture.id) is true
   - Expected: ctx.framebuffer_texture_2d(WEBGL_FRAMEBUFFER, WEBGL_COLOR_ATTACHMENT0, WEBGL_TEXTURE_2D, texture.id, 0) is true
   - Expected: ctx.render_commands[2].kind equals `WEBGL_RENDER_COMMAND_FRAMEBUFFER_TEXTURE_2D`
   - Expected: ctx.render_commands[2].target equals `WEBGL_FRAMEBUFFER`
   - Expected: ctx.render_commands[2].mask equals `WEBGL_COLOR_ATTACHMENT0`
   - Expected: ctx.render_commands[2].texture_id equals `texture.id`
   - Expected: ctx.render_commands[2].mode equals `WEBGL_TEXTURE_2D`
   - Expected: ctx.check_framebuffer_status(WEBGL_FRAMEBUFFER) equals `WEBGL_FRAMEBUFFER_INCOMPLETE_ATTACHMENT`
   - Expected: ctx.tex_image_2d(WEBGL_TEXTURE_2D, 0, WEBGL_RGBA, 2, 2, 0, WEBGL_RGBA, WEBGL_UNSIGNED_BYTE, []) is true
   - Expected: ctx.check_framebuffer_status(WEBGL_FRAMEBUFFER) equals `WEBGL_FRAMEBUFFER_COMPLETE`
   - Expected: ctx.framebuffers[0].color_texture_id equals `texture.id`
   - Expected: ctx.get_framebuffer_attachment_parameter(WEBGL_FRAMEBUFFER, WEBGL_COLOR_ATTACHMENT0, WEBGL_FRAMEBUFFER_ATTACHMENT_OBJECT_TYPE).int_value equals `WEBGL_TEXTURE`
   - Expected: ctx.get_framebuffer_attachment_parameter(WEBGL_FRAMEBUFFER, WEBGL_COLOR_ATTACHMENT0, WEBGL_FRAMEBUFFER_ATTACHMENT_OBJECT_NAME).int_value equals `texture.id`
   - Expected: ctx.get_framebuffer_attachment_parameter(WEBGL_FRAMEBUFFER, WEBGL_COLOR_ATTACHMENT0, WEBGL_FRAMEBUFFER_ATTACHMENT_TEXTURE_LEVEL).int_value equals `0`
   - Expected: ctx.get_framebuffer_attachment_parameter(WEBGL_FRAMEBUFFER, WEBGL_COLOR_ATTACHMENT0, WEBGL_FRAMEBUFFER_ATTACHMENT_TEXTURE_CUBE_MAP_FACE).int_value equals `0`
   - Expected: ctx.framebuffer_texture_2d(WEBGL_FRAMEBUFFER, WEBGL_COLOR_ATTACHMENT0, WEBGL_TEXTURE_2D, -1, 0) is true
   - Expected: ctx.get_framebuffer_attachment_parameter(WEBGL_FRAMEBUFFER, WEBGL_COLOR_ATTACHMENT0, WEBGL_FRAMEBUFFER_ATTACHMENT_OBJECT_TYPE).int_value equals `WEBGL_NO_ERROR`
   - Expected: ctx.check_framebuffer_status(WEBGL_FRAMEBUFFER) equals `WEBGL_FRAMEBUFFER_INCOMPLETE_MISSING_ATTACHMENT`


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ctx = webgl_create_context(1, 320, 240)
val framebuffer = ctx.create_framebuffer()
val texture = ctx.create_texture()
expect(ctx.bind_framebuffer(WEBGL_FRAMEBUFFER, framebuffer.id)).to_equal(true)
expect(ctx.framebuffer_texture_2d(WEBGL_FRAMEBUFFER, WEBGL_COLOR_ATTACHMENT0, WEBGL_TEXTURE_2D, texture.id, 0)).to_equal(false)
expect(ctx.get_error()).to_equal(WEBGL_INVALID_OPERATION)
expect(ctx.bind_texture(WEBGL_TEXTURE_2D, texture.id)).to_equal(true)
expect(ctx.framebuffer_texture_2d(WEBGL_FRAMEBUFFER, WEBGL_COLOR_ATTACHMENT0, WEBGL_TEXTURE_2D, texture.id, 0)).to_equal(true)
expect(ctx.render_commands[2].kind).to_equal(WEBGL_RENDER_COMMAND_FRAMEBUFFER_TEXTURE_2D)
expect(ctx.render_commands[2].target).to_equal(WEBGL_FRAMEBUFFER)
expect(ctx.render_commands[2].mask).to_equal(WEBGL_COLOR_ATTACHMENT0)
expect(ctx.render_commands[2].texture_id).to_equal(texture.id)
expect(ctx.render_commands[2].mode).to_equal(WEBGL_TEXTURE_2D)
expect(ctx.check_framebuffer_status(WEBGL_FRAMEBUFFER)).to_equal(WEBGL_FRAMEBUFFER_INCOMPLETE_ATTACHMENT)
expect(ctx.tex_image_2d(WEBGL_TEXTURE_2D, 0, WEBGL_RGBA, 2, 2, 0, WEBGL_RGBA, WEBGL_UNSIGNED_BYTE, [])).to_equal(true)
expect(ctx.check_framebuffer_status(WEBGL_FRAMEBUFFER)).to_equal(WEBGL_FRAMEBUFFER_COMPLETE)
expect(ctx.framebuffers[0].color_texture_id).to_equal(texture.id)
expect(ctx.get_framebuffer_attachment_parameter(WEBGL_FRAMEBUFFER, WEBGL_COLOR_ATTACHMENT0, WEBGL_FRAMEBUFFER_ATTACHMENT_OBJECT_TYPE).int_value).to_equal(WEBGL_TEXTURE)
expect(ctx.get_framebuffer_attachment_parameter(WEBGL_FRAMEBUFFER, WEBGL_COLOR_ATTACHMENT0, WEBGL_FRAMEBUFFER_ATTACHMENT_OBJECT_NAME).int_value).to_equal(texture.id)
expect(ctx.get_framebuffer_attachment_parameter(WEBGL_FRAMEBUFFER, WEBGL_COLOR_ATTACHMENT0, WEBGL_FRAMEBUFFER_ATTACHMENT_TEXTURE_LEVEL).int_value).to_equal(0)
expect(ctx.get_framebuffer_attachment_parameter(WEBGL_FRAMEBUFFER, WEBGL_COLOR_ATTACHMENT0, WEBGL_FRAMEBUFFER_ATTACHMENT_TEXTURE_CUBE_MAP_FACE).int_value).to_equal(0)
expect(ctx.framebuffer_texture_2d(WEBGL_FRAMEBUFFER, WEBGL_COLOR_ATTACHMENT0, WEBGL_TEXTURE_2D, -1, 0)).to_equal(true)
expect(ctx.get_framebuffer_attachment_parameter(WEBGL_FRAMEBUFFER, WEBGL_COLOR_ATTACHMENT0, WEBGL_FRAMEBUFFER_ATTACHMENT_OBJECT_TYPE).int_value).to_equal(WEBGL_NO_ERROR)
expect(ctx.check_framebuffer_status(WEBGL_FRAMEBUFFER)).to_equal(WEBGL_FRAMEBUFFER_INCOMPLETE_MISSING_ATTACHMENT)
```

</details>

#### allocates renderbuffer storage and attaches color buffers

1. var ctx = webgl create context
   - Expected: ctx.bind_framebuffer(WEBGL_FRAMEBUFFER, framebuffer.id) is true
   - Expected: ctx.framebuffer_renderbuffer(WEBGL_FRAMEBUFFER, WEBGL_COLOR_ATTACHMENT0, WEBGL_RENDERBUFFER, renderbuffer.id) is true
   - Expected: ctx.check_framebuffer_status(WEBGL_FRAMEBUFFER) equals `WEBGL_FRAMEBUFFER_INCOMPLETE_ATTACHMENT`
   - Expected: ctx.bind_renderbuffer(WEBGL_RENDERBUFFER, renderbuffer.id) is true
   - Expected: ctx.get_parameter(WEBGL_RENDERBUFFER_BINDING).int_value equals `renderbuffer.id`
   - Expected: ctx.renderbuffer_storage(WEBGL_RENDERBUFFER, WEBGL_RGBA4, 16, 16) is true
   - Expected: ctx.render_commands[1].kind equals `WEBGL_RENDER_COMMAND_FRAMEBUFFER_RENDERBUFFER`
   - Expected: ctx.render_commands[1].target equals `WEBGL_FRAMEBUFFER`
   - Expected: ctx.render_commands[1].mask equals `WEBGL_COLOR_ATTACHMENT0`
   - Expected: ctx.render_commands[1].texture_id equals `renderbuffer.id`
   - Expected: ctx.render_commands[2].kind equals `WEBGL_RENDER_COMMAND_BIND_RENDERBUFFER`
   - Expected: ctx.render_commands[2].target equals `WEBGL_RENDERBUFFER`
   - Expected: ctx.render_commands[2].texture_id equals `renderbuffer.id`
   - Expected: ctx.render_commands[3].kind equals `WEBGL_RENDER_COMMAND_RENDERBUFFER_STORAGE`
   - Expected: ctx.render_commands[3].mask equals `WEBGL_RGBA4`
   - Expected: ctx.render_commands[3].width equals `16`
   - Expected: ctx.render_commands[3].height equals `16`
   - Expected: ctx.renderbuffers[0].initialized is true
   - Expected: ctx.renderbuffers[0].internal_format equals `WEBGL_RGBA4`
   - Expected: ctx.get_renderbuffer_parameter(WEBGL_RENDERBUFFER, WEBGL_RENDERBUFFER_INTERNAL_FORMAT).int_value equals `WEBGL_RGBA4`
   - Expected: ctx.get_renderbuffer_parameter(WEBGL_RENDERBUFFER, WEBGL_RENDERBUFFER_WIDTH).int_value equals `16`
   - Expected: ctx.get_renderbuffer_parameter(WEBGL_RENDERBUFFER, WEBGL_RENDERBUFFER_HEIGHT).int_value equals `16`
   - Expected: ctx.framebuffers[0].color_renderbuffer_id equals `renderbuffer.id`
   - Expected: ctx.get_framebuffer_attachment_parameter(WEBGL_FRAMEBUFFER, WEBGL_COLOR_ATTACHMENT0, WEBGL_FRAMEBUFFER_ATTACHMENT_OBJECT_TYPE).int_value equals `WEBGL_RENDERBUFFER`
   - Expected: ctx.get_framebuffer_attachment_parameter(WEBGL_FRAMEBUFFER, WEBGL_COLOR_ATTACHMENT0, WEBGL_FRAMEBUFFER_ATTACHMENT_OBJECT_NAME).int_value equals `renderbuffer.id`
   - Expected: ctx.get_framebuffer_attachment_parameter(WEBGL_FRAMEBUFFER, WEBGL_COLOR_ATTACHMENT0, WEBGL_FRAMEBUFFER_ATTACHMENT_TEXTURE_LEVEL).int_value equals `0`
   - Expected: ctx.get_error() equals `WEBGL_INVALID_ENUM`
   - Expected: ctx.check_framebuffer_status(WEBGL_FRAMEBUFFER) equals `WEBGL_FRAMEBUFFER_COMPLETE`
   - Expected: ctx.framebuffer_renderbuffer(WEBGL_FRAMEBUFFER, WEBGL_COLOR_ATTACHMENT0, WEBGL_RENDERBUFFER, -1) is true
   - Expected: ctx.check_framebuffer_status(WEBGL_FRAMEBUFFER) equals `WEBGL_FRAMEBUFFER_INCOMPLETE_MISSING_ATTACHMENT`


<details>
<summary>Executable SSpec</summary>

Runnable source: 33 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ctx = webgl_create_context(1, 320, 240)
val framebuffer = ctx.create_framebuffer()
val renderbuffer = ctx.create_renderbuffer()
expect(ctx.bind_framebuffer(WEBGL_FRAMEBUFFER, framebuffer.id)).to_equal(true)
expect(ctx.framebuffer_renderbuffer(WEBGL_FRAMEBUFFER, WEBGL_COLOR_ATTACHMENT0, WEBGL_RENDERBUFFER, renderbuffer.id)).to_equal(true)
expect(ctx.check_framebuffer_status(WEBGL_FRAMEBUFFER)).to_equal(WEBGL_FRAMEBUFFER_INCOMPLETE_ATTACHMENT)
expect(ctx.bind_renderbuffer(WEBGL_RENDERBUFFER, renderbuffer.id)).to_equal(true)
expect(ctx.get_parameter(WEBGL_RENDERBUFFER_BINDING).int_value).to_equal(renderbuffer.id)
expect(ctx.renderbuffer_storage(WEBGL_RENDERBUFFER, WEBGL_RGBA4, 16, 16)).to_equal(true)
expect(ctx.render_commands[1].kind).to_equal(WEBGL_RENDER_COMMAND_FRAMEBUFFER_RENDERBUFFER)
expect(ctx.render_commands[1].target).to_equal(WEBGL_FRAMEBUFFER)
expect(ctx.render_commands[1].mask).to_equal(WEBGL_COLOR_ATTACHMENT0)
expect(ctx.render_commands[1].texture_id).to_equal(renderbuffer.id)
expect(ctx.render_commands[2].kind).to_equal(WEBGL_RENDER_COMMAND_BIND_RENDERBUFFER)
expect(ctx.render_commands[2].target).to_equal(WEBGL_RENDERBUFFER)
expect(ctx.render_commands[2].texture_id).to_equal(renderbuffer.id)
expect(ctx.render_commands[3].kind).to_equal(WEBGL_RENDER_COMMAND_RENDERBUFFER_STORAGE)
expect(ctx.render_commands[3].mask).to_equal(WEBGL_RGBA4)
expect(ctx.render_commands[3].width).to_equal(16)
expect(ctx.render_commands[3].height).to_equal(16)
expect(ctx.renderbuffers[0].initialized).to_equal(true)
expect(ctx.renderbuffers[0].internal_format).to_equal(WEBGL_RGBA4)
expect(ctx.get_renderbuffer_parameter(WEBGL_RENDERBUFFER, WEBGL_RENDERBUFFER_INTERNAL_FORMAT).int_value).to_equal(WEBGL_RGBA4)
expect(ctx.get_renderbuffer_parameter(WEBGL_RENDERBUFFER, WEBGL_RENDERBUFFER_WIDTH).int_value).to_equal(16)
expect(ctx.get_renderbuffer_parameter(WEBGL_RENDERBUFFER, WEBGL_RENDERBUFFER_HEIGHT).int_value).to_equal(16)
expect(ctx.framebuffers[0].color_renderbuffer_id).to_equal(renderbuffer.id)
expect(ctx.get_framebuffer_attachment_parameter(WEBGL_FRAMEBUFFER, WEBGL_COLOR_ATTACHMENT0, WEBGL_FRAMEBUFFER_ATTACHMENT_OBJECT_TYPE).int_value).to_equal(WEBGL_RENDERBUFFER)
expect(ctx.get_framebuffer_attachment_parameter(WEBGL_FRAMEBUFFER, WEBGL_COLOR_ATTACHMENT0, WEBGL_FRAMEBUFFER_ATTACHMENT_OBJECT_NAME).int_value).to_equal(renderbuffer.id)
expect(ctx.get_framebuffer_attachment_parameter(WEBGL_FRAMEBUFFER, WEBGL_COLOR_ATTACHMENT0, WEBGL_FRAMEBUFFER_ATTACHMENT_TEXTURE_LEVEL).int_value).to_equal(0)
expect(ctx.get_error()).to_equal(WEBGL_INVALID_ENUM)
expect(ctx.check_framebuffer_status(WEBGL_FRAMEBUFFER)).to_equal(WEBGL_FRAMEBUFFER_COMPLETE)
expect(ctx.framebuffer_renderbuffer(WEBGL_FRAMEBUFFER, WEBGL_COLOR_ATTACHMENT0, WEBGL_RENDERBUFFER, -1)).to_equal(true)
expect(ctx.check_framebuffer_status(WEBGL_FRAMEBUFFER)).to_equal(WEBGL_FRAMEBUFFER_INCOMPLETE_MISSING_ATTACHMENT)
```

</details>

#### supports depth stencil renderbuffer completeness

1. var ctx = webgl create context
   - Expected: ctx.bind_framebuffer(WEBGL_FRAMEBUFFER, framebuffer.id) is true
   - Expected: ctx.bind_renderbuffer(WEBGL_RENDERBUFFER, depth.id) is true
   - Expected: ctx.renderbuffer_storage(WEBGL_RENDERBUFFER, WEBGL_DEPTH_COMPONENT16, 8, 8) is true
   - Expected: ctx.bind_renderbuffer(WEBGL_RENDERBUFFER, stencil.id) is true
   - Expected: ctx.renderbuffer_storage(WEBGL_RENDERBUFFER, WEBGL_STENCIL_INDEX8, 8, 8) is true
   - Expected: ctx.framebuffer_renderbuffer(WEBGL_FRAMEBUFFER, WEBGL_DEPTH_ATTACHMENT, WEBGL_RENDERBUFFER, depth.id) is true
   - Expected: ctx.framebuffer_renderbuffer(WEBGL_FRAMEBUFFER, WEBGL_STENCIL_ATTACHMENT, WEBGL_RENDERBUFFER, stencil.id) is true
   - Expected: ctx.check_framebuffer_status(WEBGL_FRAMEBUFFER) equals `WEBGL_FRAMEBUFFER_COMPLETE`
   - Expected: ctx.bind_renderbuffer(WEBGL_RENDERBUFFER, packed.id) is true
   - Expected: ctx.renderbuffer_storage(WEBGL_RENDERBUFFER, WEBGL_DEPTH_STENCIL, 8, 8) is true
   - Expected: ctx.framebuffer_renderbuffer(WEBGL_FRAMEBUFFER, WEBGL_DEPTH_STENCIL_ATTACHMENT, WEBGL_RENDERBUFFER, packed.id) is true
   - Expected: ctx.framebuffers[0].depth_renderbuffer_id equals `-1`
   - Expected: ctx.framebuffers[0].stencil_renderbuffer_id equals `-1`
   - Expected: ctx.framebuffers[0].depth_stencil_renderbuffer_id equals `packed.id`
   - Expected: ctx.check_framebuffer_status(WEBGL_FRAMEBUFFER) equals `WEBGL_FRAMEBUFFER_COMPLETE`


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ctx = webgl_create_context(1, 320, 240)
val framebuffer = ctx.create_framebuffer()
val depth = ctx.create_renderbuffer()
val stencil = ctx.create_renderbuffer()
val packed = ctx.create_renderbuffer()
expect(ctx.bind_framebuffer(WEBGL_FRAMEBUFFER, framebuffer.id)).to_equal(true)
expect(ctx.bind_renderbuffer(WEBGL_RENDERBUFFER, depth.id)).to_equal(true)
expect(ctx.renderbuffer_storage(WEBGL_RENDERBUFFER, WEBGL_DEPTH_COMPONENT16, 8, 8)).to_equal(true)
expect(ctx.bind_renderbuffer(WEBGL_RENDERBUFFER, stencil.id)).to_equal(true)
expect(ctx.renderbuffer_storage(WEBGL_RENDERBUFFER, WEBGL_STENCIL_INDEX8, 8, 8)).to_equal(true)
expect(ctx.framebuffer_renderbuffer(WEBGL_FRAMEBUFFER, WEBGL_DEPTH_ATTACHMENT, WEBGL_RENDERBUFFER, depth.id)).to_equal(true)
expect(ctx.framebuffer_renderbuffer(WEBGL_FRAMEBUFFER, WEBGL_STENCIL_ATTACHMENT, WEBGL_RENDERBUFFER, stencil.id)).to_equal(true)
expect(ctx.check_framebuffer_status(WEBGL_FRAMEBUFFER)).to_equal(WEBGL_FRAMEBUFFER_COMPLETE)
expect(ctx.bind_renderbuffer(WEBGL_RENDERBUFFER, packed.id)).to_equal(true)
expect(ctx.renderbuffer_storage(WEBGL_RENDERBUFFER, WEBGL_DEPTH_STENCIL, 8, 8)).to_equal(true)
expect(ctx.framebuffer_renderbuffer(WEBGL_FRAMEBUFFER, WEBGL_DEPTH_STENCIL_ATTACHMENT, WEBGL_RENDERBUFFER, packed.id)).to_equal(true)
expect(ctx.framebuffers[0].depth_renderbuffer_id).to_equal(-1)
expect(ctx.framebuffers[0].stencil_renderbuffer_id).to_equal(-1)
expect(ctx.framebuffers[0].depth_stencil_renderbuffer_id).to_equal(packed.id)
expect(ctx.check_framebuffer_status(WEBGL_FRAMEBUFFER)).to_equal(WEBGL_FRAMEBUFFER_COMPLETE)
```

</details>

#### validates framebuffer target attachment and level

1. var ctx = webgl create context
   - Expected: ctx.bind_framebuffer(999, framebuffer.id) is false
   - Expected: ctx.get_error() equals `WEBGL_INVALID_ENUM`
   - Expected: ctx.bind_framebuffer(WEBGL_FRAMEBUFFER, 99) is false
   - Expected: ctx.get_error() equals `WEBGL_INVALID_VALUE`
   - Expected: ctx.framebuffer_texture_2d(WEBGL_FRAMEBUFFER, WEBGL_COLOR_ATTACHMENT0, WEBGL_TEXTURE_2D, texture.id, 0) is false
   - Expected: ctx.get_error() equals `WEBGL_INVALID_OPERATION`
   - Expected: ctx.bind_framebuffer(WEBGL_FRAMEBUFFER, framebuffer.id) is true
   - Expected: ctx.framebuffer_texture_2d(WEBGL_FRAMEBUFFER, 999, WEBGL_TEXTURE_2D, texture.id, 0) is false
   - Expected: ctx.get_error() equals `WEBGL_INVALID_ENUM`
   - Expected: ctx.framebuffer_texture_2d(WEBGL_FRAMEBUFFER, WEBGL_COLOR_ATTACHMENT0, WEBGL_TEXTURE_2D, texture.id, 1) is false
   - Expected: ctx.get_error() equals `WEBGL_INVALID_VALUE`
   - Expected: ctx.get_framebuffer_attachment_parameter(WEBGL_FRAMEBUFFER, 999, WEBGL_FRAMEBUFFER_ATTACHMENT_OBJECT_TYPE).int_value equals `0`
   - Expected: ctx.get_error() equals `WEBGL_INVALID_ENUM`
   - Expected: ctx.bind_framebuffer(WEBGL_FRAMEBUFFER, -1) is true
   - Expected: ctx.get_framebuffer_attachment_parameter(WEBGL_FRAMEBUFFER, WEBGL_COLOR_ATTACHMENT0, WEBGL_FRAMEBUFFER_ATTACHMENT_OBJECT_TYPE).int_value equals `0`
   - Expected: ctx.get_error() equals `WEBGL_INVALID_OPERATION`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ctx = webgl_create_context(1, 320, 240)
val framebuffer = ctx.create_framebuffer()
val texture = ctx.create_texture()
expect(ctx.bind_framebuffer(999, framebuffer.id)).to_equal(false)
expect(ctx.get_error()).to_equal(WEBGL_INVALID_ENUM)
expect(ctx.bind_framebuffer(WEBGL_FRAMEBUFFER, 99)).to_equal(false)
expect(ctx.get_error()).to_equal(WEBGL_INVALID_VALUE)
expect(ctx.framebuffer_texture_2d(WEBGL_FRAMEBUFFER, WEBGL_COLOR_ATTACHMENT0, WEBGL_TEXTURE_2D, texture.id, 0)).to_equal(false)
expect(ctx.get_error()).to_equal(WEBGL_INVALID_OPERATION)
expect(ctx.bind_framebuffer(WEBGL_FRAMEBUFFER, framebuffer.id)).to_equal(true)
expect(ctx.framebuffer_texture_2d(WEBGL_FRAMEBUFFER, 999, WEBGL_TEXTURE_2D, texture.id, 0)).to_equal(false)
expect(ctx.get_error()).to_equal(WEBGL_INVALID_ENUM)
expect(ctx.framebuffer_texture_2d(WEBGL_FRAMEBUFFER, WEBGL_COLOR_ATTACHMENT0, WEBGL_TEXTURE_2D, texture.id, 1)).to_equal(false)
expect(ctx.get_error()).to_equal(WEBGL_INVALID_VALUE)
expect(ctx.get_framebuffer_attachment_parameter(WEBGL_FRAMEBUFFER, 999, WEBGL_FRAMEBUFFER_ATTACHMENT_OBJECT_TYPE).int_value).to_equal(0)
expect(ctx.get_error()).to_equal(WEBGL_INVALID_ENUM)
expect(ctx.bind_framebuffer(WEBGL_FRAMEBUFFER, -1)).to_equal(true)
expect(ctx.get_framebuffer_attachment_parameter(WEBGL_FRAMEBUFFER, WEBGL_COLOR_ATTACHMENT0, WEBGL_FRAMEBUFFER_ATTACHMENT_OBJECT_TYPE).int_value).to_equal(0)
expect(ctx.get_error()).to_equal(WEBGL_INVALID_OPERATION)
```

</details>

#### validates renderbuffer target format and attachment compatibility

1. var ctx = webgl create context
   - Expected: ctx.bind_renderbuffer(999, renderbuffer.id) is false
   - Expected: ctx.get_error() equals `WEBGL_INVALID_ENUM`
   - Expected: ctx.bind_renderbuffer(WEBGL_RENDERBUFFER, 99) is false
   - Expected: ctx.get_error() equals `WEBGL_INVALID_VALUE`
   - Expected: ctx.renderbuffer_storage(WEBGL_RENDERBUFFER, WEBGL_RGBA4, 4, 4) is false
   - Expected: ctx.get_error() equals `WEBGL_INVALID_OPERATION`
   - Expected: ctx.bind_renderbuffer(WEBGL_RENDERBUFFER, renderbuffer.id) is true
   - Expected: ctx.renderbuffer_storage(WEBGL_RENDERBUFFER, WEBGL_RGBA4, -1, 4) is false
   - Expected: ctx.get_error() equals `WEBGL_INVALID_VALUE`
   - Expected: ctx.renderbuffer_storage(WEBGL_RENDERBUFFER, WEBGL_RGB565, 4, 4) is true
   - Expected: ctx.bind_framebuffer(WEBGL_FRAMEBUFFER, framebuffer.id) is true
   - Expected: ctx.framebuffer_renderbuffer(WEBGL_FRAMEBUFFER, WEBGL_DEPTH_ATTACHMENT, WEBGL_RENDERBUFFER, renderbuffer.id) is true
   - Expected: ctx.check_framebuffer_status(WEBGL_FRAMEBUFFER) equals `WEBGL_FRAMEBUFFER_INCOMPLETE_ATTACHMENT`
   - Expected: ctx.framebuffer_renderbuffer(WEBGL_FRAMEBUFFER, 999, WEBGL_RENDERBUFFER, renderbuffer.id) is false
   - Expected: ctx.get_error() equals `WEBGL_INVALID_ENUM`
   - Expected: ctx.get_renderbuffer_parameter(WEBGL_RENDERBUFFER, 999).int_value equals `0`
   - Expected: ctx.get_error() equals `WEBGL_INVALID_ENUM`
   - Expected: ctx.bind_renderbuffer(WEBGL_RENDERBUFFER, -1) is true
   - Expected: ctx.get_renderbuffer_parameter(WEBGL_RENDERBUFFER, WEBGL_RENDERBUFFER_WIDTH).int_value equals `0`
   - Expected: ctx.get_error() equals `WEBGL_INVALID_OPERATION`


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ctx = webgl_create_context(1, 320, 240)
val framebuffer = ctx.create_framebuffer()
val renderbuffer = ctx.create_renderbuffer()
expect(ctx.bind_renderbuffer(999, renderbuffer.id)).to_equal(false)
expect(ctx.get_error()).to_equal(WEBGL_INVALID_ENUM)
expect(ctx.bind_renderbuffer(WEBGL_RENDERBUFFER, 99)).to_equal(false)
expect(ctx.get_error()).to_equal(WEBGL_INVALID_VALUE)
expect(ctx.renderbuffer_storage(WEBGL_RENDERBUFFER, WEBGL_RGBA4, 4, 4)).to_equal(false)
expect(ctx.get_error()).to_equal(WEBGL_INVALID_OPERATION)
expect(ctx.bind_renderbuffer(WEBGL_RENDERBUFFER, renderbuffer.id)).to_equal(true)
expect(ctx.renderbuffer_storage(WEBGL_RENDERBUFFER, WEBGL_RGBA4, -1, 4)).to_equal(false)
expect(ctx.get_error()).to_equal(WEBGL_INVALID_VALUE)
expect(ctx.renderbuffer_storage(WEBGL_RENDERBUFFER, WEBGL_RGB565, 4, 4)).to_equal(true)
expect(ctx.bind_framebuffer(WEBGL_FRAMEBUFFER, framebuffer.id)).to_equal(true)
expect(ctx.framebuffer_renderbuffer(WEBGL_FRAMEBUFFER, WEBGL_DEPTH_ATTACHMENT, WEBGL_RENDERBUFFER, renderbuffer.id)).to_equal(true)
expect(ctx.check_framebuffer_status(WEBGL_FRAMEBUFFER)).to_equal(WEBGL_FRAMEBUFFER_INCOMPLETE_ATTACHMENT)
expect(ctx.framebuffer_renderbuffer(WEBGL_FRAMEBUFFER, 999, WEBGL_RENDERBUFFER, renderbuffer.id)).to_equal(false)
expect(ctx.get_error()).to_equal(WEBGL_INVALID_ENUM)
expect(ctx.get_renderbuffer_parameter(WEBGL_RENDERBUFFER, 999).int_value).to_equal(0)
expect(ctx.get_error()).to_equal(WEBGL_INVALID_ENUM)
expect(ctx.bind_renderbuffer(WEBGL_RENDERBUFFER, -1)).to_equal(true)
expect(ctx.get_renderbuffer_parameter(WEBGL_RENDERBUFFER, WEBGL_RENDERBUFFER_WIDTH).int_value).to_equal(0)
expect(ctx.get_error()).to_equal(WEBGL_INVALID_OPERATION)
```

</details>

#### blocks draws when the bound framebuffer is incomplete

1. var ctx =  linked program context
   - Expected: ctx.use_program(program.id) is true
   - Expected: ctx.bind_buffer(WEBGL_ARRAY_BUFFER, buffer.id) is true
   - Expected: ctx.buffer_data_size(WEBGL_ARRAY_BUFFER, 48, WEBGL_STATIC_DRAW) is true
   - Expected: ctx.enable_vertex_attrib_array(0) is true
   - Expected: ctx.vertex_attrib_pointer(0, 4, WEBGL_FLOAT, false, 0, 0) is true
   - Expected: ctx.bind_framebuffer(WEBGL_FRAMEBUFFER, framebuffer.id) is true
   - Expected: ctx.draw_arrays(WEBGL_TRIANGLES, 0, 3) is false
   - Expected: ctx.get_error() equals `WEBGL_INVALID_FRAMEBUFFER_OPERATION`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ctx = _linked_program_context()
val program = ctx.programs[0]
expect(ctx.use_program(program.id)).to_equal(true)
val buffer = ctx.create_buffer()
expect(ctx.bind_buffer(WEBGL_ARRAY_BUFFER, buffer.id)).to_equal(true)
expect(ctx.buffer_data_size(WEBGL_ARRAY_BUFFER, 48, WEBGL_STATIC_DRAW)).to_equal(true)
expect(ctx.enable_vertex_attrib_array(0)).to_equal(true)
expect(ctx.vertex_attrib_pointer(0, 4, WEBGL_FLOAT, false, 0, 0)).to_equal(true)
val framebuffer = ctx.create_framebuffer()
expect(ctx.bind_framebuffer(WEBGL_FRAMEBUFFER, framebuffer.id)).to_equal(true)
expect(ctx.draw_arrays(WEBGL_TRIANGLES, 0, 3)).to_equal(false)
expect(ctx.get_error()).to_equal(WEBGL_INVALID_FRAMEBUFFER_OPERATION)
```

</details>

### buffers attributes and draws

#### binds array buffers and records bind commands

1. var ctx = webgl create context
   - Expected: ctx.bind_buffer(WEBGL_ARRAY_BUFFER, buffer.id) is true
   - Expected: ctx.bound_array_buffer equals `buffer.id`
   - Expected: ctx.buffers[0].target equals `WEBGL_ARRAY_BUFFER`
   - Expected: ctx.render_commands.len() equals `1`
   - Expected: ctx.render_commands[0].kind equals `WEBGL_RENDER_COMMAND_BIND_BUFFER`
   - Expected: ctx.render_commands[0].target equals `WEBGL_ARRAY_BUFFER`
   - Expected: ctx.render_commands[0].buffer_id equals `buffer.id`
   - Expected: ctx.bind_buffer(WEBGL_ARRAY_BUFFER, -1) is true
   - Expected: ctx.bound_array_buffer equals `-1`
   - Expected: ctx.render_commands.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ctx = webgl_create_context(1, 320, 240)
val buffer = ctx.create_buffer()
expect(ctx.bind_buffer(WEBGL_ARRAY_BUFFER, buffer.id)).to_equal(true)
expect(ctx.bound_array_buffer).to_equal(buffer.id)
expect(ctx.buffers[0].target).to_equal(WEBGL_ARRAY_BUFFER)
expect(ctx.render_commands.len()).to_equal(1)
expect(ctx.render_commands[0].kind).to_equal(WEBGL_RENDER_COMMAND_BIND_BUFFER)
expect(ctx.render_commands[0].target).to_equal(WEBGL_ARRAY_BUFFER)
expect(ctx.render_commands[0].buffer_id).to_equal(buffer.id)
expect(ctx.bind_buffer(WEBGL_ARRAY_BUFFER, -1)).to_equal(true)
expect(ctx.bound_array_buffer).to_equal(-1)
expect(ctx.render_commands.len()).to_equal(1)
```

</details>

#### records buffer data metadata and validates target usage and size

1. var ctx = webgl create context
   - Expected: ctx.buffer_data_size(WEBGL_ARRAY_BUFFER, 12, WEBGL_STATIC_DRAW) is false
   - Expected: ctx.get_error() equals `WEBGL_INVALID_OPERATION`
   - Expected: ctx.bind_buffer(WEBGL_ARRAY_BUFFER, buffer.id) is true
   - Expected: ctx.buffer_data_size(WEBGL_ARRAY_BUFFER, -1, WEBGL_STATIC_DRAW) is false
   - Expected: ctx.get_error() equals `WEBGL_INVALID_VALUE`
   - Expected: ctx.buffer_data_size(WEBGL_ARRAY_BUFFER, 12, 999) is false
   - Expected: ctx.get_error() equals `WEBGL_INVALID_ENUM`
   - Expected: ctx.buffer_data_size(WEBGL_ARRAY_BUFFER, 12, WEBGL_DYNAMIC_DRAW) is true
   - Expected: ctx.buffers[0].byte_length equals `12`
   - Expected: ctx.buffers[0].usage equals `WEBGL_DYNAMIC_DRAW`
   - Expected: ctx.buffers[0].initialized is true
   - Expected: ctx.render_commands[1].kind equals `WEBGL_RENDER_COMMAND_BUFFER_DATA`
   - Expected: ctx.render_commands[1].target equals `WEBGL_ARRAY_BUFFER`
   - Expected: ctx.render_commands[1].buffer_id equals `12`
   - Expected: ctx.render_commands[1].mask equals `WEBGL_DYNAMIC_DRAW`
   - Expected: ctx.get_buffer_parameter(WEBGL_ARRAY_BUFFER, WEBGL_BUFFER_SIZE).int_value equals `12`
   - Expected: ctx.get_buffer_parameter(WEBGL_ARRAY_BUFFER, WEBGL_BUFFER_USAGE).int_value equals `WEBGL_DYNAMIC_DRAW`
   - Expected: ctx.get_buffer_parameter(WEBGL_ARRAY_BUFFER, 999).int_value equals `0`
   - Expected: ctx.get_error() equals `WEBGL_INVALID_ENUM`
   - Expected: ctx.bind_buffer(WEBGL_ARRAY_BUFFER, -1) is true
   - Expected: ctx.get_buffer_parameter(WEBGL_ARRAY_BUFFER, WEBGL_BUFFER_SIZE).int_value equals `0`
   - Expected: ctx.get_error() equals `WEBGL_INVALID_OPERATION`


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ctx = webgl_create_context(1, 320, 240)
val buffer = ctx.create_buffer()
expect(ctx.buffer_data_size(WEBGL_ARRAY_BUFFER, 12, WEBGL_STATIC_DRAW)).to_equal(false)
expect(ctx.get_error()).to_equal(WEBGL_INVALID_OPERATION)
expect(ctx.bind_buffer(WEBGL_ARRAY_BUFFER, buffer.id)).to_equal(true)
expect(ctx.buffer_data_size(WEBGL_ARRAY_BUFFER, -1, WEBGL_STATIC_DRAW)).to_equal(false)
expect(ctx.get_error()).to_equal(WEBGL_INVALID_VALUE)
expect(ctx.buffer_data_size(WEBGL_ARRAY_BUFFER, 12, 999)).to_equal(false)
expect(ctx.get_error()).to_equal(WEBGL_INVALID_ENUM)
expect(ctx.buffer_data_size(WEBGL_ARRAY_BUFFER, 12, WEBGL_DYNAMIC_DRAW)).to_equal(true)
expect(ctx.buffers[0].byte_length).to_equal(12)
expect(ctx.buffers[0].usage).to_equal(WEBGL_DYNAMIC_DRAW)
expect(ctx.buffers[0].initialized).to_equal(true)
expect(ctx.render_commands[1].kind).to_equal(WEBGL_RENDER_COMMAND_BUFFER_DATA)
expect(ctx.render_commands[1].target).to_equal(WEBGL_ARRAY_BUFFER)
expect(ctx.render_commands[1].buffer_id).to_equal(12)
expect(ctx.render_commands[1].mask).to_equal(WEBGL_DYNAMIC_DRAW)
expect(ctx.get_buffer_parameter(WEBGL_ARRAY_BUFFER, WEBGL_BUFFER_SIZE).int_value).to_equal(12)
expect(ctx.get_buffer_parameter(WEBGL_ARRAY_BUFFER, WEBGL_BUFFER_USAGE).int_value).to_equal(WEBGL_DYNAMIC_DRAW)
expect(ctx.get_buffer_parameter(WEBGL_ARRAY_BUFFER, 999).int_value).to_equal(0)
expect(ctx.get_error()).to_equal(WEBGL_INVALID_ENUM)
expect(ctx.bind_buffer(WEBGL_ARRAY_BUFFER, -1)).to_equal(true)
expect(ctx.get_buffer_parameter(WEBGL_ARRAY_BUFFER, WEBGL_BUFFER_SIZE).int_value).to_equal(0)
expect(ctx.get_error()).to_equal(WEBGL_INVALID_OPERATION)
```

</details>

#### configures vertex attributes from initialized array buffers

1. var ctx = webgl create context
   - Expected: ctx.vertex_attrib_pointer(0, 4, WEBGL_FLOAT, false, 0, 0) is false
   - Expected: ctx.get_error() equals `WEBGL_INVALID_OPERATION`
   - Expected: ctx.bind_buffer(WEBGL_ARRAY_BUFFER, buffer.id) is true
   - Expected: ctx.vertex_attrib_pointer(0, 4, WEBGL_FLOAT, false, 0, 0) is false
   - Expected: ctx.get_error() equals `WEBGL_INVALID_OPERATION`
   - Expected: ctx.buffer_data_size(WEBGL_ARRAY_BUFFER, 16, WEBGL_STATIC_DRAW) is true
   - Expected: ctx.enable_vertex_attrib_array(0) is true
   - Expected: ctx.vertex_attrib_pointer(0, 4, WEBGL_FLOAT, false, 0, 0) is true
   - Expected: ctx.vertex_attribs[0].enabled is true
   - Expected: ctx.vertex_attribs[0].size equals `4`
   - Expected: ctx.vertex_attribs[0].buffer_id equals `buffer.id`
   - Expected: ctx.render_commands[2].kind equals `WEBGL_RENDER_COMMAND_VERTEX_ATTRIB_ENABLE`
   - Expected: ctx.render_commands[2].x equals `0`
   - Expected: ctx.render_commands[2].mask equals `1`
   - Expected: ctx.render_commands[3].kind equals `WEBGL_RENDER_COMMAND_VERTEX_ATTRIB_POINTER`
   - Expected: ctx.render_commands[3].x equals `0`
   - Expected: ctx.render_commands[3].y equals `4`
   - Expected: ctx.render_commands[3].target equals `WEBGL_FLOAT`
   - Expected: ctx.render_commands[3].buffer_id equals `buffer.id`
   - Expected: ctx.vertex_attrib_pointer(1, 4, WEBGL_UNSIGNED_BYTE, true, 4, 0) is true
   - Expected: ctx.vertex_attribs[1].data_type equals `WEBGL_UNSIGNED_BYTE`
   - Expected: ctx.vertex_attribs[1].normalized is true
   - Expected: ctx.render_commands[4].target equals `WEBGL_UNSIGNED_BYTE`
   - Expected: ctx.vertex_attrib_pointer(2, 2, WEBGL_SHORT, false, 4, 2) is true
   - Expected: ctx.vertex_attribs[2].data_type equals `WEBGL_SHORT`
   - Expected: ctx.render_commands[5].target equals `WEBGL_SHORT`
   - Expected: ctx.vertex_attrib_pointer(16, 4, WEBGL_FLOAT, false, 0, 0) is false
   - Expected: ctx.get_error() equals `WEBGL_INVALID_VALUE`
   - Expected: ctx.vertex_attrib_pointer(0, 4, 999, false, 0, 0) is false
   - Expected: ctx.get_error() equals `WEBGL_INVALID_ENUM`
   - Expected: ctx.vertex_attrib_pointer(0, 4, WEBGL_FLOAT, false, 256, 0) is false
   - Expected: ctx.get_error() equals `WEBGL_INVALID_VALUE`
   - Expected: ctx.vertex_attrib_pointer(0, 4, WEBGL_FLOAT, false, 0, 2) is false
   - Expected: ctx.get_error() equals `WEBGL_INVALID_OPERATION`


<details>
<summary>Executable SSpec</summary>

Runnable source: 36 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ctx = webgl_create_context(1, 320, 240)
val buffer = ctx.create_buffer()
expect(ctx.vertex_attrib_pointer(0, 4, WEBGL_FLOAT, false, 0, 0)).to_equal(false)
expect(ctx.get_error()).to_equal(WEBGL_INVALID_OPERATION)
expect(ctx.bind_buffer(WEBGL_ARRAY_BUFFER, buffer.id)).to_equal(true)
expect(ctx.vertex_attrib_pointer(0, 4, WEBGL_FLOAT, false, 0, 0)).to_equal(false)
expect(ctx.get_error()).to_equal(WEBGL_INVALID_OPERATION)
expect(ctx.buffer_data_size(WEBGL_ARRAY_BUFFER, 16, WEBGL_STATIC_DRAW)).to_equal(true)
expect(ctx.enable_vertex_attrib_array(0)).to_equal(true)
expect(ctx.vertex_attrib_pointer(0, 4, WEBGL_FLOAT, false, 0, 0)).to_equal(true)
expect(ctx.vertex_attribs[0].enabled).to_equal(true)
expect(ctx.vertex_attribs[0].size).to_equal(4)
expect(ctx.vertex_attribs[0].buffer_id).to_equal(buffer.id)
expect(ctx.render_commands[2].kind).to_equal(WEBGL_RENDER_COMMAND_VERTEX_ATTRIB_ENABLE)
expect(ctx.render_commands[2].x).to_equal(0)
expect(ctx.render_commands[2].mask).to_equal(1)
expect(ctx.render_commands[3].kind).to_equal(WEBGL_RENDER_COMMAND_VERTEX_ATTRIB_POINTER)
expect(ctx.render_commands[3].x).to_equal(0)
expect(ctx.render_commands[3].y).to_equal(4)
expect(ctx.render_commands[3].target).to_equal(WEBGL_FLOAT)
expect(ctx.render_commands[3].buffer_id).to_equal(buffer.id)
expect(ctx.vertex_attrib_pointer(1, 4, WEBGL_UNSIGNED_BYTE, true, 4, 0)).to_equal(true)
expect(ctx.vertex_attribs[1].data_type).to_equal(WEBGL_UNSIGNED_BYTE)
expect(ctx.vertex_attribs[1].normalized).to_equal(true)
expect(ctx.render_commands[4].target).to_equal(WEBGL_UNSIGNED_BYTE)
expect(ctx.vertex_attrib_pointer(2, 2, WEBGL_SHORT, false, 4, 2)).to_equal(true)
expect(ctx.vertex_attribs[2].data_type).to_equal(WEBGL_SHORT)
expect(ctx.render_commands[5].target).to_equal(WEBGL_SHORT)
expect(ctx.vertex_attrib_pointer(16, 4, WEBGL_FLOAT, false, 0, 0)).to_equal(false)
expect(ctx.get_error()).to_equal(WEBGL_INVALID_VALUE)
expect(ctx.vertex_attrib_pointer(0, 4, 999, false, 0, 0)).to_equal(false)
expect(ctx.get_error()).to_equal(WEBGL_INVALID_ENUM)
expect(ctx.vertex_attrib_pointer(0, 4, WEBGL_FLOAT, false, 256, 0)).to_equal(false)
expect(ctx.get_error()).to_equal(WEBGL_INVALID_VALUE)
expect(ctx.vertex_attrib_pointer(0, 4, WEBGL_FLOAT, false, 0, 2)).to_equal(false)
expect(ctx.get_error()).to_equal(WEBGL_INVALID_OPERATION)
```

</details>

#### queries vertex attribute array state and disables attributes

1. var ctx = webgl create context
   - Expected: ctx.get_parameter(WEBGL_MAX_VERTEX_ATTRIBS).int_value equals `WEBGL_MAX_VERTEX_ATTRIBS`
   - Expected: ctx.get_vertex_attrib(0, WEBGL_VERTEX_ATTRIB_ARRAY_ENABLED).bool_value is false
   - Expected: ctx.get_vertex_attrib(0, WEBGL_VERTEX_ATTRIB_ARRAY_SIZE).int_value equals `4`
   - Expected: ctx.get_vertex_attrib(0, WEBGL_VERTEX_ATTRIB_ARRAY_BUFFER_BINDING).int_value equals `-1`
   - Expected: ctx.bind_buffer(WEBGL_ARRAY_BUFFER, buffer.id) is true
   - Expected: ctx.buffer_data_size(WEBGL_ARRAY_BUFFER, 64, WEBGL_STATIC_DRAW) is true
   - Expected: ctx.enable_vertex_attrib_array(0) is true
   - Expected: ctx.vertex_attrib_pointer(0, 3, WEBGL_FLOAT, true, 12, 4) is true
   - Expected: ctx.get_vertex_attrib(0, WEBGL_VERTEX_ATTRIB_ARRAY_ENABLED).bool_value is true
   - Expected: ctx.get_vertex_attrib(0, WEBGL_VERTEX_ATTRIB_ARRAY_SIZE).int_value equals `3`
   - Expected: ctx.get_vertex_attrib(0, WEBGL_VERTEX_ATTRIB_ARRAY_TYPE).int_value equals `WEBGL_FLOAT`
   - Expected: ctx.get_vertex_attrib(0, WEBGL_VERTEX_ATTRIB_ARRAY_NORMALIZED).bool_value is true
   - Expected: ctx.get_vertex_attrib(0, WEBGL_VERTEX_ATTRIB_ARRAY_STRIDE).int_value equals `12`
   - Expected: ctx.get_vertex_attrib(0, WEBGL_VERTEX_ATTRIB_ARRAY_POINTER).int_value equals `4`
   - Expected: ctx.get_vertex_attrib_offset(0, WEBGL_VERTEX_ATTRIB_ARRAY_POINTER) equals `4`
   - Expected: ctx.get_vertex_attrib(0, WEBGL_VERTEX_ATTRIB_ARRAY_BUFFER_BINDING).int_value equals `buffer.id`
   - Expected: ctx.disable_vertex_attrib_array(0) is true
   - Expected: ctx.get_vertex_attrib(0, WEBGL_VERTEX_ATTRIB_ARRAY_ENABLED).bool_value is false
   - Expected: ctx.render_commands[4].kind equals `WEBGL_RENDER_COMMAND_VERTEX_ATTRIB_ENABLE`
   - Expected: ctx.render_commands[4].x equals `0`
   - Expected: ctx.render_commands[4].mask equals `0`
   - Expected: ctx.get_vertex_attrib(0, WEBGL_VERTEX_ATTRIB_ARRAY_BUFFER_BINDING).int_value equals `buffer.id`


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ctx = webgl_create_context(1, 320, 240)
val buffer = ctx.create_buffer()
expect(ctx.get_parameter(WEBGL_MAX_VERTEX_ATTRIBS).int_value).to_equal(WEBGL_MAX_VERTEX_ATTRIBS)
expect(ctx.get_vertex_attrib(0, WEBGL_VERTEX_ATTRIB_ARRAY_ENABLED).bool_value).to_equal(false)
expect(ctx.get_vertex_attrib(0, WEBGL_VERTEX_ATTRIB_ARRAY_SIZE).int_value).to_equal(4)
expect(ctx.get_vertex_attrib(0, WEBGL_VERTEX_ATTRIB_ARRAY_BUFFER_BINDING).int_value).to_equal(-1)
expect(ctx.bind_buffer(WEBGL_ARRAY_BUFFER, buffer.id)).to_equal(true)
expect(ctx.buffer_data_size(WEBGL_ARRAY_BUFFER, 64, WEBGL_STATIC_DRAW)).to_equal(true)
expect(ctx.enable_vertex_attrib_array(0)).to_equal(true)
expect(ctx.vertex_attrib_pointer(0, 3, WEBGL_FLOAT, true, 12, 4)).to_equal(true)
expect(ctx.get_vertex_attrib(0, WEBGL_VERTEX_ATTRIB_ARRAY_ENABLED).bool_value).to_equal(true)
expect(ctx.get_vertex_attrib(0, WEBGL_VERTEX_ATTRIB_ARRAY_SIZE).int_value).to_equal(3)
expect(ctx.get_vertex_attrib(0, WEBGL_VERTEX_ATTRIB_ARRAY_TYPE).int_value).to_equal(WEBGL_FLOAT)
expect(ctx.get_vertex_attrib(0, WEBGL_VERTEX_ATTRIB_ARRAY_NORMALIZED).bool_value).to_equal(true)
expect(ctx.get_vertex_attrib(0, WEBGL_VERTEX_ATTRIB_ARRAY_STRIDE).int_value).to_equal(12)
expect(ctx.get_vertex_attrib(0, WEBGL_VERTEX_ATTRIB_ARRAY_POINTER).int_value).to_equal(4)
expect(ctx.get_vertex_attrib_offset(0, WEBGL_VERTEX_ATTRIB_ARRAY_POINTER)).to_equal(4)
expect(ctx.get_vertex_attrib(0, WEBGL_VERTEX_ATTRIB_ARRAY_BUFFER_BINDING).int_value).to_equal(buffer.id)
expect(ctx.disable_vertex_attrib_array(0)).to_equal(true)
expect(ctx.get_vertex_attrib(0, WEBGL_VERTEX_ATTRIB_ARRAY_ENABLED).bool_value).to_equal(false)
expect(ctx.render_commands[4].kind).to_equal(WEBGL_RENDER_COMMAND_VERTEX_ATTRIB_ENABLE)
expect(ctx.render_commands[4].x).to_equal(0)
expect(ctx.render_commands[4].mask).to_equal(0)
expect(ctx.get_vertex_attrib(0, WEBGL_VERTEX_ATTRIB_ARRAY_BUFFER_BINDING).int_value).to_equal(buffer.id)
```

</details>

#### validates vertex attribute query parameters

1. var ctx = webgl create context
   - Expected: ctx.disable_vertex_attrib_array(WEBGL_MAX_VERTEX_ATTRIBS) is false
   - Expected: ctx.get_error() equals `WEBGL_INVALID_VALUE`
   - Expected: ctx.get_vertex_attrib(-1, WEBGL_VERTEX_ATTRIB_ARRAY_ENABLED).int_value equals `0`
   - Expected: ctx.get_error() equals `WEBGL_INVALID_VALUE`
   - Expected: ctx.get_vertex_attrib(0, 999).int_value equals `0`
   - Expected: ctx.get_error() equals `WEBGL_INVALID_ENUM`
   - Expected: ctx.get_vertex_attrib_offset(WEBGL_MAX_VERTEX_ATTRIBS, WEBGL_VERTEX_ATTRIB_ARRAY_POINTER) equals `0`
   - Expected: ctx.get_error() equals `WEBGL_INVALID_VALUE`
   - Expected: ctx.get_vertex_attrib_offset(0, WEBGL_VERTEX_ATTRIB_ARRAY_SIZE) equals `0`
   - Expected: ctx.get_error() equals `WEBGL_INVALID_ENUM`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ctx = webgl_create_context(1, 320, 240)
expect(ctx.disable_vertex_attrib_array(WEBGL_MAX_VERTEX_ATTRIBS)).to_equal(false)
expect(ctx.get_error()).to_equal(WEBGL_INVALID_VALUE)
expect(ctx.get_vertex_attrib(-1, WEBGL_VERTEX_ATTRIB_ARRAY_ENABLED).int_value).to_equal(0)
expect(ctx.get_error()).to_equal(WEBGL_INVALID_VALUE)
expect(ctx.get_vertex_attrib(0, 999).int_value).to_equal(0)
expect(ctx.get_error()).to_equal(WEBGL_INVALID_ENUM)
expect(ctx.get_vertex_attrib_offset(WEBGL_MAX_VERTEX_ATTRIBS, WEBGL_VERTEX_ATTRIB_ARRAY_POINTER)).to_equal(0)
expect(ctx.get_error()).to_equal(WEBGL_INVALID_VALUE)
expect(ctx.get_vertex_attrib_offset(0, WEBGL_VERTEX_ATTRIB_ARRAY_SIZE)).to_equal(0)
expect(ctx.get_error()).to_equal(WEBGL_INVALID_ENUM)
```

</details>

#### tracks generic vertex attribute current values

1. var ctx = webgl create context
   - Expected: ctx.get_vertex_attrib(0, WEBGL_CURRENT_VERTEX_ATTRIB).float_values[0] equals `0.0`
   - Expected: ctx.get_vertex_attrib(0, WEBGL_CURRENT_VERTEX_ATTRIB).float_values[3] equals `1.0`
   - Expected: ctx.vertex_attrib_1f(0, 0.125) is true
   - Expected: ctx.get_vertex_attrib(0, WEBGL_CURRENT_VERTEX_ATTRIB).float_values[0] equals `0.125`
   - Expected: ctx.get_vertex_attrib(0, WEBGL_CURRENT_VERTEX_ATTRIB).float_values[3] equals `1.0`
   - Expected: ctx.vertex_attrib_2f(0, 0.25, 0.5) is true
   - Expected: ctx.get_vertex_attrib(0, WEBGL_CURRENT_VERTEX_ATTRIB).float_values[1] equals `0.5`
   - Expected: ctx.vertex_attrib_3f(0, 0.25, 0.5, 0.75) is true
   - Expected: ctx.get_vertex_attrib(0, WEBGL_CURRENT_VERTEX_ATTRIB).float_values[2] equals `0.75`
   - Expected: ctx.vertex_attrib_4f(0, 0.25, 0.5, 0.75, 1.0) is true
   - Expected: ctx.vertex_attrib_1fv(0, [0.375]) is true
   - Expected: ctx.get_vertex_attrib(0, WEBGL_CURRENT_VERTEX_ATTRIB).float_values[0] equals `0.375`
   - Expected: ctx.vertex_attrib_2fv(0, [0.25, 0.625]) is true
   - Expected: ctx.get_vertex_attrib(0, WEBGL_CURRENT_VERTEX_ATTRIB).float_values[1] equals `0.625`
   - Expected: ctx.vertex_attrib_3fv(0, [0.25, 0.5, 0.875]) is true
   - Expected: ctx.get_vertex_attrib(0, WEBGL_CURRENT_VERTEX_ATTRIB).float_values[2] equals `0.875`
   - Expected: ctx.vertex_attrib_4fv(0, [0.25, 0.5, 0.75, 1.0]) is true
   - Expected: current.float_values[0] equals `0.25`
   - Expected: current.float_values[1] equals `0.5`
   - Expected: current.float_values[2] equals `0.75`
   - Expected: current.float_values[3] equals `1.0`
   - Expected: ctx.render_commands[0].kind equals `WEBGL_RENDER_COMMAND_VERTEX_ATTRIB_4F`
   - Expected: ctx.render_commands[0].red equals `0.125`
   - Expected: ctx.render_commands[1].green equals `0.5`
   - Expected: ctx.render_commands[2].blue equals `0.75`
   - Expected: ctx.render_commands[3].x equals `0`
   - Expected: ctx.render_commands[3].red equals `0.25`
   - Expected: ctx.render_commands[3].alpha equals `1.0`
   - Expected: ctx.render_commands[7].kind equals `WEBGL_RENDER_COMMAND_VERTEX_ATTRIB_4F`
   - Expected: ctx.render_commands[7].blue equals `0.75`
   - Expected: ctx.vertex_attrib_4fv(0, [1.0, 2.0, 3.0]) is false
   - Expected: ctx.get_error() equals `WEBGL_INVALID_VALUE`
   - Expected: ctx.vertex_attrib_4f(WEBGL_MAX_VERTEX_ATTRIBS, 1.0, 1.0, 1.0, 1.0) is false
   - Expected: ctx.get_error() equals `WEBGL_INVALID_VALUE`


<details>
<summary>Executable SSpec</summary>

Runnable source: 36 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ctx = webgl_create_context(1, 320, 240)
expect(ctx.get_vertex_attrib(0, WEBGL_CURRENT_VERTEX_ATTRIB).float_values[0]).to_equal(0.0)
expect(ctx.get_vertex_attrib(0, WEBGL_CURRENT_VERTEX_ATTRIB).float_values[3]).to_equal(1.0)
expect(ctx.vertex_attrib_1f(0, 0.125)).to_equal(true)
expect(ctx.get_vertex_attrib(0, WEBGL_CURRENT_VERTEX_ATTRIB).float_values[0]).to_equal(0.125)
expect(ctx.get_vertex_attrib(0, WEBGL_CURRENT_VERTEX_ATTRIB).float_values[3]).to_equal(1.0)
expect(ctx.vertex_attrib_2f(0, 0.25, 0.5)).to_equal(true)
expect(ctx.get_vertex_attrib(0, WEBGL_CURRENT_VERTEX_ATTRIB).float_values[1]).to_equal(0.5)
expect(ctx.vertex_attrib_3f(0, 0.25, 0.5, 0.75)).to_equal(true)
expect(ctx.get_vertex_attrib(0, WEBGL_CURRENT_VERTEX_ATTRIB).float_values[2]).to_equal(0.75)
expect(ctx.vertex_attrib_4f(0, 0.25, 0.5, 0.75, 1.0)).to_equal(true)
expect(ctx.vertex_attrib_1fv(0, [0.375])).to_equal(true)
expect(ctx.get_vertex_attrib(0, WEBGL_CURRENT_VERTEX_ATTRIB).float_values[0]).to_equal(0.375)
expect(ctx.vertex_attrib_2fv(0, [0.25, 0.625])).to_equal(true)
expect(ctx.get_vertex_attrib(0, WEBGL_CURRENT_VERTEX_ATTRIB).float_values[1]).to_equal(0.625)
expect(ctx.vertex_attrib_3fv(0, [0.25, 0.5, 0.875])).to_equal(true)
expect(ctx.get_vertex_attrib(0, WEBGL_CURRENT_VERTEX_ATTRIB).float_values[2]).to_equal(0.875)
expect(ctx.vertex_attrib_4fv(0, [0.25, 0.5, 0.75, 1.0])).to_equal(true)
val current = ctx.get_vertex_attrib(0, WEBGL_CURRENT_VERTEX_ATTRIB)
expect(current.float_values[0]).to_equal(0.25)
expect(current.float_values[1]).to_equal(0.5)
expect(current.float_values[2]).to_equal(0.75)
expect(current.float_values[3]).to_equal(1.0)
expect(ctx.render_commands[0].kind).to_equal(WEBGL_RENDER_COMMAND_VERTEX_ATTRIB_4F)
expect(ctx.render_commands[0].red).to_equal(0.125)
expect(ctx.render_commands[1].green).to_equal(0.5)
expect(ctx.render_commands[2].blue).to_equal(0.75)
expect(ctx.render_commands[3].x).to_equal(0)
expect(ctx.render_commands[3].red).to_equal(0.25)
expect(ctx.render_commands[3].alpha).to_equal(1.0)
expect(ctx.render_commands[7].kind).to_equal(WEBGL_RENDER_COMMAND_VERTEX_ATTRIB_4F)
expect(ctx.render_commands[7].blue).to_equal(0.75)
expect(ctx.vertex_attrib_4fv(0, [1.0, 2.0, 3.0])).to_equal(false)
expect(ctx.get_error()).to_equal(WEBGL_INVALID_VALUE)
expect(ctx.vertex_attrib_4f(WEBGL_MAX_VERTEX_ATTRIBS, 1.0, 1.0, 1.0, 1.0)).to_equal(false)
expect(ctx.get_error()).to_equal(WEBGL_INVALID_VALUE)
```

</details>

#### records draw arrays after linked program and vertex source are ready

1. var ctx =  linked program context
   - Expected: ctx.draw_arrays(WEBGL_TRIANGLES, 0, 3) is false
   - Expected: ctx.get_error() equals `WEBGL_INVALID_OPERATION`
   - Expected: ctx.use_program(program.id) is true
   - Expected: ctx.bind_buffer(WEBGL_ARRAY_BUFFER, buffer.id) is true
   - Expected: ctx.buffer_data_size(WEBGL_ARRAY_BUFFER, 48, WEBGL_STATIC_DRAW) is true
   - Expected: ctx.enable_vertex_attrib_array(0) is true
   - Expected: ctx.vertex_attrib_pointer(0, 4, WEBGL_FLOAT, false, 0, 0) is true
   - Expected: ctx.draw_arrays(WEBGL_TRIANGLES, 0, 3) is true
   - Expected: ctx.draw_call_count equals `1`
   - Expected: ctx.last_draw_mode equals `WEBGL_TRIANGLES`
   - Expected: ctx.last_draw_count equals `3`
   - Expected: ctx.render_commands[5].kind equals `WEBGL_RENDER_COMMAND_DRAW_ARRAYS`
   - Expected: ctx.render_commands[5].mode equals `WEBGL_TRIANGLES`
   - Expected: ctx.render_commands[5].count equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ctx = _linked_program_context()
val program = ctx.programs[0]
expect(ctx.draw_arrays(WEBGL_TRIANGLES, 0, 3)).to_equal(false)
expect(ctx.get_error()).to_equal(WEBGL_INVALID_OPERATION)
expect(ctx.use_program(program.id)).to_equal(true)
val buffer = ctx.create_buffer()
expect(ctx.bind_buffer(WEBGL_ARRAY_BUFFER, buffer.id)).to_equal(true)
expect(ctx.buffer_data_size(WEBGL_ARRAY_BUFFER, 48, WEBGL_STATIC_DRAW)).to_equal(true)
expect(ctx.enable_vertex_attrib_array(0)).to_equal(true)
expect(ctx.vertex_attrib_pointer(0, 4, WEBGL_FLOAT, false, 0, 0)).to_equal(true)
expect(ctx.draw_arrays(WEBGL_TRIANGLES, 0, 3)).to_equal(true)
expect(ctx.draw_call_count).to_equal(1)
expect(ctx.last_draw_mode).to_equal(WEBGL_TRIANGLES)
expect(ctx.last_draw_count).to_equal(3)
expect(ctx.render_commands[5].kind).to_equal(WEBGL_RENDER_COMMAND_DRAW_ARRAYS)
expect(ctx.render_commands[5].mode).to_equal(WEBGL_TRIANGLES)
expect(ctx.render_commands[5].count).to_equal(3)
```

</details>

#### records indexed draws and gates unsigned int indices

1. var ctx =  linked program context
   - Expected: ctx.use_program(program.id) is true
   - Expected: ctx.bind_buffer(WEBGL_ARRAY_BUFFER, vertex_buffer.id) is true
   - Expected: ctx.buffer_data_size(WEBGL_ARRAY_BUFFER, 48, WEBGL_STATIC_DRAW) is true
   - Expected: ctx.enable_vertex_attrib_array(0) is true
   - Expected: ctx.vertex_attrib_pointer(0, 4, WEBGL_FLOAT, false, 0, 0) is true
   - Expected: ctx.bind_buffer(WEBGL_ELEMENT_ARRAY_BUFFER, index_buffer.id) is true
   - Expected: ctx.buffer_data_size(WEBGL_ELEMENT_ARRAY_BUFFER, 6, WEBGL_STATIC_DRAW) is true
   - Expected: ctx.draw_elements(WEBGL_TRIANGLES, 3, WEBGL_UNSIGNED_INT, 0) is false
   - Expected: ctx.get_error() equals `WEBGL_INVALID_ENUM`
   - Expected: ctx.draw_elements(WEBGL_LINES, 2, WEBGL_UNSIGNED_SHORT, 0) is true
   - Expected: ctx.indexed_draw_call_count equals `1`
   - Expected: ctx.render_commands[7].kind equals `WEBGL_RENDER_COMMAND_DRAW_ELEMENTS`
   - Expected: ctx.render_commands[7].element_type equals `WEBGL_UNSIGNED_SHORT`
   - Expected: ctx.get_extension("OES_element_index_uint").valid is true
   - Expected: ctx.draw_elements(WEBGL_TRIANGLES, 3, WEBGL_UNSIGNED_INT, 0) is true
   - Expected: ctx.indexed_draw_call_count equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ctx = _linked_program_context()
val program = ctx.programs[0]
expect(ctx.use_program(program.id)).to_equal(true)
val vertex_buffer = ctx.create_buffer()
expect(ctx.bind_buffer(WEBGL_ARRAY_BUFFER, vertex_buffer.id)).to_equal(true)
expect(ctx.buffer_data_size(WEBGL_ARRAY_BUFFER, 48, WEBGL_STATIC_DRAW)).to_equal(true)
expect(ctx.enable_vertex_attrib_array(0)).to_equal(true)
expect(ctx.vertex_attrib_pointer(0, 4, WEBGL_FLOAT, false, 0, 0)).to_equal(true)
val index_buffer = ctx.create_buffer()
expect(ctx.bind_buffer(WEBGL_ELEMENT_ARRAY_BUFFER, index_buffer.id)).to_equal(true)
expect(ctx.buffer_data_size(WEBGL_ELEMENT_ARRAY_BUFFER, 6, WEBGL_STATIC_DRAW)).to_equal(true)
expect(ctx.draw_elements(WEBGL_TRIANGLES, 3, WEBGL_UNSIGNED_INT, 0)).to_equal(false)
expect(ctx.get_error()).to_equal(WEBGL_INVALID_ENUM)
expect(ctx.draw_elements(WEBGL_LINES, 2, WEBGL_UNSIGNED_SHORT, 0)).to_equal(true)
expect(ctx.indexed_draw_call_count).to_equal(1)
expect(ctx.render_commands[7].kind).to_equal(WEBGL_RENDER_COMMAND_DRAW_ELEMENTS)
expect(ctx.render_commands[7].element_type).to_equal(WEBGL_UNSIGNED_SHORT)
expect(ctx.get_extension("OES_element_index_uint").valid).to_equal(true)
expect(ctx.draw_elements(WEBGL_TRIANGLES, 3, WEBGL_UNSIGNED_INT, 0)).to_equal(true)
expect(ctx.indexed_draw_call_count).to_equal(2)
```

</details>

### extensions

#### reports and enables supported extensions canonically

1. var ctx = webgl create context
   - Expected: ctx.supports_extension("OES_texture_float") is true
   - Expected: ctx.is_extension_enabled("OES_texture_float") is false
   - Expected: extension.valid is true
   - Expected: extension.name equals `OES_texture_float`
   - Expected: extension.enabled is true
   - Expected: ctx.is_extension_enabled("OES_texture_float") is true
   - Expected: ctx.enabled_extensions.len() equals `1`
   - Expected: again.valid is true
   - Expected: ctx.enabled_extensions.len() equals `1`
   - Expected: ctx.get_error() equals `WEBGL_NO_ERROR`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ctx = webgl_create_context(1, 320, 240)
expect(ctx.supports_extension("OES_texture_float")).to_equal(true)
expect(ctx.is_extension_enabled("OES_texture_float")).to_equal(false)
val extension = ctx.get_extension("OES_texture_float")
expect(extension.valid).to_equal(true)
expect(extension.name).to_equal("OES_texture_float")
expect(extension.enabled).to_equal(true)
expect(ctx.is_extension_enabled("OES_texture_float")).to_equal(true)
expect(ctx.enabled_extensions.len()).to_equal(1)
val again = ctx.get_extension("OES_texture_float")
expect(again.valid).to_equal(true)
expect(ctx.enabled_extensions.len()).to_equal(1)
expect(ctx.get_error()).to_equal(WEBGL_NO_ERROR)
```

</details>

#### keeps unsupported extensions unavailable without enabling state

1. var ctx = webgl create context
   - Expected: extension.valid is false
   - Expected: extension.enabled is false
   - Expected: ctx.supports_extension("EXT_color_buffer_float") is false
   - Expected: ctx.enabled_extensions.len() equals `0`
   - Expected: ctx.get_error() equals `WEBGL_NO_ERROR`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ctx = webgl_create_context(1, 320, 240)
val extension = ctx.get_extension("EXT_color_buffer_float")
expect(extension.valid).to_equal(false)
expect(extension.enabled).to_equal(false)
expect(ctx.supports_extension("EXT_color_buffer_float")).to_equal(false)
expect(ctx.enabled_extensions.len()).to_equal(0)
expect(ctx.get_error()).to_equal(WEBGL_NO_ERROR)
```

</details>

#### makes EXT_color_buffer_float available for WebGL2

1. var ctx = webgl create context
   - Expected: ctx.supports_extension("EXT_color_buffer_float") is true
   - Expected: extension.valid is true
   - Expected: extension.name equals `EXT_color_buffer_float`
   - Expected: ctx.is_extension_enabled("EXT_color_buffer_float") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ctx = webgl_create_context(2, 320, 240)
expect(ctx.supports_extension("EXT_color_buffer_float")).to_equal(true)
val extension = ctx.get_extension("EXT_color_buffer_float")
expect(extension.valid).to_equal(true)
expect(extension.name).to_equal("EXT_color_buffer_float")
expect(ctx.is_extension_enabled("EXT_color_buffer_float")).to_equal(true)
```

</details>

### shader and program lifecycle

#### compiles vertex and fragment shaders

1. var ctx = webgl create context
   - Expected: ctx.shader_source(vs.id, _vertex_glsl()) is true
   - Expected: ctx.shader_source(fs.id, _fragment_glsl()) is true
   - Expected: ctx.compile_shader(vs.id).compiled is true
   - Expected: ctx.compile_shader(fs.id).compiled is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ctx = webgl_create_context(1, 320, 240)
val vs = ctx.create_shader(WEBGL_VERTEX_SHADER)
val fs = ctx.create_shader(WEBGL_FRAGMENT_SHADER)
expect(ctx.shader_source(vs.id, _vertex_glsl())).to_equal(true)
expect(ctx.shader_source(fs.id, _fragment_glsl())).to_equal(true)
expect(ctx.compile_shader(vs.id).compiled).to_equal(true)
expect(ctx.compile_shader(fs.id).compiled).to_equal(true)
```

</details>

#### fails shader compile with info log

1. var ctx = webgl create context
   - Expected: ctx.shader_source(vs.id, "void main() { }") is true
   - Expected: compiled.compiled is false
   - Expected: compiled.info_log equals `vertex shader must write gl_Position`
   - Expected: ctx.get_error() equals `WEBGL_INVALID_OPERATION`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ctx = webgl_create_context(1, 320, 240)
val vs = ctx.create_shader(WEBGL_VERTEX_SHADER)
expect(ctx.shader_source(vs.id, "void main() { }")).to_equal(true)
val compiled = ctx.compile_shader(vs.id)
expect(compiled.compiled).to_equal(false)
expect(compiled.info_log).to_equal("vertex shader must write gl_Position")
expect(ctx.get_error()).to_equal(WEBGL_INVALID_OPERATION)
```

</details>

#### rejects GLSL ES 3.00 shaders in WebGL1

1. var ctx = webgl create context
   - Expected: ctx.shader_source(vs.id, _webgl2_vertex_glsl()) is true
   - Expected: compiled.compiled is false
   - Expected: compiled.info_log equals `GLSL ES 3.00 shaders require WebGL2`
   - Expected: ctx.get_error() equals `WEBGL_INVALID_OPERATION`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ctx = webgl_create_context(1, 320, 240)
val vs = ctx.create_shader(WEBGL_VERTEX_SHADER)
expect(ctx.shader_source(vs.id, _webgl2_vertex_glsl())).to_equal(true)
val compiled = ctx.compile_shader(vs.id)
expect(compiled.compiled).to_equal(false)
expect(compiled.info_log).to_equal("GLSL ES 3.00 shaders require WebGL2")
expect(ctx.get_error()).to_equal(WEBGL_INVALID_OPERATION)
```

</details>

#### accepts GLSL ES 3.00 shaders in WebGL2

1. var ctx = webgl create context
   - Expected: ctx.shader_source(vs.id, _webgl2_vertex_glsl()) is true
   - Expected: ctx.shader_source(fs.id, _webgl2_fragment_glsl()) is true
   - Expected: ctx.compile_shader(vs.id).compiled is true
   - Expected: ctx.compile_shader(fs.id).compiled is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ctx = webgl_create_context(2, 320, 240)
val vs = ctx.create_shader(WEBGL_VERTEX_SHADER)
val fs = ctx.create_shader(WEBGL_FRAGMENT_SHADER)
expect(ctx.shader_source(vs.id, _webgl2_vertex_glsl())).to_equal(true)
expect(ctx.shader_source(fs.id, _webgl2_fragment_glsl())).to_equal(true)
expect(ctx.compile_shader(vs.id).compiled).to_equal(true)
expect(ctx.compile_shader(fs.id).compiled).to_equal(true)
```

</details>

#### links and uses a compiled program

1. var ctx = webgl create context
   - Expected: ctx.shader_source(vs.id, _vertex_glsl()) is true
   - Expected: ctx.shader_source(fs.id, _fragment_glsl()) is true
   - Expected: ctx.compile_shader(vs.id).compiled is true
   - Expected: ctx.compile_shader(fs.id).compiled is true
   - Expected: ctx.attach_shader(program.id, vs.id) is true
   - Expected: ctx.attach_shader(program.id, fs.id) is true
   - Expected: linked.linked is true
   - Expected: ctx.use_program(program.id) is true
   - Expected: ctx.current_program_id equals `program.id`
   - Expected: ctx.get_parameter(WEBGL_CURRENT_PROGRAM).int_value equals `program.id`
   - Expected: ctx.render_commands[0].kind equals `WEBGL_RENDER_COMMAND_USE_PROGRAM`
   - Expected: ctx.render_commands[0].program_id equals `program.id`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ctx = webgl_create_context(1, 320, 240)
val vs = ctx.create_shader(WEBGL_VERTEX_SHADER)
val fs = ctx.create_shader(WEBGL_FRAGMENT_SHADER)
expect(ctx.shader_source(vs.id, _vertex_glsl())).to_equal(true)
expect(ctx.shader_source(fs.id, _fragment_glsl())).to_equal(true)
expect(ctx.compile_shader(vs.id).compiled).to_equal(true)
expect(ctx.compile_shader(fs.id).compiled).to_equal(true)
val program = ctx.create_program()
expect(ctx.attach_shader(program.id, vs.id)).to_equal(true)
expect(ctx.attach_shader(program.id, fs.id)).to_equal(true)
val linked = ctx.link_program(program.id)
expect(linked.linked).to_equal(true)
expect(ctx.use_program(program.id)).to_equal(true)
expect(ctx.current_program_id).to_equal(program.id)
expect(ctx.get_parameter(WEBGL_CURRENT_PROGRAM).int_value).to_equal(program.id)
expect(ctx.render_commands[0].kind).to_equal(WEBGL_RENDER_COMMAND_USE_PROGRAM)
expect(ctx.render_commands[0].program_id).to_equal(program.id)
```

</details>

#### reports shader parameters and info logs

1. var ctx = webgl create context
   - Expected: ctx.shader_source(vs.id, _vertex_glsl()) is true
   - Expected: ctx.compile_shader(vs.id).compiled is true
   - Expected: ctx.get_shader_source(vs.id) equals `_vertex_glsl()`
   - Expected: ctx.get_shader_parameter(vs.id, WEBGL_COMPILE_STATUS).bool_value is true
   - Expected: ctx.get_shader_parameter(vs.id, WEBGL_SHADER_TYPE).int_value equals `WEBGL_VERTEX_SHADER`
   - Expected: ctx.get_shader_parameter(vs.id, WEBGL_INFO_LOG_LENGTH).int_value equals `0`
   - Expected: ctx.get_shader_info_log(vs.id) equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ctx = webgl_create_context(1, 320, 240)
val vs = ctx.create_shader(WEBGL_VERTEX_SHADER)
expect(ctx.shader_source(vs.id, _vertex_glsl())).to_equal(true)
expect(ctx.compile_shader(vs.id).compiled).to_equal(true)
expect(ctx.get_shader_source(vs.id)).to_equal(_vertex_glsl())
expect(ctx.get_shader_parameter(vs.id, WEBGL_COMPILE_STATUS).bool_value).to_equal(true)
expect(ctx.get_shader_parameter(vs.id, WEBGL_SHADER_TYPE).int_value).to_equal(WEBGL_VERTEX_SHADER)
expect(ctx.get_shader_parameter(vs.id, WEBGL_INFO_LOG_LENGTH).int_value).to_equal(0)
expect(ctx.get_shader_info_log(vs.id)).to_equal("")
```

</details>

#### reports shader precision formats

1. var ctx = webgl create context
   - Expected: high_float.valid is true
   - Expected: high_float.range_min equals `127`
   - Expected: high_float.range_max equals `127`
   - Expected: high_float.precision equals `23`
   - Expected: medium_int.valid is true
   - Expected: medium_int.range_min equals `16`
   - Expected: medium_int.range_max equals `16`
   - Expected: medium_int.precision equals `0`
   - Expected: ctx.get_shader_precision_format(WEBGL_FRAGMENT_SHADER, WEBGL_LOW_FLOAT).precision equals `8`
   - Expected: ctx.get_shader_precision_format(WEBGL_VERTEX_SHADER, WEBGL_MEDIUM_FLOAT).precision equals `10`
   - Expected: ctx.get_shader_precision_format(WEBGL_VERTEX_SHADER, WEBGL_LOW_INT).range_min equals `8`
   - Expected: ctx.get_shader_precision_format(WEBGL_FRAGMENT_SHADER, WEBGL_HIGH_INT).range_max equals `31`
   - Expected: ctx.get_error() equals `WEBGL_NO_ERROR`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ctx = webgl_create_context(1, 320, 240)
val high_float = ctx.get_shader_precision_format(WEBGL_VERTEX_SHADER, WEBGL_HIGH_FLOAT)
expect(high_float.valid).to_equal(true)
expect(high_float.range_min).to_equal(127)
expect(high_float.range_max).to_equal(127)
expect(high_float.precision).to_equal(23)
val medium_int = ctx.get_shader_precision_format(WEBGL_FRAGMENT_SHADER, WEBGL_MEDIUM_INT)
expect(medium_int.valid).to_equal(true)
expect(medium_int.range_min).to_equal(16)
expect(medium_int.range_max).to_equal(16)
expect(medium_int.precision).to_equal(0)
expect(ctx.get_shader_precision_format(WEBGL_FRAGMENT_SHADER, WEBGL_LOW_FLOAT).precision).to_equal(8)
expect(ctx.get_shader_precision_format(WEBGL_VERTEX_SHADER, WEBGL_MEDIUM_FLOAT).precision).to_equal(10)
expect(ctx.get_shader_precision_format(WEBGL_VERTEX_SHADER, WEBGL_LOW_INT).range_min).to_equal(8)
expect(ctx.get_shader_precision_format(WEBGL_FRAGMENT_SHADER, WEBGL_HIGH_INT).range_max).to_equal(31)
expect(ctx.get_error()).to_equal(WEBGL_NO_ERROR)
```

</details>

#### validates shader precision format enums

1. var ctx = webgl create context
   - Expected: bad_shader.valid is false
   - Expected: bad_shader.error equals `invalid shader type`
   - Expected: ctx.get_error() equals `WEBGL_INVALID_ENUM`
   - Expected: bad_precision.valid is false
   - Expected: bad_precision.error equals `invalid precision type`
   - Expected: ctx.get_error() equals `WEBGL_INVALID_ENUM`
2. ctx lose context
   - Expected: lost.valid is false
   - Expected: lost.error equals `context lost`
   - Expected: ctx.get_error() equals `WEBGL_CONTEXT_LOST_WEBGL`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ctx = webgl_create_context(1, 320, 240)
val bad_shader = ctx.get_shader_precision_format(999, WEBGL_HIGH_FLOAT)
expect(bad_shader.valid).to_equal(false)
expect(bad_shader.error).to_equal("invalid shader type")
expect(ctx.get_error()).to_equal(WEBGL_INVALID_ENUM)
val bad_precision = ctx.get_shader_precision_format(WEBGL_VERTEX_SHADER, 999)
expect(bad_precision.valid).to_equal(false)
expect(bad_precision.error).to_equal("invalid precision type")
expect(ctx.get_error()).to_equal(WEBGL_INVALID_ENUM)
ctx.lose_context()
val lost = ctx.get_shader_precision_format(WEBGL_VERTEX_SHADER, WEBGL_HIGH_FLOAT)
expect(lost.valid).to_equal(false)
expect(lost.error).to_equal("context lost")
expect(ctx.get_error()).to_equal(WEBGL_CONTEXT_LOST_WEBGL)
```

</details>

#### deletes shaders and rejects later shader commands

1. var ctx = webgl create context
   - Expected: ctx.is_shader(vs.id) is true
   - Expected: ctx.is_shader(99) is false
   - Expected: ctx.shader_source(vs.id, _vertex_glsl()) is true
   - Expected: ctx.compile_shader(vs.id).compiled is true
   - Expected: ctx.delete_shader(vs.id) is true
   - Expected: ctx.is_shader(vs.id) is false
   - Expected: ctx.get_shader_parameter(vs.id, WEBGL_DELETE_STATUS).bool_value is true
   - Expected: ctx.get_shader_source(vs.id) equals ``
   - Expected: ctx.get_error() equals `WEBGL_INVALID_VALUE`
   - Expected: ctx.shader_source(vs.id, _vertex_glsl()) is false
   - Expected: ctx.get_error() equals `WEBGL_INVALID_VALUE`
   - Expected: ctx.compile_shader(vs.id).valid is false
   - Expected: ctx.get_error() equals `WEBGL_INVALID_VALUE`
   - Expected: ctx.attach_shader(program.id, vs.id) is false
   - Expected: ctx.get_error() equals `WEBGL_INVALID_VALUE`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ctx = webgl_create_context(1, 320, 240)
val vs = ctx.create_shader(WEBGL_VERTEX_SHADER)
val program = ctx.create_program()
expect(ctx.is_shader(vs.id)).to_equal(true)
expect(ctx.is_shader(99)).to_equal(false)
expect(ctx.shader_source(vs.id, _vertex_glsl())).to_equal(true)
expect(ctx.compile_shader(vs.id).compiled).to_equal(true)
expect(ctx.delete_shader(vs.id)).to_equal(true)
expect(ctx.is_shader(vs.id)).to_equal(false)
expect(ctx.get_shader_parameter(vs.id, WEBGL_DELETE_STATUS).bool_value).to_equal(true)
expect(ctx.get_shader_source(vs.id)).to_equal("")
expect(ctx.get_error()).to_equal(WEBGL_INVALID_VALUE)
expect(ctx.shader_source(vs.id, _vertex_glsl())).to_equal(false)
expect(ctx.get_error()).to_equal(WEBGL_INVALID_VALUE)
expect(ctx.compile_shader(vs.id).valid).to_equal(false)
expect(ctx.get_error()).to_equal(WEBGL_INVALID_VALUE)
expect(ctx.attach_shader(program.id, vs.id)).to_equal(false)
expect(ctx.get_error()).to_equal(WEBGL_INVALID_VALUE)
```

</details>

#### reports program reflection parameters

1. var ctx =  linked program context
   - Expected: ctx.get_program_parameter(program.id, WEBGL_LINK_STATUS).bool_value is true
   - Expected: ctx.get_program_parameter(program.id, WEBGL_VALIDATE_STATUS).bool_value is true
   - Expected: ctx.get_program_parameter(program.id, WEBGL_ATTACHED_SHADERS).int_value equals `2`
   - Expected: ctx.get_program_parameter(program.id, WEBGL_ACTIVE_ATTRIBUTES).int_value equals `1`
   - Expected: ctx.get_program_parameter(program.id, WEBGL_ACTIVE_UNIFORMS).int_value equals `2`
   - Expected: program.active_attribs[0].name equals `position`
   - Expected: program.active_attribs[0].data_type equals `WEBGL_FLOAT_VEC4`
   - Expected: program.active_uniforms[1].name equals `diffuse`
   - Expected: program.active_uniforms[1].data_type equals `WEBGL_SAMPLER_2D`
   - Expected: ctx.get_program_info_log(program.id) equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ctx = _linked_program_context()
val program = ctx.programs[0]
expect(ctx.get_program_parameter(program.id, WEBGL_LINK_STATUS).bool_value).to_equal(true)
expect(ctx.get_program_parameter(program.id, WEBGL_VALIDATE_STATUS).bool_value).to_equal(true)
expect(ctx.get_program_parameter(program.id, WEBGL_ATTACHED_SHADERS).int_value).to_equal(2)
expect(ctx.get_program_parameter(program.id, WEBGL_ACTIVE_ATTRIBUTES).int_value).to_equal(1)
expect(ctx.get_program_parameter(program.id, WEBGL_ACTIVE_UNIFORMS).int_value).to_equal(2)
expect(program.active_attribs[0].name).to_equal("position")
expect(program.active_attribs[0].data_type).to_equal(WEBGL_FLOAT_VEC4)
expect(program.active_uniforms[1].name).to_equal("diffuse")
expect(program.active_uniforms[1].data_type).to_equal(WEBGL_SAMPLER_2D)
expect(ctx.get_program_info_log(program.id)).to_equal("")
```

</details>

#### validates linked programs explicitly

1. var ctx =  linked program context
   - Expected: ctx.validate_program(program.id) is true
   - Expected: ctx.get_program_parameter(program.id, WEBGL_VALIDATE_STATUS).bool_value is true
   - Expected: ctx.get_program_info_log(program.id) equals ``
   - Expected: ctx.get_error() equals `WEBGL_NO_ERROR`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ctx = _linked_program_context()
val program = ctx.programs[0]
expect(ctx.validate_program(program.id)).to_equal(true)
expect(ctx.get_program_parameter(program.id, WEBGL_VALIDATE_STATUS).bool_value).to_equal(true)
expect(ctx.get_program_info_log(program.id)).to_equal("")
expect(ctx.get_error()).to_equal(WEBGL_NO_ERROR)
```

</details>

#### reports failed explicit program validation

1. var ctx = webgl create context
   - Expected: ctx.validate_program(program.id) is false
   - Expected: ctx.get_program_parameter(program.id, WEBGL_VALIDATE_STATUS).bool_value is false
   - Expected: ctx.get_program_info_log(program.id) equals `linked program required`
   - Expected: ctx.get_error() equals `WEBGL_NO_ERROR`
   - Expected: ctx.validate_program(99) is false
   - Expected: ctx.get_error() equals `WEBGL_INVALID_VALUE`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ctx = webgl_create_context(1, 320, 240)
val program = ctx.create_program()
expect(ctx.validate_program(program.id)).to_equal(false)
expect(ctx.get_program_parameter(program.id, WEBGL_VALIDATE_STATUS).bool_value).to_equal(false)
expect(ctx.get_program_info_log(program.id)).to_equal("linked program required")
expect(ctx.get_error()).to_equal(WEBGL_NO_ERROR)
expect(ctx.validate_program(99)).to_equal(false)
expect(ctx.get_error()).to_equal(WEBGL_INVALID_VALUE)
```

</details>

#### detaches shaders and updates attached shader count

1. var ctx = webgl create context
   - Expected: ctx.shader_source(vs.id, _vertex_glsl()) is true
   - Expected: ctx.shader_source(fs.id, _fragment_glsl()) is true
   - Expected: ctx.compile_shader(vs.id).compiled is true
   - Expected: ctx.compile_shader(fs.id).compiled is true
   - Expected: ctx.attach_shader(program.id, vs.id) is true
   - Expected: ctx.attach_shader(program.id, fs.id) is true
   - Expected: ctx.get_program_parameter(program.id, WEBGL_ATTACHED_SHADERS).int_value equals `2`
   - Expected: ctx.detach_shader(program.id, fs.id) is true
   - Expected: ctx.get_program_parameter(program.id, WEBGL_ATTACHED_SHADERS).int_value equals `1`
   - Expected: ctx.detach_shader(program.id, fs.id) is false
   - Expected: ctx.get_error() equals `WEBGL_INVALID_OPERATION`
   - Expected: linked.linked is false
   - Expected: linked.info_log equals `compiled vertex and fragment shaders required`
   - Expected: ctx.get_error() equals `WEBGL_INVALID_OPERATION`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ctx = webgl_create_context(1, 320, 240)
val vs = ctx.create_shader(WEBGL_VERTEX_SHADER)
val fs = ctx.create_shader(WEBGL_FRAGMENT_SHADER)
expect(ctx.shader_source(vs.id, _vertex_glsl())).to_equal(true)
expect(ctx.shader_source(fs.id, _fragment_glsl())).to_equal(true)
expect(ctx.compile_shader(vs.id).compiled).to_equal(true)
expect(ctx.compile_shader(fs.id).compiled).to_equal(true)
val program = ctx.create_program()
expect(ctx.attach_shader(program.id, vs.id)).to_equal(true)
expect(ctx.attach_shader(program.id, fs.id)).to_equal(true)
expect(ctx.get_program_parameter(program.id, WEBGL_ATTACHED_SHADERS).int_value).to_equal(2)
expect(ctx.detach_shader(program.id, fs.id)).to_equal(true)
expect(ctx.get_program_parameter(program.id, WEBGL_ATTACHED_SHADERS).int_value).to_equal(1)
expect(ctx.detach_shader(program.id, fs.id)).to_equal(false)
expect(ctx.get_error()).to_equal(WEBGL_INVALID_OPERATION)
val linked = ctx.link_program(program.id)
expect(linked.linked).to_equal(false)
expect(linked.info_log).to_equal("compiled vertex and fragment shaders required")
expect(ctx.get_error()).to_equal(WEBGL_INVALID_OPERATION)
```

</details>

#### returns attached shader handles including deleted attachments

1. var ctx = webgl create context
   - Expected: ctx.attach_shader(program.id, vs.id) is true
   - Expected: ctx.attach_shader(program.id, fs.id) is true
   - Expected: attached.len() equals `2`
   - Expected: attached[0].id equals `vs.id`
   - Expected: attached[1].id equals `fs.id`
   - Expected: ctx.delete_shader(fs.id) is true
   - Expected: after_delete.len() equals `2`
   - Expected: after_delete[1].valid is false
   - Expected: ctx.detach_shader(program.id, fs.id) is true
   - Expected: after_detach.len() equals `1`
   - Expected: after_detach[0].id equals `vs.id`
   - Expected: ctx.get_attached_shaders(99).len() equals `0`
   - Expected: ctx.get_error() equals `WEBGL_INVALID_VALUE`


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ctx = webgl_create_context(1, 320, 240)
val vs = ctx.create_shader(WEBGL_VERTEX_SHADER)
val fs = ctx.create_shader(WEBGL_FRAGMENT_SHADER)
val program = ctx.create_program()
expect(ctx.attach_shader(program.id, vs.id)).to_equal(true)
expect(ctx.attach_shader(program.id, fs.id)).to_equal(true)
val attached = ctx.get_attached_shaders(program.id)
expect(attached.len()).to_equal(2)
expect(attached[0].id).to_equal(vs.id)
expect(attached[1].id).to_equal(fs.id)
expect(ctx.delete_shader(fs.id)).to_equal(true)
val after_delete = ctx.get_attached_shaders(program.id)
expect(after_delete.len()).to_equal(2)
expect(after_delete[1].valid).to_equal(false)
expect(ctx.detach_shader(program.id, fs.id)).to_equal(true)
val after_detach = ctx.get_attached_shaders(program.id)
expect(after_detach.len()).to_equal(1)
expect(after_detach[0].id).to_equal(vs.id)
expect(ctx.get_attached_shaders(99).len()).to_equal(0)
expect(ctx.get_error()).to_equal(WEBGL_INVALID_VALUE)
```

</details>

#### deletes programs and clears current program state

1. var ctx =  uniform program context
   - Expected: ctx.is_program(program.id) is true
   - Expected: ctx.is_program(99) is false
   - Expected: ctx.uniform_4f(tint, 0.25, 0.5, 0.75, 1.0) is true
   - Expected: ctx.delete_program(program.id) is true
   - Expected: ctx.is_program(program.id) is false
   - Expected: ctx.get_parameter(WEBGL_CURRENT_PROGRAM).int_value equals `-1`
   - Expected: ctx.get_program_parameter(program.id, WEBGL_DELETE_STATUS).bool_value is true
   - Expected: ctx.get_program_parameter(program.id, WEBGL_LINK_STATUS).bool_value is false
   - Expected: ctx.use_program(program.id) is false
   - Expected: ctx.get_error() equals `WEBGL_INVALID_VALUE`
   - Expected: ctx.uniform_values.len() equals `0`
   - Expected: ctx.attach_shader(program.id, shader.id) is false
   - Expected: ctx.get_error() equals `WEBGL_INVALID_VALUE`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ctx = _uniform_program_context()
val program = ctx.programs[0]
val tint = ctx.get_uniform_location(program.id, "tint")
expect(ctx.is_program(program.id)).to_equal(true)
expect(ctx.is_program(99)).to_equal(false)
expect(ctx.uniform_4f(tint, 0.25, 0.5, 0.75, 1.0)).to_equal(true)
expect(ctx.delete_program(program.id)).to_equal(true)
expect(ctx.is_program(program.id)).to_equal(false)
expect(ctx.get_parameter(WEBGL_CURRENT_PROGRAM).int_value).to_equal(-1)
expect(ctx.get_program_parameter(program.id, WEBGL_DELETE_STATUS).bool_value).to_equal(true)
expect(ctx.get_program_parameter(program.id, WEBGL_LINK_STATUS).bool_value).to_equal(false)
expect(ctx.use_program(program.id)).to_equal(false)
expect(ctx.get_error()).to_equal(WEBGL_INVALID_VALUE)
expect(ctx.uniform_values.len()).to_equal(0)
val shader = ctx.create_shader(WEBGL_VERTEX_SHADER)
expect(ctx.attach_shader(program.id, shader.id)).to_equal(false)
expect(ctx.get_error()).to_equal(WEBGL_INVALID_VALUE)
```

</details>

#### returns active attribute and uniform records by index

1. var ctx =  linked program context
   - Expected: attrib.name equals `position`
   - Expected: attrib.data_type equals `WEBGL_FLOAT_VEC4`
   - Expected: attrib.location equals `0`
   - Expected: tint.name equals `tint`
   - Expected: diffuse.name equals `diffuse`
   - Expected: diffuse.data_type equals `WEBGL_SAMPLER_2D`
   - Expected: ctx.get_error() equals `WEBGL_NO_ERROR`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ctx = _linked_program_context()
val program = ctx.programs[0]
val attrib = ctx.get_active_attrib(program.id, 0)
expect(attrib.name).to_equal("position")
expect(attrib.data_type).to_equal(WEBGL_FLOAT_VEC4)
expect(attrib.location).to_equal(0)
val tint = ctx.get_active_uniform(program.id, 0)
val diffuse = ctx.get_active_uniform(program.id, 1)
expect(tint.name).to_equal("tint")
expect(diffuse.name).to_equal("diffuse")
expect(diffuse.data_type).to_equal(WEBGL_SAMPLER_2D)
expect(ctx.get_error()).to_equal(WEBGL_NO_ERROR)
```

</details>

#### resolves active attribute and uniform locations

1. var ctx =  linked program context
   - Expected: ctx.get_attrib_location(program.id, "position") equals `0`
   - Expected: ctx.get_uniform_location(program.id, "tint") equals `0`
   - Expected: ctx.get_uniform_location(program.id, "diffuse") equals `1`
   - Expected: ctx.get_attrib_location(program.id, "missing") equals `-1`
   - Expected: ctx.get_uniform_location(program.id, "missing") equals `-1`
   - Expected: ctx.get_error() equals `WEBGL_NO_ERROR`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ctx = _linked_program_context()
val program = ctx.programs[0]
expect(ctx.get_attrib_location(program.id, "position")).to_equal(0)
expect(ctx.get_uniform_location(program.id, "tint")).to_equal(0)
expect(ctx.get_uniform_location(program.id, "diffuse")).to_equal(1)
expect(ctx.get_attrib_location(program.id, "missing")).to_equal(-1)
expect(ctx.get_uniform_location(program.id, "missing")).to_equal(-1)
expect(ctx.get_error()).to_equal(WEBGL_NO_ERROR)
```

</details>

#### stores current program uniform values by location

1. var ctx =  uniform program context
   - Expected: ctx.uniform_1f(opacity, 0.75) is true
   - Expected: ctx.uniform_4f(tint, 0.1, 0.2, 0.3, 1.0) is true
   - Expected: ctx.uniform_1i(diffuse, 2) is true
   - Expected: ctx.uniform_matrix4fv(model, false, matrix) is true
   - Expected: ctx.uniform_1fv(opacity, [0.875]) is true
   - Expected: ctx.uniform_values.len() equals `4`
   - Expected: ctx.uniform_values[0].data_type equals `WEBGL_FLOAT`
   - Expected: ctx.uniform_values[0].float_values[0] equals `0.875`
   - Expected: ctx.get_uniform(program.id, opacity).float_value equals `0.875`
   - Expected: ctx.uniform_values[2].data_type equals `WEBGL_SAMPLER_2D`
   - Expected: ctx.uniform_values[2].int_value equals `2`
   - Expected: ctx.get_uniform(program.id, diffuse).int_value equals `2`
   - Expected: ctx.uniform_values[3].data_type equals `WEBGL_FLOAT_MAT4`
   - Expected: ctx.uniform_values[3].float_values[12] equals `2.0`
   - Expected: ctx.get_uniform(program.id, model).float_values[12] equals `2.0`
   - Expected: ctx.render_commands[1].kind equals `WEBGL_RENDER_COMMAND_UNIFORM_1F`
   - Expected: ctx.render_commands[1].program_id equals `program.id`
   - Expected: ctx.render_commands[1].x equals `opacity`
   - Expected: ctx.render_commands[1].red equals `0.75`
   - Expected: ctx.render_commands[2].kind equals `WEBGL_RENDER_COMMAND_UNIFORM_4F`
   - Expected: ctx.render_commands[2].x equals `tint`
   - Expected: ctx.render_commands[2].red equals `0.1`
   - Expected: ctx.render_commands[2].alpha equals `1.0`
   - Expected: ctx.render_commands[3].kind equals `WEBGL_RENDER_COMMAND_UNIFORM_1I`
   - Expected: ctx.render_commands[3].x equals `diffuse`
   - Expected: ctx.render_commands[3].mask equals `2`
   - Expected: ctx.render_commands[4].kind equals `WEBGL_RENDER_COMMAND_UNIFORM_MATRIX4FV`
   - Expected: ctx.render_commands[4].x equals `model`
   - Expected: ctx.render_commands[4].float_values.len() equals `16`
   - Expected: ctx.render_commands[4].float_values[12] equals `2.0`
   - Expected: ctx.render_commands[5].kind equals `WEBGL_RENDER_COMMAND_UNIFORM_1FV`
   - Expected: ctx.render_commands[5].float_values[0] equals `0.875`
   - Expected: ctx.uniform_1fv(opacity, [0.1, 0.2]) is false
   - Expected: ctx.get_error() equals `WEBGL_INVALID_VALUE`
   - Expected: ctx.uniform_4f(tint, 0.9, 0.8, 0.7, 1.0) is true
   - Expected: ctx.uniform_values.len() equals `4`
   - Expected: ctx.uniform_values[1].float_values[0] equals `0.9`
   - Expected: ctx.render_commands[6].kind equals `WEBGL_RENDER_COMMAND_UNIFORM_4F`
   - Expected: ctx.render_commands[6].red equals `0.9`
   - Expected: ctx.get_error() equals `WEBGL_NO_ERROR`


<details>
<summary>Executable SSpec</summary>

Runnable source: 47 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ctx = _uniform_program_context()
val program = ctx.programs[0]
val model = ctx.get_uniform_location(program.id, "model")
val opacity = ctx.get_uniform_location(program.id, "opacity")
val tint = ctx.get_uniform_location(program.id, "tint")
val diffuse = ctx.get_uniform_location(program.id, "diffuse")
expect(ctx.uniform_1f(opacity, 0.75)).to_equal(true)
expect(ctx.uniform_4f(tint, 0.1, 0.2, 0.3, 1.0)).to_equal(true)
expect(ctx.uniform_1i(diffuse, 2)).to_equal(true)
val matrix: [f64] = [1.0, 0.0, 0.0, 0.0, 0.0, 1.0, 0.0, 0.0, 0.0, 0.0, 1.0, 0.0, 2.0, 3.0, 4.0, 1.0]
expect(ctx.uniform_matrix4fv(model, false, matrix)).to_equal(true)
expect(ctx.uniform_1fv(opacity, [0.875])).to_equal(true)
expect(ctx.uniform_values.len()).to_equal(4)
expect(ctx.uniform_values[0].data_type).to_equal(WEBGL_FLOAT)
expect(ctx.uniform_values[0].float_values[0]).to_equal(0.875)
expect(ctx.get_uniform(program.id, opacity).float_value).to_equal(0.875)
expect(ctx.uniform_values[2].data_type).to_equal(WEBGL_SAMPLER_2D)
expect(ctx.uniform_values[2].int_value).to_equal(2)
expect(ctx.get_uniform(program.id, diffuse).int_value).to_equal(2)
expect(ctx.uniform_values[3].data_type).to_equal(WEBGL_FLOAT_MAT4)
expect(ctx.uniform_values[3].float_values[12]).to_equal(2.0)
expect(ctx.get_uniform(program.id, model).float_values[12]).to_equal(2.0)
expect(ctx.render_commands[1].kind).to_equal(WEBGL_RENDER_COMMAND_UNIFORM_1F)
expect(ctx.render_commands[1].program_id).to_equal(program.id)
expect(ctx.render_commands[1].x).to_equal(opacity)
expect(ctx.render_commands[1].red).to_equal(0.75)
expect(ctx.render_commands[2].kind).to_equal(WEBGL_RENDER_COMMAND_UNIFORM_4F)
expect(ctx.render_commands[2].x).to_equal(tint)
expect(ctx.render_commands[2].red).to_equal(0.1)
expect(ctx.render_commands[2].alpha).to_equal(1.0)
expect(ctx.render_commands[3].kind).to_equal(WEBGL_RENDER_COMMAND_UNIFORM_1I)
expect(ctx.render_commands[3].x).to_equal(diffuse)
expect(ctx.render_commands[3].mask).to_equal(2)
expect(ctx.render_commands[4].kind).to_equal(WEBGL_RENDER_COMMAND_UNIFORM_MATRIX4FV)
expect(ctx.render_commands[4].x).to_equal(model)
expect(ctx.render_commands[4].float_values.len()).to_equal(16)
expect(ctx.render_commands[4].float_values[12]).to_equal(2.0)
expect(ctx.render_commands[5].kind).to_equal(WEBGL_RENDER_COMMAND_UNIFORM_1FV)
expect(ctx.render_commands[5].float_values[0]).to_equal(0.875)
expect(ctx.uniform_1fv(opacity, [0.1, 0.2])).to_equal(false)
expect(ctx.get_error()).to_equal(WEBGL_INVALID_VALUE)
expect(ctx.uniform_4f(tint, 0.9, 0.8, 0.7, 1.0)).to_equal(true)
expect(ctx.uniform_values.len()).to_equal(4)
expect(ctx.uniform_values[1].float_values[0]).to_equal(0.9)
expect(ctx.render_commands[6].kind).to_equal(WEBGL_RENDER_COMMAND_UNIFORM_4F)
expect(ctx.render_commands[6].red).to_equal(0.9)
expect(ctx.get_error()).to_equal(WEBGL_NO_ERROR)
```

</details>

#### stores vec2 and vec3 uniform values by location

1. var ctx =  vector uniform program context
   - Expected: ctx.get_active_uniform(program.id, 0).data_type equals `WEBGL_FLOAT_VEC2`
   - Expected: ctx.get_active_uniform(program.id, 1).data_type equals `WEBGL_FLOAT_VEC3`
   - Expected: ctx.uniform_2f(uv_scale, 2.0, 4.0) is true
   - Expected: ctx.uniform_3f(normal_bias, 0.1, 0.2, 0.3) is true
   - Expected: ctx.uniform_values.len() equals `2`
   - Expected: ctx.uniform_values[0].data_type equals `WEBGL_FLOAT_VEC2`
   - Expected: ctx.uniform_values[0].float_values[1] equals `4.0`
   - Expected: ctx.uniform_values[1].data_type equals `WEBGL_FLOAT_VEC3`
   - Expected: ctx.uniform_values[1].float_values[2] equals `0.3`
   - Expected: ctx.render_commands[1].kind equals `WEBGL_RENDER_COMMAND_UNIFORM_2F`
   - Expected: ctx.render_commands[1].x equals `uv_scale`
   - Expected: ctx.render_commands[1].green equals `4.0`
   - Expected: ctx.render_commands[2].kind equals `WEBGL_RENDER_COMMAND_UNIFORM_3F`
   - Expected: ctx.render_commands[2].x equals `normal_bias`
   - Expected: ctx.render_commands[2].blue equals `0.3`
   - Expected: ctx.uniform_2f(tint, 1.0, 1.0) is false
   - Expected: ctx.get_error() equals `WEBGL_INVALID_OPERATION`


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ctx = _vector_uniform_program_context()
val program = ctx.programs[0]
val uv_scale = ctx.get_uniform_location(program.id, "uvScale")
val normal_bias = ctx.get_uniform_location(program.id, "normalBias")
val tint = ctx.get_uniform_location(program.id, "tint")
expect(ctx.get_active_uniform(program.id, 0).data_type).to_equal(WEBGL_FLOAT_VEC2)
expect(ctx.get_active_uniform(program.id, 1).data_type).to_equal(WEBGL_FLOAT_VEC3)
expect(ctx.uniform_2f(uv_scale, 2.0, 4.0)).to_equal(true)
expect(ctx.uniform_3f(normal_bias, 0.1, 0.2, 0.3)).to_equal(true)
expect(ctx.uniform_values.len()).to_equal(2)
expect(ctx.uniform_values[0].data_type).to_equal(WEBGL_FLOAT_VEC2)
expect(ctx.uniform_values[0].float_values[1]).to_equal(4.0)
expect(ctx.uniform_values[1].data_type).to_equal(WEBGL_FLOAT_VEC3)
expect(ctx.uniform_values[1].float_values[2]).to_equal(0.3)
expect(ctx.render_commands[1].kind).to_equal(WEBGL_RENDER_COMMAND_UNIFORM_2F)
expect(ctx.render_commands[1].x).to_equal(uv_scale)
expect(ctx.render_commands[1].green).to_equal(4.0)
expect(ctx.render_commands[2].kind).to_equal(WEBGL_RENDER_COMMAND_UNIFORM_3F)
expect(ctx.render_commands[2].x).to_equal(normal_bias)
expect(ctx.render_commands[2].blue).to_equal(0.3)
expect(ctx.uniform_2f(tint, 1.0, 1.0)).to_equal(false)
expect(ctx.get_error()).to_equal(WEBGL_INVALID_OPERATION)
```

</details>

#### stores integer uniform values by location

1. var ctx =  integer uniform program context
   - Expected: ctx.get_active_uniform(program.id, 0).data_type equals `WEBGL_INT`
   - Expected: ctx.get_active_uniform(program.id, 1).data_type equals `WEBGL_INT_VEC2`
   - Expected: ctx.get_active_uniform(program.id, 2).data_type equals `WEBGL_INT_VEC3`
   - Expected: ctx.get_active_uniform(program.id, 3).data_type equals `WEBGL_INT_VEC4`
   - Expected: ctx.get_uniform(program.id, layer).int_value equals `0`
   - Expected: ctx.get_uniform(program.id, flags).int_values[1] equals `0`
   - Expected: ctx.uniform_1i(layer, 3) is true
   - Expected: ctx.uniform_2i(flags, 4, 5) is true
   - Expected: ctx.uniform_3i(range, 6, 7, 8) is true
   - Expected: ctx.uniform_4i(mask, 9, 10, 11, 12) is true
   - Expected: ctx.uniform_values.len() equals `4`
   - Expected: ctx.get_uniform(program.id, layer).int_value equals `3`
   - Expected: ctx.get_uniform(program.id, flags).int_values[1] equals `5`
   - Expected: ctx.get_uniform(program.id, range).int_values[2] equals `8`
   - Expected: ctx.get_uniform(program.id, mask).int_values[3] equals `12`
   - Expected: ctx.render_commands[1].kind equals `WEBGL_RENDER_COMMAND_UNIFORM_1I`
   - Expected: ctx.render_commands[1].mask equals `3`
   - Expected: ctx.render_commands[2].kind equals `WEBGL_RENDER_COMMAND_UNIFORM_2I`
   - Expected: ctx.render_commands[2].width equals `5`
   - Expected: ctx.render_commands[3].kind equals `WEBGL_RENDER_COMMAND_UNIFORM_3I`
   - Expected: ctx.render_commands[3].height equals `8`
   - Expected: ctx.render_commands[4].kind equals `WEBGL_RENDER_COMMAND_UNIFORM_4I`
   - Expected: ctx.render_commands[4].mask equals `12`
   - Expected: ctx.uniform_2i(layer, 1, 2) is false
   - Expected: ctx.get_error() equals `WEBGL_INVALID_OPERATION`


<details>
<summary>Executable SSpec</summary>

Runnable source: 31 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ctx = _integer_uniform_program_context()
val program = ctx.programs[0]
val layer = ctx.get_uniform_location(program.id, "layer")
val flags = ctx.get_uniform_location(program.id, "flags")
val range = ctx.get_uniform_location(program.id, "range")
val mask = ctx.get_uniform_location(program.id, "mask")
expect(ctx.get_active_uniform(program.id, 0).data_type).to_equal(WEBGL_INT)
expect(ctx.get_active_uniform(program.id, 1).data_type).to_equal(WEBGL_INT_VEC2)
expect(ctx.get_active_uniform(program.id, 2).data_type).to_equal(WEBGL_INT_VEC3)
expect(ctx.get_active_uniform(program.id, 3).data_type).to_equal(WEBGL_INT_VEC4)
expect(ctx.get_uniform(program.id, layer).int_value).to_equal(0)
expect(ctx.get_uniform(program.id, flags).int_values[1]).to_equal(0)
expect(ctx.uniform_1i(layer, 3)).to_equal(true)
expect(ctx.uniform_2i(flags, 4, 5)).to_equal(true)
expect(ctx.uniform_3i(range, 6, 7, 8)).to_equal(true)
expect(ctx.uniform_4i(mask, 9, 10, 11, 12)).to_equal(true)
expect(ctx.uniform_values.len()).to_equal(4)
expect(ctx.get_uniform(program.id, layer).int_value).to_equal(3)
expect(ctx.get_uniform(program.id, flags).int_values[1]).to_equal(5)
expect(ctx.get_uniform(program.id, range).int_values[2]).to_equal(8)
expect(ctx.get_uniform(program.id, mask).int_values[3]).to_equal(12)
expect(ctx.render_commands[1].kind).to_equal(WEBGL_RENDER_COMMAND_UNIFORM_1I)
expect(ctx.render_commands[1].mask).to_equal(3)
expect(ctx.render_commands[2].kind).to_equal(WEBGL_RENDER_COMMAND_UNIFORM_2I)
expect(ctx.render_commands[2].width).to_equal(5)
expect(ctx.render_commands[3].kind).to_equal(WEBGL_RENDER_COMMAND_UNIFORM_3I)
expect(ctx.render_commands[3].height).to_equal(8)
expect(ctx.render_commands[4].kind).to_equal(WEBGL_RENDER_COMMAND_UNIFORM_4I)
expect(ctx.render_commands[4].mask).to_equal(12)
expect(ctx.uniform_2i(layer, 1, 2)).to_equal(false)
expect(ctx.get_error()).to_equal(WEBGL_INVALID_OPERATION)
```

</details>

#### stores vector uniform array values by location

1. var ctx =  vector uniform program context
   - Expected: ctx.uniform_2fv(uv_scale, [3.0, 5.0]) is true
   - Expected: ctx.uniform_3fv(normal_bias, [0.4, 0.5, 0.6]) is true
   - Expected: ctx.uniform_4fv(tint, [0.1, 0.2, 0.3, 1.0]) is true
   - Expected: ctx.uniform_values.len() equals `3`
   - Expected: ctx.uniform_values[0].float_values[1] equals `5.0`
   - Expected: ctx.uniform_values[1].float_values[2] equals `0.6`
   - Expected: ctx.uniform_values[2].float_values[3] equals `1.0`
   - Expected: ctx.render_commands[1].kind equals `WEBGL_RENDER_COMMAND_UNIFORM_2FV`
   - Expected: ctx.render_commands[1].float_values[1] equals `5.0`
   - Expected: ctx.render_commands[2].kind equals `WEBGL_RENDER_COMMAND_UNIFORM_3FV`
   - Expected: ctx.render_commands[2].float_values[2] equals `0.6`
   - Expected: ctx.render_commands[3].kind equals `WEBGL_RENDER_COMMAND_UNIFORM_4FV`
   - Expected: ctx.render_commands[3].float_values[3] equals `1.0`
   - Expected: ctx.uniform_3fv(normal_bias, [0.1]) is false
   - Expected: ctx.get_error() equals `WEBGL_INVALID_VALUE`


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ctx = _vector_uniform_program_context()
val program = ctx.programs[0]
val uv_scale = ctx.get_uniform_location(program.id, "uvScale")
val normal_bias = ctx.get_uniform_location(program.id, "normalBias")
val tint = ctx.get_uniform_location(program.id, "tint")
expect(ctx.uniform_2fv(uv_scale, [3.0, 5.0])).to_equal(true)
expect(ctx.uniform_3fv(normal_bias, [0.4, 0.5, 0.6])).to_equal(true)
expect(ctx.uniform_4fv(tint, [0.1, 0.2, 0.3, 1.0])).to_equal(true)
expect(ctx.uniform_values.len()).to_equal(3)
expect(ctx.uniform_values[0].float_values[1]).to_equal(5.0)
expect(ctx.uniform_values[1].float_values[2]).to_equal(0.6)
expect(ctx.uniform_values[2].float_values[3]).to_equal(1.0)
expect(ctx.render_commands[1].kind).to_equal(WEBGL_RENDER_COMMAND_UNIFORM_2FV)
expect(ctx.render_commands[1].float_values[1]).to_equal(5.0)
expect(ctx.render_commands[2].kind).to_equal(WEBGL_RENDER_COMMAND_UNIFORM_3FV)
expect(ctx.render_commands[2].float_values[2]).to_equal(0.6)
expect(ctx.render_commands[3].kind).to_equal(WEBGL_RENDER_COMMAND_UNIFORM_4FV)
expect(ctx.render_commands[3].float_values[3]).to_equal(1.0)
expect(ctx.uniform_3fv(normal_bias, [0.1])).to_equal(false)
expect(ctx.get_error()).to_equal(WEBGL_INVALID_VALUE)
```

</details>

#### returns default and stored uniform values

1. var ctx =  vector uniform program context
   - Expected: ctx.get_uniform(program.id, uv_scale).float_values[0] equals `0.0`
   - Expected: ctx.get_uniform(program.id, uv_scale).float_values[1] equals `0.0`
   - Expected: ctx.uniform_2f(uv_scale, 2.0, 4.0) is true
   - Expected: ctx.uniform_4fv(tint, [0.1, 0.2, 0.3, 1.0]) is true
   - Expected: ctx.get_uniform(program.id, uv_scale).float_values[1] equals `4.0`
   - Expected: ctx.get_uniform(program.id, tint).float_values[3] equals `1.0`
   - Expected: ctx.get_uniform(program.id, -1).int_value equals `0`
   - Expected: ctx.get_error() equals `WEBGL_INVALID_VALUE`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ctx = _vector_uniform_program_context()
val program = ctx.programs[0]
val uv_scale = ctx.get_uniform_location(program.id, "uvScale")
val tint = ctx.get_uniform_location(program.id, "tint")
expect(ctx.get_uniform(program.id, uv_scale).float_values[0]).to_equal(0.0)
expect(ctx.get_uniform(program.id, uv_scale).float_values[1]).to_equal(0.0)
expect(ctx.uniform_2f(uv_scale, 2.0, 4.0)).to_equal(true)
expect(ctx.uniform_4fv(tint, [0.1, 0.2, 0.3, 1.0])).to_equal(true)
expect(ctx.get_uniform(program.id, uv_scale).float_values[1]).to_equal(4.0)
expect(ctx.get_uniform(program.id, tint).float_values[3]).to_equal(1.0)
expect(ctx.get_uniform(program.id, -1).int_value).to_equal(0)
expect(ctx.get_error()).to_equal(WEBGL_INVALID_VALUE)
```

</details>

<details>
<summary>Advanced: validates uniform setter type and matrix arguments</summary>

#### validates uniform setter type and matrix arguments

1. var ctx =  uniform program context
   - Expected: ctx.uniform_1f(-1, 1.0) is true
   - Expected: ctx.render_commands.len() equals `command_count`
   - Expected: ctx.uniform_1i(opacity, 1) is false
   - Expected: ctx.render_commands.len() equals `command_count`
   - Expected: ctx.get_error() equals `WEBGL_INVALID_OPERATION`
   - Expected: ctx.uniform_4f(opacity, 1.0, 1.0, 1.0, 1.0) is false
   - Expected: ctx.get_error() equals `WEBGL_INVALID_OPERATION`
   - Expected: ctx.uniform_matrix4fv(model, true, []) is false
   - Expected: ctx.get_error() equals `WEBGL_INVALID_VALUE`
   - Expected: ctx.uniform_matrix4fv(model, false, [1.0]) is false
   - Expected: ctx.get_error() equals `WEBGL_INVALID_VALUE`
   - Expected: ctx.uniform_matrix4fv(tint, false, [1.0]) is false
   - Expected: ctx.get_error() equals `WEBGL_INVALID_OPERATION`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ctx = _uniform_program_context()
val program = ctx.programs[0]
val model = ctx.get_uniform_location(program.id, "model")
val opacity = ctx.get_uniform_location(program.id, "opacity")
val tint = ctx.get_uniform_location(program.id, "tint")
val command_count = ctx.render_commands.len()
expect(ctx.uniform_1f(-1, 1.0)).to_equal(true)
expect(ctx.render_commands.len()).to_equal(command_count)
expect(ctx.uniform_1i(opacity, 1)).to_equal(false)
expect(ctx.render_commands.len()).to_equal(command_count)
expect(ctx.get_error()).to_equal(WEBGL_INVALID_OPERATION)
expect(ctx.uniform_4f(opacity, 1.0, 1.0, 1.0, 1.0)).to_equal(false)
expect(ctx.get_error()).to_equal(WEBGL_INVALID_OPERATION)
expect(ctx.uniform_matrix4fv(model, true, [])).to_equal(false)
expect(ctx.get_error()).to_equal(WEBGL_INVALID_VALUE)
expect(ctx.uniform_matrix4fv(model, false, [1.0])).to_equal(false)
expect(ctx.get_error()).to_equal(WEBGL_INVALID_VALUE)
expect(ctx.uniform_matrix4fv(tint, false, [1.0])).to_equal(false)
expect(ctx.get_error()).to_equal(WEBGL_INVALID_OPERATION)
```

</details>


</details>

#### validates reflection query errors

1. var ctx = webgl create context
   - Expected: ctx.get_shader_parameter(99, WEBGL_COMPILE_STATUS).bool_value is false
   - Expected: ctx.get_error() equals `WEBGL_INVALID_VALUE`
   - Expected: ctx.get_shader_parameter(shader.id, 999).bool_value is false
   - Expected: ctx.get_error() equals `WEBGL_INVALID_ENUM`
   - Expected: ctx.get_program_parameter(program.id, 999).bool_value is false
   - Expected: ctx.get_error() equals `WEBGL_INVALID_ENUM`
   - Expected: ctx.get_attrib_location(program.id, "position") equals `-1`
   - Expected: ctx.get_error() equals `WEBGL_INVALID_OPERATION`
   - Expected: ctx.get_active_attrib(program.id, 0).name equals ``
   - Expected: ctx.get_error() equals `WEBGL_INVALID_OPERATION`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ctx = webgl_create_context(1, 320, 240)
val program = ctx.create_program()
expect(ctx.get_shader_parameter(99, WEBGL_COMPILE_STATUS).bool_value).to_equal(false)
expect(ctx.get_error()).to_equal(WEBGL_INVALID_VALUE)
val shader = ctx.create_shader(WEBGL_VERTEX_SHADER)
expect(ctx.get_shader_parameter(shader.id, 999).bool_value).to_equal(false)
expect(ctx.get_error()).to_equal(WEBGL_INVALID_ENUM)
expect(ctx.get_program_parameter(program.id, 999).bool_value).to_equal(false)
expect(ctx.get_error()).to_equal(WEBGL_INVALID_ENUM)
expect(ctx.get_attrib_location(program.id, "position")).to_equal(-1)
expect(ctx.get_error()).to_equal(WEBGL_INVALID_OPERATION)
expect(ctx.get_active_attrib(program.id, 0).name).to_equal("")
expect(ctx.get_error()).to_equal(WEBGL_INVALID_OPERATION)
```

</details>

#### validates active reflection index bounds

1. var ctx =  linked program context
   - Expected: ctx.get_active_attrib(program.id, 1).name equals ``
   - Expected: ctx.get_error() equals `WEBGL_INVALID_VALUE`
   - Expected: ctx.get_active_uniform(program.id, -1).name equals ``
   - Expected: ctx.get_error() equals `WEBGL_INVALID_VALUE`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ctx = _linked_program_context()
val program = ctx.programs[0]
expect(ctx.get_active_attrib(program.id, 1).name).to_equal("")
expect(ctx.get_error()).to_equal(WEBGL_INVALID_VALUE)
expect(ctx.get_active_uniform(program.id, -1).name).to_equal("")
expect(ctx.get_error()).to_equal(WEBGL_INVALID_VALUE)
```

</details>

#### returns reflection defaults while context is lost

1. var ctx =  linked program context
2. ctx lose context
   - Expected: ctx.is_shader(shader.id) is false
   - Expected: ctx.is_program(program.id) is false
   - Expected: ctx.get_shader_parameter(shader.id, WEBGL_COMPILE_STATUS).bool_value is false
   - Expected: ctx.get_shader_source(shader.id) equals ``
   - Expected: ctx.get_shader_info_log(shader.id) equals ``
   - Expected: ctx.get_program_parameter(program.id, WEBGL_LINK_STATUS).bool_value is false
   - Expected: ctx.get_program_info_log(program.id) equals ``
   - Expected: ctx.get_attrib_location(program.id, "position") equals `-1`
   - Expected: ctx.get_uniform_location(program.id, "tint") equals `-1`
   - Expected: ctx.get_active_attrib(program.id, 0).name equals ``
   - Expected: ctx.get_active_uniform(program.id, 0).name equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ctx = _linked_program_context()
val program = ctx.programs[0]
val shader = ctx.shaders[0]
ctx.lose_context()
expect(ctx.is_shader(shader.id)).to_equal(false)
expect(ctx.is_program(program.id)).to_equal(false)
expect(ctx.get_shader_parameter(shader.id, WEBGL_COMPILE_STATUS).bool_value).to_equal(false)
expect(ctx.get_shader_source(shader.id)).to_equal("")
expect(ctx.get_shader_info_log(shader.id)).to_equal("")
expect(ctx.get_program_parameter(program.id, WEBGL_LINK_STATUS).bool_value).to_equal(false)
expect(ctx.get_program_info_log(program.id)).to_equal("")
expect(ctx.get_attrib_location(program.id, "position")).to_equal(-1)
expect(ctx.get_uniform_location(program.id, "tint")).to_equal(-1)
expect(ctx.get_active_attrib(program.id, 0).name).to_equal("")
expect(ctx.get_active_uniform(program.id, 0).name).to_equal("")
```

</details>

#### rejects program link without both shader stages

1. var ctx = webgl create context
   - Expected: ctx.shader_source(vs.id, _vertex_glsl()) is true
   - Expected: ctx.compile_shader(vs.id).compiled is true
   - Expected: ctx.attach_shader(program.id, vs.id) is true
   - Expected: linked.linked is false
   - Expected: linked.info_log equals `compiled vertex and fragment shaders required`
   - Expected: ctx.use_program(program.id) is false
   - Expected: ctx.get_error() equals `WEBGL_INVALID_OPERATION`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ctx = webgl_create_context(1, 320, 240)
val vs = ctx.create_shader(WEBGL_VERTEX_SHADER)
expect(ctx.shader_source(vs.id, _vertex_glsl())).to_equal(true)
expect(ctx.compile_shader(vs.id).compiled).to_equal(true)
val program = ctx.create_program()
expect(ctx.attach_shader(program.id, vs.id)).to_equal(true)
val linked = ctx.link_program(program.id)
expect(linked.linked).to_equal(false)
expect(linked.info_log).to_equal("compiled vertex and fragment shaders required")
expect(ctx.use_program(program.id)).to_equal(false)
expect(ctx.get_error()).to_equal(WEBGL_INVALID_OPERATION)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/feature/web_platform/webgl/webgl_context_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Browser WebGL context
- context names
- error state and context loss
- resources
- render command recording
- render state
- textures
- framebuffers
- buffers attributes and draws
- extensions
- shader and program lifecycle

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 97 |
| Active scenarios | 97 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

# Webgl Render Commands Specification

> <details>

<!-- sdn-diagram:id=webgl_render_commands_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=webgl_render_commands_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

webgl_render_commands_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=webgl_render_commands_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Webgl Render Commands Specification

## Scenarios

### Browser WebGL render command IR

#### records viewport dimensions as flat command data

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val command = webgl_render_command_viewport(4, 8, 640, 480)
expect(command.kind).to_equal(WEBGL_RENDER_COMMAND_VIEWPORT)
expect(command.x).to_equal(4)
expect(command.y).to_equal(8)
expect(command.width).to_equal(640)
expect(command.height).to_equal(480)
expect(command.program_id).to_equal(-1)
```

</details>

#### records clear color channels

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val command = webgl_render_command_clear_color(0.25, 0.5, 0.75, 1.0)
expect(command.kind).to_equal(WEBGL_RENDER_COMMAND_CLEAR_COLOR)
expect(command.red).to_equal(0.25)
expect(command.green).to_equal(0.5)
expect(command.blue).to_equal(0.75)
expect(command.alpha).to_equal(1.0)
expect(command.mask).to_equal(0)
```

</details>

#### records clear mask

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val command = webgl_render_command_clear(16640)
expect(command.kind).to_equal(WEBGL_RENDER_COMMAND_CLEAR)
expect(command.mask).to_equal(16640)
```

</details>

#### records program binding

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val command = webgl_render_command_use_program(7)
expect(command.kind).to_equal(WEBGL_RENDER_COMMAND_USE_PROGRAM)
expect(command.program_id).to_equal(7)
expect(command.buffer_id).to_equal(-1)
expect(command.texture_id).to_equal(-1)
```

</details>

#### records uniform setter payloads

<details>
<summary>Executable SSpec</summary>

Runnable source: 46 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sampler = webgl_render_command_uniform_1i(7, 2, 3)
expect(sampler.kind).to_equal(WEBGL_RENDER_COMMAND_UNIFORM_1I)
expect(sampler.program_id).to_equal(7)
expect(sampler.x).to_equal(2)
expect(sampler.mask).to_equal(3)
val flags = webgl_render_command_uniform_2i(7, 11, 4, 5)
expect(flags.kind).to_equal(WEBGL_RENDER_COMMAND_UNIFORM_2I)
expect(flags.x).to_equal(11)
expect(flags.y).to_equal(4)
expect(flags.width).to_equal(5)
val range = webgl_render_command_uniform_3i(7, 12, 6, 7, 8)
expect(range.kind).to_equal(WEBGL_RENDER_COMMAND_UNIFORM_3I)
expect(range.height).to_equal(8)
val mask = webgl_render_command_uniform_4i(7, 13, 9, 10, 11, 12)
expect(mask.kind).to_equal(WEBGL_RENDER_COMMAND_UNIFORM_4I)
expect(mask.mask).to_equal(12)
val uv_scale = webgl_render_command_uniform_2f(7, 3, 2.0, 4.0)
expect(uv_scale.kind).to_equal(WEBGL_RENDER_COMMAND_UNIFORM_2F)
expect(uv_scale.x).to_equal(3)
expect(uv_scale.green).to_equal(4.0)
val normal_bias = webgl_render_command_uniform_3f(7, 6, 0.1, 0.2, 0.3)
expect(normal_bias.kind).to_equal(WEBGL_RENDER_COMMAND_UNIFORM_3F)
expect(normal_bias.x).to_equal(6)
expect(normal_bias.blue).to_equal(0.3)
val tint = webgl_render_command_uniform_4f(7, 4, 0.1, 0.2, 0.3, 1.0)
expect(tint.kind).to_equal(WEBGL_RENDER_COMMAND_UNIFORM_4F)
expect(tint.x).to_equal(4)
expect(tint.red).to_equal(0.1)
expect(tint.alpha).to_equal(1.0)
val opacity_values = webgl_render_command_uniform_1fv(7, 3, [0.75])
expect(opacity_values.kind).to_equal(WEBGL_RENDER_COMMAND_UNIFORM_1FV)
expect(opacity_values.float_values[0]).to_equal(0.75)
val uv_values = webgl_render_command_uniform_2fv(7, 8, [2.0, 4.0])
expect(uv_values.kind).to_equal(WEBGL_RENDER_COMMAND_UNIFORM_2FV)
expect(uv_values.float_values[1]).to_equal(4.0)
val normal_values = webgl_render_command_uniform_3fv(7, 9, [0.1, 0.2, 0.3])
expect(normal_values.kind).to_equal(WEBGL_RENDER_COMMAND_UNIFORM_3FV)
expect(normal_values.float_values[2]).to_equal(0.3)
val tint_values = webgl_render_command_uniform_4fv(7, 10, [0.1, 0.2, 0.3, 1.0])
expect(tint_values.kind).to_equal(WEBGL_RENDER_COMMAND_UNIFORM_4FV)
expect(tint_values.float_values[3]).to_equal(1.0)
val matrix_values: [f64] = [1.0, 0.0, 0.0, 0.0]
val matrix = webgl_render_command_uniform_matrix4fv(7, 5, matrix_values)
expect(matrix.kind).to_equal(WEBGL_RENDER_COMMAND_UNIFORM_MATRIX4FV)
expect(matrix.float_values.len()).to_equal(4)
expect(matrix.float_values[0]).to_equal(1.0)
```

</details>

#### records read pixels requests

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val command = webgl_render_command_read_pixels(1, 2, 3, 4, 6408, 5121)
expect(command.kind).to_equal(WEBGL_RENDER_COMMAND_READ_PIXELS)
expect(command.x).to_equal(1)
expect(command.y).to_equal(2)
expect(command.width).to_equal(3)
expect(command.height).to_equal(4)
expect(command.target).to_equal(6408)
expect(command.element_type).to_equal(5121)
```

</details>

#### records buffer and texture bindings

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val buffer = webgl_render_command_bind_buffer(34962, 3)
val texture = webgl_render_command_bind_texture(3553, 9)
expect(buffer.kind).to_equal(WEBGL_RENDER_COMMAND_BIND_BUFFER)
expect(buffer.target).to_equal(34962)
expect(buffer.buffer_id).to_equal(3)
expect(texture.kind).to_equal(WEBGL_RENDER_COMMAND_BIND_TEXTURE)
expect(texture.target).to_equal(3553)
expect(texture.texture_id).to_equal(9)
```

</details>

#### records generic vertex attribute values

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val command = webgl_render_command_vertex_attrib_4f(2, 0.25, 0.5, 0.75, 1.0)
expect(command.kind).to_equal(WEBGL_RENDER_COMMAND_VERTEX_ATTRIB_4F)
expect(command.x).to_equal(2)
expect(command.red).to_equal(0.25)
expect(command.green).to_equal(0.5)
expect(command.blue).to_equal(0.75)
expect(command.alpha).to_equal(1.0)
```

</details>

#### records draw arrays parameters

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val command = webgl_render_command_draw_arrays(4, 2, 6)
expect(command.kind).to_equal(WEBGL_RENDER_COMMAND_DRAW_ARRAYS)
expect(command.mode).to_equal(4)
expect(command.first).to_equal(2)
expect(command.count).to_equal(6)
expect(command.element_type).to_equal(0)
```

</details>

#### records draw elements parameters

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val command = webgl_render_command_draw_elements(4, 12, 5123, 24)
expect(command.kind).to_equal(WEBGL_RENDER_COMMAND_DRAW_ELEMENTS)
expect(command.mode).to_equal(4)
expect(command.first).to_equal(0)
expect(command.count).to_equal(12)
expect(command.element_type).to_equal(5123)
expect(command.offset).to_equal(24)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/feature/web_platform/webgl/webgl_render_commands_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Browser WebGL render command IR

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 10 |
| Active scenarios | 10 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

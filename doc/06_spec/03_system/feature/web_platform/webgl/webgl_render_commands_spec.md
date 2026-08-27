# webgl_render_commands_spec

> Purpose: records viewport dimensions as flat command data

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# webgl_render_commands_spec

Purpose: records viewport dimensions as flat command data

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/feature/web_platform/webgl/webgl_render_commands_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: records viewport dimensions as flat command data
Audience: compiler and tooling engineers who maintain this spec

## Scenarios

### Browser WebGL render command IR

#### records viewport dimensions as flat command data

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- records viewport dimensions as flat command data
- Verify: records viewport dimensions as flat command data
   - Expected: command.kind equals `WEBGL_RENDER_COMMAND_VIEWPORT`
   - Expected: command.x equals `4`
   - Expected: command.y equals `8`
   - Expected: command.width equals `640`
   - Expected: command.height equals `480`
   - Expected: command.program_id equals `-1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("records viewport dimensions as flat command data")
step("Verify: records viewport dimensions as flat command data")
# @req: REQ-FEATURE-WebgRendComm-001
val command = webgl_render_command_viewport(4, 8, 640, 480)
expect(command.kind).to_equal(WEBGL_RENDER_COMMAND_VIEWPORT)
expect(command.x).to_equal(4)  # oracle: value fixed by the spec contract
expect(command.y).to_equal(8)  # oracle: value fixed by the spec contract
expect(command.width).to_equal(640)  # oracle: value fixed by the spec contract
expect(command.height).to_equal(480)  # oracle: value fixed by the spec contract
expect(command.program_id).to_equal(-1)  # oracle: value fixed by the spec contract
```

</details>

#### records clear color channels

- records clear color channels
- Verify: records clear color channels
   - Expected: command.kind equals `WEBGL_RENDER_COMMAND_CLEAR_COLOR`
   - Expected: command.red equals `0.25`
   - Expected: command.green equals `0.5`
   - Expected: command.blue equals `0.75`
   - Expected: command.alpha equals `1.0`
   - Expected: command.mask equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("records clear color channels")
step("Verify: records clear color channels")
# @req: REQ-FEATURE-WebgRendComm-001
val command = webgl_render_command_clear_color(0.25, 0.5, 0.75, 1.0)
expect(command.kind).to_equal(WEBGL_RENDER_COMMAND_CLEAR_COLOR)
expect(command.red).to_equal(0.25)
expect(command.green).to_equal(0.5)
expect(command.blue).to_equal(0.75)
expect(command.alpha).to_equal(1.0)
expect(command.mask).to_equal(0)  # oracle: value fixed by the spec contract
```

</details>

#### records clear mask

- records clear mask
- Verify: records clear mask
   - Expected: command.kind equals `WEBGL_RENDER_COMMAND_CLEAR`
   - Expected: command.mask equals `16640`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("records clear mask")
step("Verify: records clear mask")
# @req: REQ-FEATURE-WebgRendComm-001
val command = webgl_render_command_clear(16640)
expect(command.kind).to_equal(WEBGL_RENDER_COMMAND_CLEAR)
expect(command.mask).to_equal(16640)  # oracle: value fixed by the spec contract
```

</details>

#### records program binding

- records program binding
- Verify: records program binding
   - Expected: command.kind equals `WEBGL_RENDER_COMMAND_USE_PROGRAM`
   - Expected: command.program_id equals `7`
   - Expected: command.buffer_id equals `-1`
   - Expected: command.texture_id equals `-1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("records program binding")
step("Verify: records program binding")
# @req: REQ-FEATURE-WebgRendComm-001
val command = webgl_render_command_use_program(7)
expect(command.kind).to_equal(WEBGL_RENDER_COMMAND_USE_PROGRAM)
expect(command.program_id).to_equal(7)  # oracle: value fixed by the spec contract
expect(command.buffer_id).to_equal(-1)  # oracle: value fixed by the spec contract
expect(command.texture_id).to_equal(-1)  # oracle: value fixed by the spec contract
```

</details>

#### records uniform setter payloads

- records uniform setter payloads
- Verify: records uniform setter payloads
   - Expected: sampler.kind equals `WEBGL_RENDER_COMMAND_UNIFORM_1I`
   - Expected: sampler.program_id equals `7`
   - Expected: sampler.x equals `2`
   - Expected: sampler.mask equals `3`
   - Expected: flags.kind equals `WEBGL_RENDER_COMMAND_UNIFORM_2I`
   - Expected: flags.x equals `11`
   - Expected: flags.y equals `4`
   - Expected: flags.width equals `5`
   - Expected: range.kind equals `WEBGL_RENDER_COMMAND_UNIFORM_3I`
   - Expected: range.height equals `8`
   - Expected: mask.kind equals `WEBGL_RENDER_COMMAND_UNIFORM_4I`
   - Expected: mask.mask equals `12`
   - Expected: uv_scale.kind equals `WEBGL_RENDER_COMMAND_UNIFORM_2F`
   - Expected: uv_scale.x equals `3`
   - Expected: uv_scale.green equals `4.0`
   - Expected: normal_bias.kind equals `WEBGL_RENDER_COMMAND_UNIFORM_3F`
   - Expected: normal_bias.x equals `6`
   - Expected: normal_bias.blue equals `0.3`
   - Expected: tint.kind equals `WEBGL_RENDER_COMMAND_UNIFORM_4F`
   - Expected: tint.x equals `4`
   - Expected: tint.red equals `0.1`
   - Expected: tint.alpha equals `1.0`
   - Expected: opacity_values.kind equals `WEBGL_RENDER_COMMAND_UNIFORM_1FV`
   - Expected: opacity_values.float_values[0] equals `0.75`
   - Expected: uv_values.kind equals `WEBGL_RENDER_COMMAND_UNIFORM_2FV`
   - Expected: uv_values.float_values[1] equals `4.0`
   - Expected: normal_values.kind equals `WEBGL_RENDER_COMMAND_UNIFORM_3FV`
   - Expected: normal_values.float_values[2] equals `0.3`
   - Expected: tint_values.kind equals `WEBGL_RENDER_COMMAND_UNIFORM_4FV`
   - Expected: tint_values.float_values[3] equals `1.0`
   - Expected: matrix.kind equals `WEBGL_RENDER_COMMAND_UNIFORM_MATRIX4FV`
   - Expected: matrix.float_values.len() equals `4`
   - Expected: matrix.float_values[0] equals `1.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 50 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("records uniform setter payloads")
step("Verify: records uniform setter payloads")
# @req: REQ-FEATURE-WebgRendComm-001
val sampler = webgl_render_command_uniform_1i(7, 2, 3)
expect(sampler.kind).to_equal(WEBGL_RENDER_COMMAND_UNIFORM_1I)
expect(sampler.program_id).to_equal(7)  # oracle: value fixed by the spec contract
expect(sampler.x).to_equal(2)  # oracle: value fixed by the spec contract
expect(sampler.mask).to_equal(3)  # oracle: value fixed by the spec contract
val flags = webgl_render_command_uniform_2i(7, 11, 4, 5)
expect(flags.kind).to_equal(WEBGL_RENDER_COMMAND_UNIFORM_2I)
expect(flags.x).to_equal(11)  # oracle: value fixed by the spec contract
expect(flags.y).to_equal(4)  # oracle: value fixed by the spec contract
expect(flags.width).to_equal(5)  # oracle: value fixed by the spec contract
val range = webgl_render_command_uniform_3i(7, 12, 6, 7, 8)
expect(range.kind).to_equal(WEBGL_RENDER_COMMAND_UNIFORM_3I)
expect(range.height).to_equal(8)  # oracle: value fixed by the spec contract
val mask = webgl_render_command_uniform_4i(7, 13, 9, 10, 11, 12)
expect(mask.kind).to_equal(WEBGL_RENDER_COMMAND_UNIFORM_4I)
expect(mask.mask).to_equal(12)  # oracle: value fixed by the spec contract
val uv_scale = webgl_render_command_uniform_2f(7, 3, 2.0, 4.0)
expect(uv_scale.kind).to_equal(WEBGL_RENDER_COMMAND_UNIFORM_2F)
expect(uv_scale.x).to_equal(3)  # oracle: value fixed by the spec contract
expect(uv_scale.green).to_equal(4.0)
val normal_bias = webgl_render_command_uniform_3f(7, 6, 0.1, 0.2, 0.3)
expect(normal_bias.kind).to_equal(WEBGL_RENDER_COMMAND_UNIFORM_3F)
expect(normal_bias.x).to_equal(6)  # oracle: value fixed by the spec contract
expect(normal_bias.blue).to_equal(0.3)
val tint = webgl_render_command_uniform_4f(7, 4, 0.1, 0.2, 0.3, 1.0)
expect(tint.kind).to_equal(WEBGL_RENDER_COMMAND_UNIFORM_4F)
expect(tint.x).to_equal(4)  # oracle: value fixed by the spec contract
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
expect(matrix.float_values.len()).to_equal(4)  # oracle: value fixed by the spec contract
expect(matrix.float_values[0]).to_equal(1.0)
```

</details>

#### records read pixels requests

- records read pixels requests
- Verify: records read pixels requests
   - Expected: command.kind equals `WEBGL_RENDER_COMMAND_READ_PIXELS`
   - Expected: command.x equals `1`
   - Expected: command.y equals `2`
   - Expected: command.width equals `3`
   - Expected: command.height equals `4`
   - Expected: command.target equals `6408`
   - Expected: command.element_type equals `5121`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("records read pixels requests")
step("Verify: records read pixels requests")
# @req: REQ-FEATURE-WebgRendComm-001
val command = webgl_render_command_read_pixels(1, 2, 3, 4, 6408, 5121)
expect(command.kind).to_equal(WEBGL_RENDER_COMMAND_READ_PIXELS)
expect(command.x).to_equal(1)  # oracle: value fixed by the spec contract
expect(command.y).to_equal(2)  # oracle: value fixed by the spec contract
expect(command.width).to_equal(3)  # oracle: value fixed by the spec contract
expect(command.height).to_equal(4)  # oracle: value fixed by the spec contract
expect(command.target).to_equal(6408)  # oracle: value fixed by the spec contract
expect(command.element_type).to_equal(5121)  # oracle: value fixed by the spec contract
```

</details>

#### records buffer and texture bindings

- records buffer and texture bindings
- Verify: records buffer and texture bindings
   - Expected: buffer.kind equals `WEBGL_RENDER_COMMAND_BIND_BUFFER`
   - Expected: buffer.target equals `34962`
   - Expected: buffer.buffer_id equals `3`
   - Expected: texture.kind equals `WEBGL_RENDER_COMMAND_BIND_TEXTURE`
   - Expected: texture.target equals `3553`
   - Expected: texture.texture_id equals `9`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("records buffer and texture bindings")
step("Verify: records buffer and texture bindings")
# @req: REQ-FEATURE-WebgRendComm-001
val buffer = webgl_render_command_bind_buffer(34962, 3)
val texture = webgl_render_command_bind_texture(3553, 9)
expect(buffer.kind).to_equal(WEBGL_RENDER_COMMAND_BIND_BUFFER)
expect(buffer.target).to_equal(34962)  # oracle: value fixed by the spec contract
expect(buffer.buffer_id).to_equal(3)  # oracle: value fixed by the spec contract
expect(texture.kind).to_equal(WEBGL_RENDER_COMMAND_BIND_TEXTURE)
expect(texture.target).to_equal(3553)  # oracle: value fixed by the spec contract
expect(texture.texture_id).to_equal(9)  # oracle: value fixed by the spec contract
```

</details>

#### records generic vertex attribute values

- records generic vertex attribute values
- Verify: records generic vertex attribute values
   - Expected: command.kind equals `WEBGL_RENDER_COMMAND_VERTEX_ATTRIB_4F`
   - Expected: command.x equals `2`
   - Expected: command.red equals `0.25`
   - Expected: command.green equals `0.5`
   - Expected: command.blue equals `0.75`
   - Expected: command.alpha equals `1.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("records generic vertex attribute values")
step("Verify: records generic vertex attribute values")
# @req: REQ-FEATURE-WebgRendComm-001
val command = webgl_render_command_vertex_attrib_4f(2, 0.25, 0.5, 0.75, 1.0)
expect(command.kind).to_equal(WEBGL_RENDER_COMMAND_VERTEX_ATTRIB_4F)
expect(command.x).to_equal(2)  # oracle: value fixed by the spec contract
expect(command.red).to_equal(0.25)
expect(command.green).to_equal(0.5)
expect(command.blue).to_equal(0.75)
expect(command.alpha).to_equal(1.0)
```

</details>

#### records draw arrays parameters

- records draw arrays parameters
- Verify: records draw arrays parameters
   - Expected: command.kind equals `WEBGL_RENDER_COMMAND_DRAW_ARRAYS`
   - Expected: command.mode equals `4`
   - Expected: command.first equals `2`
   - Expected: command.count equals `6`
   - Expected: command.element_type equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("records draw arrays parameters")
step("Verify: records draw arrays parameters")
# @req: REQ-FEATURE-WebgRendComm-001
val command = webgl_render_command_draw_arrays(4, 2, 6)
expect(command.kind).to_equal(WEBGL_RENDER_COMMAND_DRAW_ARRAYS)
expect(command.mode).to_equal(4)  # oracle: value fixed by the spec contract
expect(command.first).to_equal(2)  # oracle: value fixed by the spec contract
expect(command.count).to_equal(6)  # oracle: value fixed by the spec contract
expect(command.element_type).to_equal(0)  # oracle: value fixed by the spec contract
```

</details>

#### records draw elements parameters

- records draw elements parameters
- Verify: records draw elements parameters
   - Expected: command.kind equals `WEBGL_RENDER_COMMAND_DRAW_ELEMENTS`
   - Expected: command.mode equals `4`
   - Expected: command.first equals `0`
   - Expected: command.count equals `12`
   - Expected: command.element_type equals `5123`
   - Expected: command.offset equals `24`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("records draw elements parameters")
step("Verify: records draw elements parameters")
# @req: REQ-FEATURE-WebgRendComm-001
val command = webgl_render_command_draw_elements(4, 12, 5123, 24)
expect(command.kind).to_equal(WEBGL_RENDER_COMMAND_DRAW_ELEMENTS)
expect(command.mode).to_equal(4)  # oracle: value fixed by the spec contract
expect(command.first).to_equal(0)  # oracle: value fixed by the spec contract
expect(command.count).to_equal(12)  # oracle: value fixed by the spec contract
expect(command.element_type).to_equal(5123)  # oracle: value fixed by the spec contract
expect(command.offset).to_equal(24)  # oracle: value fixed by the spec contract
```

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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
- `REQ-FEATURE-WebgRendComm-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `d7fbe609166d4d14ba45cc44ca2c559897e9fc0e2cadc8b8fb0ab5d2ebee09ad`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `d7fbe609166d4d14ba45cc44ca2c559897e9fc0e2cadc8b8fb0ab5d2ebee09ad`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `d7fbe609166d4d14ba45cc44ca2c559897e9fc0e2cadc8b8fb0ab5d2ebee09ad`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/03_system/feature/web_platform/webgl/webgl_render_commands_spec.spl
mirror: doc/06_spec/03_system/feature/web_platform/webgl/webgl_render_commands_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/feature/web_platform/webgl/webgl_render_commands_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/feature/web_platform/webgl/webgl_render_commands_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/feature/web_platform/webgl/webgl_render_commands_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 17 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/feature/web_platform/webgl/webgl_render_commands_spec.spl:47:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'records viewport dimensions as flat command data' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/web_platform/webgl/webgl_render_commands_spec.spl:60:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'records clear color channels' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/web_platform/webgl/webgl_render_commands_spec.spl:73:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'records clear mask' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

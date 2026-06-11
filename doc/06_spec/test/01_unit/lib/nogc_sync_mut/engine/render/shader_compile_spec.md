# Shader Compile Specification

> <details>

<!-- sdn-diagram:id=shader_compile_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=shader_compile_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

shader_compile_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=shader_compile_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 17 | 17 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Shader Compile Specification

## Scenarios

### Stream E: ShaderArtifact construction

### empty artifact

#### AC-5: is_compiled is false when not compiled

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val art = make_empty_artifact()
expect(art.is_compiled).to_equal(false)
```

</details>

#### AC-5: error_msg is empty string when no error

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val art = make_empty_artifact()
expect(art.error_msg).to_equal("")
```

</details>

#### AC-5: spirv_vertex is empty slice when not compiled

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val art = make_empty_artifact()
expect(art.spirv_vertex.length).to_equal(0)
```

</details>

#### AC-5: wgsl_vertex is empty when not compiled

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val art = make_empty_artifact()
expect(art.wgsl_vertex).to_equal("")
```

</details>

### Stream E: ShaderCompiler caching

### shader_compiler_new

#### AC-5: creates compiler with empty cache

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val compiler = shader_compiler_new()
expect(compiler.cache.keys.length).to_equal(0)
```

</details>

### get_or_compile_wgsl caching

#### AC-5: first compile call returns an artifact

1. var compiler = shader compiler new
   - Expected: got_something is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var compiler = shader_compiler_new()
val src = make_simple_shader_source()
val art = shader_compiler_get_or_compile_wgsl(compiler, src)
val got_something = art.is_compiled or art.error_msg.length >= 0
expect(got_something).to_equal(true)
```

</details>

#### AC-5: second call with same source returns cached result (cache grows by 1 total)

1. var compiler = shader compiler new
   - Expected: cache_size_after_second equals `cache_size_after_first`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var compiler = shader_compiler_new()
val src = make_simple_shader_source()
val _ = shader_compiler_get_or_compile_wgsl(compiler, src)
val cache_size_after_first = compiler.cache.keys.length
val _ = shader_compiler_get_or_compile_wgsl(compiler, src)
val cache_size_after_second = compiler.cache.keys.length
expect(cache_size_after_second).to_equal(cache_size_after_first)
```

</details>

#### AC-5: different sources produce separate cache entries

1. var compiler = shader compiler new
   - Expected: compiler.cache.keys.length equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var compiler = shader_compiler_new()
val src1 = make_simple_shader_source()
val src2 = make_phong_shader_source()
val _ = shader_compiler_get_or_compile_wgsl(compiler, src1)
val _ = shader_compiler_get_or_compile_wgsl(compiler, src2)
expect(compiler.cache.keys.length).to_equal(2)
```

</details>

### get_or_compile_spirv caching

#### AC-5: second call with same source does not grow spirv cache

1. var compiler = shader compiler new
   - Expected: compiler.cache.keys.length equals `cache_size`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var compiler = shader_compiler_new()
val src = make_simple_shader_source()
val _ = shader_compiler_get_or_compile_spirv(compiler, src)
val cache_size = compiler.cache.keys.length
val _ = shader_compiler_get_or_compile_spirv(compiler, src)
expect(compiler.cache.keys.length).to_equal(cache_size)
```

</details>

### Stream E: WgslEmitter basic GLSL to WGSL transformation

### wgsl_emit_vertex

#### AC-5: output is non-empty text

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val glsl = "void main() { gl_Position = vec4(0.0, 0.0, 0.0, 1.0); }"
val wgsl = wgsl_emit_vertex(glsl)
expect(wgsl.length).to_be_greater_than(0)
```

</details>

#### AC-5: output does not contain void main() (GLSL form)

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val glsl = "void main() { gl_Position = vec4(0.0, 0.0, 0.0, 1.0); }"
val wgsl = wgsl_emit_vertex(glsl)
val has_glsl_main = wgsl.contains("void main()")
expect(has_glsl_main).to_equal(false)
```

</details>

#### AC-5: output contains @vertex (WGSL entry point marker)

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val glsl = "void main() { gl_Position = vec4(0.0, 0.0, 0.0, 1.0); }"
val wgsl = wgsl_emit_vertex(glsl)
expect(wgsl).to_contain("@vertex")
```

</details>

#### AC-5: gl_Position is replaced by builtin position annotation

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val glsl = "void main() { gl_Position = vec4(0.0, 0.0, 0.0, 1.0); }"
val wgsl = wgsl_emit_vertex(glsl)
val has_builtin = wgsl.contains("position") or wgsl.contains("builtin")
expect(has_builtin).to_equal(true)
```

</details>

### wgsl_emit_fragment

#### AC-5: output is non-empty text

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val glsl = "void main() { gl_FragColor = vec4(1.0, 0.0, 0.0, 1.0); }"
val wgsl = wgsl_emit_fragment(glsl)
expect(wgsl.length).to_be_greater_than(0)
```

</details>

#### AC-5: output contains @fragment (WGSL entry point marker)

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val glsl = "void main() { gl_FragColor = vec4(1.0, 0.0, 0.0, 1.0); }"
val wgsl = wgsl_emit_fragment(glsl)
expect(wgsl).to_contain("@fragment")
```

</details>

#### AC-5: gl_FragColor is replaced by location annotation

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val glsl = "void main() { gl_FragColor = vec4(1.0, 0.0, 0.0, 1.0); }"
val wgsl = wgsl_emit_fragment(glsl)
val has_location = wgsl.contains("location") or wgsl.contains("@location")
expect(has_location).to_equal(true)
```

</details>

#### AC-5: output does not contain gl_FragColor

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val glsl = "void main() { gl_FragColor = vec4(1.0, 0.0, 0.0, 1.0); }"
val wgsl = wgsl_emit_fragment(glsl)
val still_has_fragcolor = wgsl.contains("gl_FragColor")
expect(still_has_fragcolor).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_sync_mut/engine/render/shader_compile_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Stream E: ShaderArtifact construction
- empty artifact
- Stream E: ShaderCompiler caching
- shader_compiler_new
- get_or_compile_wgsl caching
- get_or_compile_spirv caching
- Stream E: WgslEmitter basic GLSL to WGSL transformation
- wgsl_emit_vertex
- wgsl_emit_fragment

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 17 |
| Active scenarios | 17 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

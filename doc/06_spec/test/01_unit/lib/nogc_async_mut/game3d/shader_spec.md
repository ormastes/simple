# Shader Specification

> 1. check

<!-- sdn-diagram:id=shader_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=shader_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

shader_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=shader_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Shader Specification

## Scenarios

### ShaderSystem

#### creates shaders

1. check
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val vertex = Shader.new("vertex", "vertex_code")
val fragment = Shader.new("fragment", "fragment_code")
check(vertex.name == "vertex")
check(fragment.name == "fragment")
```

</details>

#### compiles shaders

1. shader compile
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val shader = Shader.new("test", "shader_code")
shader.compile()
check(shader.is_compiled() == true)
```

</details>

#### sets shader uniforms

1. uniform set value
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val uniform = ShaderUniform.new("color", "vec4")
uniform.set_value("1.0, 1.0, 1.0, 1.0")
check(uniform.get_value() == "1.0, 1.0, 1.0, 1.0")
```

</details>

#### handles shader programs

1. program link
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val vs = Shader.new("vertex", "vs_code")
val fs = Shader.new("fragment", "fs_code")
val program = ShaderProgram.new(vs, fs)
program.link()
check(program.is_linked() == true)
```

</details>

#### handles shader includes

1. program add uniform
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val vs = Shader.new("vertex", "vs_code")
val fs = Shader.new("fragment", "fs_code")
val program = ShaderProgram.new(vs, fs)
val uniform = ShaderUniform.new("projection", "mat4")
program.add_uniform(uniform)
check(program.get_uniform_count() == 1)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_async_mut/game3d/shader_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- ShaderSystem

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

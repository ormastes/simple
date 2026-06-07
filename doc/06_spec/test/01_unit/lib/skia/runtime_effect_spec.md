# Skia RuntimeEffect Specification

> Tests the structural container types for SkRuntimeEffect: the uniform/child schema entries, the effect constructor, the is_compiled probe, and the SkRuntimeShaderBuilder's uniform-setting + build() stub. The SkSL frontend is out of scope — these tests only exercise the container surface so the rest of the paint/shader stack can reference RuntimeEffect types today.

<!-- sdn-diagram:id=runtime_effect_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=runtime_effect_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

runtime_effect_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=runtime_effect_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Skia RuntimeEffect Specification

Tests the structural container types for SkRuntimeEffect: the uniform/child schema entries, the effect constructor, the is_compiled probe, and the SkRuntimeShaderBuilder's uniform-setting + build() stub. The SkSL frontend is out of scope — these tests only exercise the container surface so the rest of the paint/shader stack can reference RuntimeEffect types today.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #SKI-RT-001 |
| Category | Stdlib |
| Difficulty | 2/5 |
| Status | Structural stub |
| Source | `test/01_unit/lib/skia/runtime_effect_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests the structural container types for SkRuntimeEffect: the uniform/child
schema entries, the effect constructor, the is_compiled probe, and the
SkRuntimeShaderBuilder's uniform-setting + build() stub. The SkSL frontend
is out of scope — these tests only exercise the container surface so the
rest of the paint/shader stack can reference RuntimeEffect types today.

## Scenarios

### runtime_effect

#### sk_runtime_effect_make: creates effect with source and uniforms

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val u0 = RuntimeEffectUniform(name: "uTime", kind: UniformKind.Float, array_count: 1)
val u1 = RuntimeEffectUniform(name: "uRes", kind: UniformKind.Float2, array_count: 1)
val uniforms = [u0, u1]
val children = []
val src = "half4 main(float2 p) { return half4(1); }"
val eff = sk_runtime_effect_make(src, uniforms, children)
expect(eff.sksl_source).to_equal(src)
expect(eff.uniforms.len()).to_equal(2)
expect(eff.children.len()).to_equal(0)
```

</details>

#### sk_runtime_effect_is_compiled: new effect (empty bytecode) returns false

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val eff = sk_runtime_effect_make("half4 main(float2 p) { return half4(0); }", [], [])
val compiled = sk_runtime_effect_is_compiled(eff)
expect(compiled).to_equal(false)
expect(eff.bytecode.len()).to_equal(0)
```

</details>

#### SkRuntimeShaderBuilder: set_uniform_float stores value in uniform_values

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val u0 = RuntimeEffectUniform(name: "uAlpha", kind: UniformKind.Float, array_count: 1)
val eff = sk_runtime_effect_make("src", [u0], [])
val builder = SkRuntimeShaderBuilder(
    effect: eff,
    uniform_values: [[]],
    children_shaders: []
)
val updated = builder.set_uniform_float("uAlpha", 0.5)
expect(updated.uniform_values.len()).to_equal(1)
expect(updated.uniform_values[0].len()).to_be_greater_than(0)
```

</details>

#### SkRuntimeShaderBuilder: build() returns None when bytecode is empty

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val eff = sk_runtime_effect_make("src", [], [])
val builder = SkRuntimeShaderBuilder(
    effect: eff,
    uniform_values: [],
    children_shaders: []
)
val result = builder.build()
expect(result).to_be_nil()
```

</details>

#### UniformKind variants are distinct

<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = UniformKind.Float
val b = UniformKind.Float2
val c = UniformKind.Float3
val d = UniformKind.Float4
val e = UniformKind.Int
val f = UniformKind.Matrix3
val g = UniformKind.Matrix4
val ab = a == b
val ac = a == c
val ad = a == d
val ae = a == e
val af = a == f
val ag = a == g
val fg = f == g
expect(ab).to_equal(false)
expect(ac).to_equal(false)
expect(ad).to_equal(false)
expect(ae).to_equal(false)
expect(af).to_equal(false)
expect(ag).to_equal(false)
expect(fg).to_equal(false)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

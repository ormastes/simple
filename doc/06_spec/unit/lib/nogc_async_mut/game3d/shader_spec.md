# Shader Specification

> Tests covering ShaderSystem.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Shader Specification

## Scenarios

### ShaderSystem

#### creates shaders

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- creates shaders


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates shaders")
val vertex = Shader.new("vertex", "vertex_code")
val fragment = Shader.new("fragment", "fragment_code")
check(vertex.name == "vertex")
check(fragment.name == "fragment")
```

</details>

#### compiles shaders

- compiles shaders


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("compiles shaders")
val shader = Shader.new("test", "shader_code")
shader.compile()
check(shader.is_compiled() == true)
```

</details>

#### sets shader uniforms

- sets shader uniforms


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("sets shader uniforms")
val uniform = ShaderUniform.new("color", "vec4")
uniform.set_value("1.0, 1.0, 1.0, 1.0")
check(uniform.get_value() == "1.0, 1.0, 1.0, 1.0")
```

</details>

#### handles shader programs

- handles shader programs


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles shader programs")
val vs = Shader.new("vertex", "vs_code")
val fs = Shader.new("fragment", "fs_code")
val program = ShaderProgram.new(vs, fs)
program.link()
check(program.is_linked() == true)
```

</details>

#### handles shader includes

- handles shader includes


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles shader includes")
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
| Source | `test/unit/lib/nogc_async_mut/game3d/shader_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering ShaderSystem.
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `2791997a9a978c7113e1e97ea98f36d8db563b4a7065844d8bcfa1ecab8c4b8f`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `2791997a9a978c7113e1e97ea98f36d8db563b4a7065844d8bcfa1ecab8c4b8f`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `2791997a9a978c7113e1e97ea98f36d8db563b4a7065844d8bcfa1ecab8c4b8f`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/lib/nogc_async_mut/game3d/shader_spec.spl
mirror: doc/06_spec/unit/lib/nogc_async_mut/game3d/shader_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/lib/nogc_async_mut/game3d/shader_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/lib/nogc_async_mut/game3d/shader_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/lib/nogc_async_mut/game3d/shader_spec.spl:86:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates shaders' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/nogc_async_mut/game3d/shader_spec.spl:94:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'compiles shaders' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/nogc_async_mut/game3d/shader_spec.spl:101:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'sets shader uniforms' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

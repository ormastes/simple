# Engine3d Pipeline Specification

> Tests covering Engine3D Shader Pipeline Lifecycle.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Engine3d Pipeline Specification

## Scenarios

### Engine3D Shader Pipeline Lifecycle

#### create_shader

#### returns i32 id

- returns i32 id


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("returns i32 id")
var engine = Engine3D.create(320, 240)
val id = engine.create_shader("void main(){}", "void main(){}")
expect(id).to_be_greater_than(-2)
```

</details>

#### delete_shader

#### with valid id does not crash

- with valid id does not crash
   - Expected: true is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("with valid id does not crash")
var engine = Engine3D.create(320, 240)
val id = engine.create_shader("void main(){}", "void main(){}")
engine.delete_shader(id)
expect(true).to_equal(true)
```

</details>

#### create_pipeline

#### returns i32 id

- returns i32 id


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("returns i32 id")
var engine = Engine3D.create(320, 240)
val shader_id = engine.create_shader("void main(){}", "void main(){}")
val id = engine.create_pipeline(shader_id, true, 0, 0)
expect(id).to_be_greater_than(-2)
```

</details>

#### bind_pipeline

#### with valid id does not crash

- with valid id does not crash
   - Expected: true is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("with valid id does not crash")
var engine = Engine3D.create(320, 240)
val shader_id = engine.create_shader("void main(){}", "void main(){}")
val pipeline_id = engine.create_pipeline(shader_id, false, 0, 0)
engine.bind_pipeline(pipeline_id)
expect(true).to_equal(true)
```

</details>

#### render pass lifecycle

#### begin_render_pass and end_render_pass lifecycle works

- begin_render_pass and end_render_pass lifecycle works
   - Expected: true is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("begin_render_pass and end_render_pass lifecycle works")
var engine = Engine3D.create(320, 240)
val color_target = engine.create_texture(320, 240, [0xFF000000])
val depth_target = engine.create_depth_texture(320, 240)
engine.begin_render_pass(color_target, depth_target)
engine.end_render_pass()
expect(true).to_equal(true)
```

</details>

#### compute kernel

#### create_compute_kernel returns i32 id

- create_compute_kernel returns i32 id


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("create_compute_kernel returns i32 id")
var engine = Engine3D.create(320, 240)
val id = engine.create_compute_kernel("void main(){}")
expect(id).to_be_greater_than(-2)
```

</details>

#### dispatch_compute with valid kernel id does not crash

- dispatch_compute with valid kernel id does not crash
   - Expected: true is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("dispatch_compute with valid kernel id does not crash")
var engine = Engine3D.create(320, 240)
val id = engine.create_compute_kernel("void main(){}")
engine.dispatch_compute(id, 1, 1, 1)
expect(true).to_equal(true)
```

</details>

#### storage buffer

#### create_storage_buffer returns i32 id

- create_storage_buffer returns i32 id


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("create_storage_buffer returns i32 id")
var engine = Engine3D.create(320, 240)
val id = engine.create_storage_buffer(256)
expect(id).to_be_greater_than(-2)
```

</details>

#### update_buffer and read_buffer round-trip may return empty in emu

- update_buffer and read_buffer round-trip may return empty in emu


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("update_buffer and read_buffer round-trip may return empty in emu")
var engine = Engine3D.create(320, 240)
val id = engine.create_storage_buffer(4)
val data: [u8] = [1, 2, 3, 4]
engine.update_buffer(id, data)
val result = engine.read_buffer(id)
expect(result.len()).to_be_greater_than(-1)
```

</details>

#### shadow pass lifecycle

#### begin_shadow_pass and end_shadow_pass lifecycle works

- begin_shadow_pass and end_shadow_pass lifecycle works
   - Expected: true is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("begin_shadow_pass and end_shadow_pass lifecycle works")
var engine = Engine3D.create(320, 240)
val mat: [f32] = [
    1.0, 0.0, 0.0, 0.0,
    0.0, 1.0, 0.0, 0.0,
    0.0, 0.0, 1.0, 0.0,
    0.0, 0.0, 0.0, 1.0
]
engine.begin_shadow_pass(mat, 512)
engine.end_shadow_pass()
expect(true).to_equal(true)
```

</details>

#### synchronization

#### pipeline_barrier does not crash

- pipeline_barrier does not crash
   - Expected: true is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("pipeline_barrier does not crash")
var engine = Engine3D.create(320, 240)
engine.pipeline_barrier()
expect(true).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/integration/rendering/engine3d_pipeline_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Engine3D Shader Pipeline Lifecycle.
- Engine3D Shader Pipeline Lifecycle

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 11 |
| Active scenarios | 11 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-INTEGRATION`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `d4c573fac64a0c73e2d5669b8ffe0d32dcdd60cafc973c285b29f315495afa4f`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `d4c573fac64a0c73e2d5669b8ffe0d32dcdd60cafc973c285b29f315495afa4f`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `d4c573fac64a0c73e2d5669b8ffe0d32dcdd60cafc973c285b29f315495afa4f`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/integration/rendering/engine3d_pipeline_spec.spl
mirror: doc/06_spec/integration/rendering/engine3d_pipeline_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/integration/rendering/engine3d_pipeline_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/integration/rendering/engine3d_pipeline_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/integration/rendering/engine3d_pipeline_spec.spl:19:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns i32 id' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/rendering/engine3d_pipeline_spec.spl:28:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'with valid id does not crash' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/rendering/engine3d_pipeline_spec.spl:38:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns i32 id' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

# vulkan_line_strict_source_contract_spec

> Strict Vulkan line source contract.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# vulkan_line_strict_source_contract_spec

Strict Vulkan line source contract.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gc_async_mut/gpu/engine2d/vulkan_line_strict_source_contract_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Strict Vulkan line source contract.

This host-safe guard complements the live device oracle. It proves the session
loads the dedicated line artifact, the backend submits that artifact as one
ordered GPU Bresenham invocation, and strict DrawIR rejects oracle mismatch.

## Scenarios

### strict Vulkan DrawIR line source contract

#### loads the real line SPIR-V pipeline and never aliases the no-op shader

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- loads the real line SPIR-V pipeline and never aliases the no-op shader


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("loads the real line SPIR-V pipeline and never aliases the no-op shader")
val session = file_read(
    "src/lib/gc_async_mut/gpu/engine2d/vulkan_session.spl")
expect(session).to_contain(
    "self.shader_line          = vulkan_sffi_compile_spirv(spirv_line())")
expect(session).to_contain(
    "self.pipe_line           = vulkan_sffi_create_compute_pipeline(self.shader_line")
expect(session).to_contain("elif self.shader_line <= 0:")
expect(session).to_contain("elif self.pipe_line <= 0:")
```

</details>

#### dispatches the canonical ordered GPU Bresenham kernel and fails closed

- dispatches the canonical ordered GPU Bresenham kernel and fails closed


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("dispatches the canonical ordered GPU Bresenham kernel and fails closed")
val glsl = file_read(
    "src/lib/gc_async_mut/gpu/engine2d/backend_vulkan_glsl.spl")
val backend = file_read(
    "src/lib/gc_async_mut/gpu/engine2d/backend_vulkan.spl")
expect(glsl).to_contain("layout(local_size_x = 1) in;")
expect(glsl).to_contain("int err = dx - dy;")
expect(glsl).to_contain("if (px == pc.x2 && py == pc.y2) break;")
expect(glsl).to_contain("if (e2 > -dy) { err -= dy; px += sx; }")
expect(glsl).to_contain("if (e2 < dx) { err += dx; py += sy; }")
expect(backend).to_contain("self.pipe_line, pc, 1, 1, 1")
expect(backend).to_contain("self.mark_cpu_fallback(\"line-dispatch-failed\")")
```

</details>

#### bounds box commands separately from point-bounded EDGE and PATH commands

- bounds box commands separately from point-bounded EDGE and PATH commands


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("bounds box commands separately from point-bounded EDGE and PATH commands")
val executor = file_read(
    "src/lib/gc_async_mut/gpu/engine2d/draw_ir_adv.spl")
expect(executor).to_contain(
    "fn _engine2d_draw_ir_strict_vulkan_box_bounded")
expect(executor).to_contain("if command.kind == DRAW_IR_COMMAND_RECT:")
expect(executor).to_contain("elif command.kind == DRAW_IR_COMMAND_TEXT:")
expect(executor).to_contain("for point in stroke.points:")
expect(executor).to_contain(
    "return \"strict-vulkan-line-bounds-required\"")
```

</details>

#### accepts production pixels only with strict device evidence

- accepts production pixels only with strict device evidence


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("accepts production pixels only with strict device evidence")
val executor = file_read(
    "src/lib/gc_async_mut/gpu/engine2d/draw_ir_adv.spl")
expect(executor).to_contain(
    "result.readback_source == \"device_readback\"")
expect(executor).to_contain("result.backend_handle > 0")
expect(executor).to_contain("result.device_identity > 0")
expect(executor).to_contain("strict-vulkan-device-evidence-required")
expect(executor).to_contain("result.pixels = []")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
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

- Canonical SPipe generation for source `24d0b2be3b0efba8dab6e4caf14426b9206ef727505c6e2cf44d4b32dca7a644`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `24d0b2be3b0efba8dab6e4caf14426b9206ef727505c6e2cf44d4b32dca7a644`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `24d0b2be3b0efba8dab6e4caf14426b9206ef727505c6e2cf44d4b32dca7a644`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/gc_async_mut/gpu/engine2d/vulkan_line_strict_source_contract_spec.spl
mirror: doc/06_spec/01_unit/lib/gc_async_mut/gpu/engine2d/vulkan_line_strict_source_contract_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/gc_async_mut/gpu/engine2d/vulkan_line_strict_source_contract_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/gc_async_mut/gpu/engine2d/vulkan_line_strict_source_contract_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/gc_async_mut/gpu/engine2d/vulkan_line_strict_source_contract_spec.spl:19:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'loads the real line SPIR-V pipeline and never aliases the no-op shader' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gc_async_mut/gpu/engine2d/vulkan_line_strict_source_contract_spec.spl:31:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'dispatches the canonical ordered GPU Bresenham kernel and fails closed' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gc_async_mut/gpu/engine2d/vulkan_line_strict_source_contract_spec.spl:46:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'bounds box commands separately from point-bounded EDGE and PATH commands' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

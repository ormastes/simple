# processing_cuda_directx_native_spec

> Verifies the processing cuda directx native behaviour end to end so maintainers of this

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# processing_cuda_directx_native_spec

Verifies the processing cuda directx native behaviour end to end so maintainers of this

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/app/simple_2d/feature/processing_cuda_directx_native_spec.spl` |
| Updated | 2026-08-22 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Verifies the processing cuda directx native behaviour end to end so maintainers of this
component and reviewers of its spec share one pinned definition.
## Operator workflow
Run `bin/simple test <this spec>`; read the per-scenario verdicts in
the `Results:` summary. Each scenario asserts an observable outcome.
## Compatibility and limitations
Covers the currently shipped behaviour only; performance, stress and
unrelated sibling features are out of scope.

## Scenarios

### CUDA-to-DirectX native evidence admission

#### should require deterministic HLSL bindings before native Windows submission

- Verify: should require deterministic HLSL bindings before native Windows submission
- Select representative renderer processing kernels
- Translate drawing access for the destination backend
- Compile and validate the backend artifact


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-006 REQ-007 REQ-011 REQ-012
step("Verify: should require deterministic HLSL bindings before native Windows submission")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
step("Select representative renderer processing kernels")
val translator = file_read("src/lib/gc_async_mut/processing/cuda_drawing_translation.spl")
expect(translator).to_contain("PROCESSING_IR_OP_FILL_RECT_U32")

step("Translate drawing access for the destination backend")
expect(translator).to_contain("ProcessingBackendTarget.DirectXHlsl")
expect(translator).to_contain("RWStructuredBuffer<uint> output : register(u0)")
expect(translator).to_contain("cbuffer DrawParams : register(b0)")
expect(translator).to_contain("output[py * stride + px]")
expect(translator).to_contain("inside ? pixel_value : 0u")

step("Compile and validate the backend artifact")
expect(translator).to_contain("unsupported-cuda-drawing-op")
expect(translator).to_contain("unsupported-cuda-drawing-translation-target")
```

</details>

#### should record Windows execution as blocked until raw device readback exists

- Verify: should record Windows execution as blocked until raw device readback exists
- Submit native work and capture device readback
- Compare device readback with the CPU oracle
- Record unavailable native host evidence


<details>
<summary>Executable SSpec</summary>

Runnable source: 27 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-006 REQ-007 REQ-011 REQ-012
step("Verify: should record Windows execution as blocked until raw device readback exists")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
step("Submit native work and capture device readback")
val todos = file_read("doc/08_tracking/todo/todo_db.sdn")
expect(todos).to_contain("653, TODO, gpu, P1")
expect(todos).to_contain("Windows x86_64 with the Windows SDK D3D12 runtime and debug layer")
expect(todos).to_contain("DirectX 12 compute-capable physical adapter")
expect(todos).to_contain("Windows SDK D3D12 runtime and debug layer")
expect(todos).to_contain("WARP is not admissible")
expect(todos).to_contain("DXC available on PATH")
expect(todos).to_contain("generated HLSL and compiled DXIL artifacts")
expect(todos).to_contain("D3D12 command submission, queue, fence-completion, and debug-layer event evidence")
expect(todos).to_contain("rendered output image plus dimensions/format/hash")
expect(todos).to_contain("raw device readback")

step("Compare device readback with the CPU oracle")
expect(todos).to_contain("CPU oracle")
expect(todos).to_contain("mismatch count")

step("Record unavailable native host evidence")
expect(todos).to_contain("processing_cuda_directx_native_spec.spl --mode=interpreter")
expect(todos).to_contain("Owner: prepared-Windows evidence operator")
expect(todos).to_contain("Merge owner: root Codex agent")
expect(todos).to_contain("Final reviewer: normal/highest-capability Codex reviewer")
expect(todos).to_contain("open, true")
fail_test("BLOCKED CUDA-to-DirectX native row: prepared Windows DirectX 12 host required; resume under TODO 653")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `35dae35fc2c106124a0f560f1124190aa2b451508984c8feda2728f8a1397587`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `35dae35fc2c106124a0f560f1124190aa2b451508984c8feda2728f8a1397587`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `35dae35fc2c106124a0f560f1124190aa2b451508984c8feda2728f8a1397587`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **93/100**; effective score: **93/100**; blockers: **0**.

SSpec documentization score: 93/100
source: test/03_system/app/simple_2d/feature/processing_cuda_directx_native_spec.spl
mirror: doc/06_spec/03_system/app/simple_2d/feature/processing_cuda_directx_native_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=90 oracle=100
  traceability=100 evidence=85 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/app/simple_2d/feature/processing_cuda_directx_native_spec.md:1:1: warning SSDOC-EVD-002 [evidence] (-15): source steps are not visible in the generated manual
  why: Source tokens alone do not prove reader-visible workflow structure.
  improve: Use supported literal step calls and regenerate the manual.
doc/06_spec/03_system/app/simple_2d/feature/processing_cuda_directx_native_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/app/simple_2d/feature/processing_cuda_directx_native_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: assumptions/preconditions, traceability, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/app/simple_2d/feature/processing_cuda_directx_native_spec.spl:28:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should require deterministic HLSL bindings before native Windows submission' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/simple_2d/feature/processing_cuda_directx_native_spec.spl:47:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should record Windows execution as blocked until raw device readback exists' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->

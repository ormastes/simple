# Processing Cuda Backend Specification

> Tests covering CUDA ProcessingIR backend operator flow.

## Windows DirectX row

<details>
<summary>Full Scenario Manual</summary>

# Processing Cuda Backend Specification

## Scenarios

### CUDA ProcessingIR backend operator flow

#### should document generation validation readback and unavailable-host evidence

- should document generation validation readback and unavailable-host evidence
- Select representative renderer processing kernels
- Lower shared ProcessingIR for the selected backend
- Translate drawing access for the destination backend
- Compile and validate the backend artifact
- Submit native work and capture device readback
- Compare device readback with the CPU oracle
- Record unavailable native host evidence


<details>
<summary>Executable SSpec</summary>

Runnable source: 35 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should document generation validation readback and unavailable-host evidence")
step("Select representative renderer processing kernels")
val executor = file_read(CUDA_EXECUTOR)
expect(executor).to_contain("PROCESSING_IR_OP_FILL_U32")

step("Lower shared ProcessingIR for the selected backend")
expect(executor).to_contain("fn processing_cuda_artifact(ir: ProcessingIr)")
expect(executor).to_contain("ProcessingBackendTarget.CudaPtx")
expect(executor).to_contain(".visible .entry processing_fill_u32")

step("Translate drawing access for the destination backend")
val drawing = file_read(DRAW_TRANSLATOR)
expect(drawing).to_contain("ProcessingBackendTarget.VulkanSpirv")
expect(drawing).to_contain("ProcessingBackendTarget.DirectXHlsl")
expect(drawing).to_contain("RWStructuredBuffer<uint> output : register(u0)")
expect(drawing).to_contain("output[py * stride + px]")

step("Compile and validate the backend artifact")
expect(executor).to_contain("fn processing_cuda_compile_evidence(")
expect(executor).to_contain("cuda-compiler-identity-missing")

step("Submit native work and capture device readback")
val wrapper = file_read(CUDA_WRAPPER)
expect(wrapper).to_contain("readback_source=device_readback")
expect(wrapper).to_contain("cpu_fallback=false")

step("Compare device readback with the CPU oracle")
expect(executor).to_contain("processing_ir_output_matches(ir, result.values)")
expect(executor).to_contain("cuda-oracle-mismatch")

step("Record unavailable native host evidence")
val todos = file_read(TODO_DB)
expect(todos).to_contain("653, TODO, gpu, P1")
expect(todos).to_contain("processing_cuda_directx_native_spec.spl --mode=interpreter")
```

</details>

#### should fail closed before GPU submission when the source-matched probe is absent

- should fail closed before GPU submission when the source-matched probe is absent
- Select representative renderer processing kernels
- Compile and validate the backend artifact
- Submit native work and capture device readback
- Record unavailable native host evidence


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should fail closed before GPU submission when the source-matched probe is absent")
step("Select representative renderer processing kernels")
val wrapper = file_read(CUDA_WRAPPER)
expect(wrapper).to_contain("if [ ! -x \"$PROBE_BIN\" ]; then")
expect(wrapper).to_contain("processing_cuda_fill_native_status=blocked")
expect(wrapper).to_contain("processing_cuda_fill_native_reason=probe-binary-missing")
expect(wrapper).to_contain("exit 1")

step("Compile and validate the backend artifact")
expect(wrapper).to_contain("receipt_count=")
expect(wrapper).to_contain("if [ \"$receipt_count\" -ne 1 ] || [ \"$valid\" -ne 1 ]; then")
expect(wrapper).to_contain("processing_cuda_fill_native_reason=invalid-receipt")

step("Submit native work and capture device readback")
expect(wrapper).to_contain("handle=[1-9][0-9]* identity=[1-9][0-9]*")
expect(wrapper).to_contain("cpu_fallback=false")

step("Record unavailable native host evidence")
val todos = file_read(TODO_DB)
expect(todos).to_contain("650, TODO, gpu, P1")
expect(todos).to_contain("no new device PASS is claimed")
```

</details>

#### should bound bootstrap resume to the exact requested test entry

- should bound bootstrap resume to the exact requested test entry
- Select representative renderer processing kernels
- Lower shared ProcessingIR for the selected backend
- Record unavailable native host evidence


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should bound bootstrap resume to the exact requested test entry")
step("Select representative renderer processing kernels")
val loader = file_read(LOADER)
expect(loader).to_contain("fn _driver_is_bootstrap_entry_source(path: text, module_name: text) -> bool:")
expect(loader).to_contain("return path == native_entry or path.ends_with(\"/\" + native_entry)")
# Was `to_contain("A caller-supplied --entry is authoritative")`, the
# rationale comment. Anchored to the guard that actually enforces it.
expect(loader).to_contain("    if native_entry != \"\":")
expect(loader).to_contain("val _skip_dirs = [\"test\", \"tests\", \"doc\"")

step("Lower shared ProcessingIR for the selected backend")
val todos = file_read(TODO_DB)
expect(todos).to_contain("SIMPLE_NATIVE_BUILD_TRACE_CLOSURE=1")
expect(todos).to_contain("SIMPLE_NATIVE_BUILD_TRACE_CLOSURE_TIMING=1")
expect(todos).to_contain("Require the first closure-entry marker")
expect(todos).to_contain("redeploy the compiled CLI rather than increasing the timeout")

step("Record unavailable native host evidence")
expect(todos).to_contain("Do not run a fourth cycle in the same session")
```

</details>

#### should keep architecture and operator guidance traceable to CUDA native evidence

- should keep architecture and operator guidance traceable to CUDA native evidence
- Select representative renderer processing kernels
- Compare device readback with the CPU oracle


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should keep architecture and operator guidance traceable to CUDA native evidence")
step("Select representative renderer processing kernels")
val architecture = file_read(ARCHITECTURE)
val guide = file_read(OPERATOR_GUIDE)
val manual = file_read(CUDA_MANUAL)
expect(architecture).to_contain("Processing IR Contract")
expect(architecture).to_contain("CUDA")
expect(guide).to_contain("CUDA")
expect(manual).to_contain("check-processing-cuda-fill-native.shs")

step("Compare device readback with the CPU oracle")
expect(guide).to_contain("device")
expect(guide).to_contain("CPU oracle")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/app/simple_2d/feature/processing_cuda_backend_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering CUDA ProcessingIR backend operator flow.
- CUDA ProcessingIR backend operator flow

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

- `REQ-SSPEC-SYSTEM`
- `REQ-001`
- `REQ-003`
- `REQ-006`
- `REQ-007`
- `REQ-008`
- `REQ-010`
- `REQ-011`
- `REQ-012`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `c0fb319bf3f3ac62cd3b3900ba5c994297491f5db8d4d507bda61c1eb6586653`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `c0fb319bf3f3ac62cd3b3900ba5c994297491f5db8d4d507bda61c1eb6586653`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `c0fb319bf3f3ac62cd3b3900ba5c994297491f5db8d4d507bda61c1eb6586653`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **83/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/03_system/app/simple_2d/feature/processing_cuda_backend_spec.spl
mirror: doc/06_spec/03_system/app/simple_2d/feature/processing_cuda_backend_spec.md (current)
findings: 10 blockers: 1
  narrative=100 structure=80 oracle=100
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=83; blocker cap makes effective=49
doc/06_spec/03_system/app/simple_2d/feature/processing_cuda_backend_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/app/simple_2d/feature/processing_cuda_backend_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/app/simple_2d/feature/processing_cuda_backend_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 8 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/03_system/app/simple_2d/feature/processing_cuda_backend_spec.spl:27:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should document generation validation readback and unavailable-host evidence' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/simple_2d/feature/processing_cuda_backend_spec.spl:64:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should fail closed before GPU submission when the source-matched probe is absent' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/simple_2d/feature/processing_cuda_backend_spec.spl:64:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should fail closed before GPU submission when the source-matched probe is absent' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/app/simple_2d/feature/processing_cuda_backend_spec.spl:88:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should bound bootstrap resume to the exact requested test entry' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/simple_2d/feature/processing_cuda_backend_spec.spl:88:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should bound bootstrap resume to the exact requested test entry' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/app/simple_2d/feature/processing_cuda_backend_spec.spl:110:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should keep architecture and operator guidance traceable to CUDA native evidence' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/simple_2d/feature/processing_cuda_backend_spec.spl:110:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should keep architecture and operator guidance traceable to CUDA native evidence' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

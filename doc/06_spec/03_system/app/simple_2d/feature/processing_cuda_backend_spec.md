# processing_cuda_backend_spec

> Verifies the processing cuda backend behaviour end to end so maintainers of this

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# processing_cuda_backend_spec

Verifies the processing cuda backend behaviour end to end so maintainers of this

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/app/simple_2d/feature/processing_cuda_backend_spec.spl` |
| Updated | 2026-08-22 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Verifies the processing cuda backend behaviour end to end so maintainers of this
component and reviewers of its spec share one pinned definition.
## Operator workflow
Run `bin/simple test <this spec>`; read the per-scenario verdicts in
the `Results:` summary. Each scenario asserts an observable outcome.
## Compatibility and limitations
Covers the currently shipped behaviour only; performance, stress and
unrelated sibling features are out of scope.

## Scenarios

### CUDA ProcessingIR backend operator flow

#### should document generation validation readback and unavailable-host evidence

- Verify: should document generation validation readback and unavailable-host evidence
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
# @req: REQ-001 REQ-003 REQ-006 REQ-007 REQ-008 REQ-010 REQ-011 REQ-012
step("Verify: should document generation validation readback and unavailable-host evidence")
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

- Verify: should fail closed before GPU submission when the source-matched probe is absent
- Select representative renderer processing kernels
- Compile and validate the backend artifact
- Submit native work and capture device readback
- Record unavailable native host evidence


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-001 REQ-003 REQ-006 REQ-007 REQ-008 REQ-010 REQ-011 REQ-012
step("Verify: should fail closed before GPU submission when the source-matched probe is absent")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
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

- Verify: should bound bootstrap resume to the exact requested test entry
- Select representative renderer processing kernels
- Lower shared ProcessingIR for the selected backend
- Record unavailable native host evidence


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-001 REQ-003 REQ-006 REQ-007 REQ-008 REQ-010 REQ-011 REQ-012
step("Verify: should bound bootstrap resume to the exact requested test entry")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
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

- Verify: should keep architecture and operator guidance traceable to CUDA native evidence
- Select representative renderer processing kernels
- Compare device readback with the CPU oracle


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-001 REQ-003 REQ-006 REQ-007 REQ-008 REQ-010 REQ-011 REQ-012
step("Verify: should keep architecture and operator guidance traceable to CUDA native evidence")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
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

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `74f88c5a60ec121b21731c6159ef070d311905ff4f141b4191e6f8e693aac93e`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `74f88c5a60ec121b21731c6159ef070d311905ff4f141b4191e6f8e693aac93e`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `74f88c5a60ec121b21731c6159ef070d311905ff4f141b4191e6f8e693aac93e`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **91/100**; effective score: **91/100**; blockers: **0**.

SSpec documentization score: 91/100
source: test/03_system/app/simple_2d/feature/processing_cuda_backend_spec.spl
mirror: doc/06_spec/03_system/app/simple_2d/feature/processing_cuda_backend_spec.md (current)
findings: 7 blockers: 0
  narrative=100 structure=80 oracle=100
  traceability=100 evidence=85 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/app/simple_2d/feature/processing_cuda_backend_spec.md:1:1: warning SSDOC-EVD-002 [evidence] (-15): source steps are not visible in the generated manual
  why: Source tokens alone do not prove reader-visible workflow structure.
  improve: Use supported literal step calls and regenerate the manual.
doc/06_spec/03_system/app/simple_2d/feature/processing_cuda_backend_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/app/simple_2d/feature/processing_cuda_backend_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: assumptions/preconditions, traceability, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/app/simple_2d/feature/processing_cuda_backend_spec.spl:37:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should document generation validation readback and unavailable-host evidence' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/simple_2d/feature/processing_cuda_backend_spec.spl:74:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should fail closed before GPU submission when the source-matched probe is absent' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/simple_2d/feature/processing_cuda_backend_spec.spl:99:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should bound bootstrap resume to the exact requested test entry' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/simple_2d/feature/processing_cuda_backend_spec.spl:122:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should keep architecture and operator guidance traceable to CUDA native evidence' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->

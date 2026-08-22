# gpu_renderer_processing_backends_spec

> Verifies the gpu renderer processing backends behaviour end to end so maintainers of this

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# gpu_renderer_processing_backends_spec

Verifies the gpu renderer processing backends behaviour end to end so maintainers of this

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/app/simple_2d/feature/gpu_renderer_processing_backends_spec.spl` |
| Updated | 2026-08-22 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Verifies the gpu renderer processing backends behaviour end to end so maintainers of this
component and reviewers of its spec share one pinned definition.
## Operator workflow
Run `bin/simple test <this spec>`; read the per-scenario verdicts in
the `Results:` summary. Each scenario asserts an observable outcome.
## Compatibility and limitations
Covers the currently shipped behaviour only; performance, stress and
unrelated sibling features are out of scope.

## Scenarios

### GPU renderer ProcessingIR Vulkan backend

#### should validate SPIR-V and return device-origin FillRect parity

- Verify: should validate SPIR-V and return device-origin FillRect parity
- Select representative renderer processing kernels
   - Expected: processing_backend_host_probe(ProcessingBackendTarget.VulkanSpirv) equals `vulkan-spirv`
- Lower shared ProcessingIR for the selected backend
   - Expected: artifact.valid is true
   - Expected: artifact.format equals `spirv`
- Translate drawing access for the destination backend
- Compile and validate the backend artifact
   - Expected: structural.artifact_valid is true
   - Expected: rt_file_write_bytes(path, artifact.binary) is true
   - Expected: status equals `0)  # oracle: pinned constant asserted by this scenario`
   - Expected: stderr equals ``
- Submit native work and capture device readback
   - Expected: readback.submitted is true
   - Expected: readback.device_origin is true
- Compare device readback with the CPU oracle
   - Expected: readback.oracle_match is true
   - Expected: check_processing_backend_oracle_parity(ir, readback) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 34 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-001 REQ-002 REQ-006 REQ-007 REQ-008 REQ-010 REQ-011
step("Verify: should validate SPIR-V and return device-origin FillRect parity")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
step("Select representative renderer processing kernels")
val ir = processing_ir_fill_rect_u32(16, 16, 16, 2, 3, 6, 5, 0xff3366ccu32)
expect(processing_backend_host_probe(ProcessingBackendTarget.VulkanSpirv)).to_equal("vulkan-spirv")

step("Lower shared ProcessingIR for the selected backend")
val artifact = compile_processing_backend_artifact(ir, ProcessingBackendTarget.VulkanSpirv)
expect(artifact.valid).to_equal(true)
expect(artifact.format).to_equal("spirv")
expect(artifact.binary.len()).to_be_greater_than(20)

step("Translate drawing access for the destination backend")
expect(artifact.semantic_key).to_contain("x=2|y=3|rect_width=6|rect_height=5")

step("Compile and validate the backend artifact")
val structural = validate_processing_backend_artifact(ir, artifact)
expect(structural.artifact_valid).to_equal(true)
val path = "/tmp/simple_processing_fill_rect_u32.spv"
expect(rt_file_write_bytes(path, artifact.binary)).to_equal(true)
val (_stdout, stderr, status) = rt_process_run("spirv-val", ["--target-env", "vulkan1.1", path])
expect(status).to_equal(0)  # oracle: pinned constant asserted by this scenario
expect(stderr).to_equal("")

step("Submit native work and capture device readback")
val readback = run_processing_backend_device_probe(ir, artifact)
expect(readback.submitted).to_equal(true)
expect(readback.device_origin).to_equal(true)
expect(readback.device_identity).to_be_greater_than(0)

step("Compare device readback with the CPU oracle")
expect(readback.oracle_match).to_equal(true)
expect(check_processing_backend_oracle_parity(ir, readback)).to_equal(true)
```

</details>

#### should preserve a one-pixel half-open drawing edge in the shared oracle

- Verify: should preserve a one-pixel half-open drawing edge in the shared oracle
- Select the smallest valid renderer drawing kernel
   - Expected: artifact.valid is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-001 REQ-002 REQ-006 REQ-007 REQ-008 REQ-010 REQ-011
step("Verify: should preserve a one-pixel half-open drawing edge in the shared oracle")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
step("Select the smallest valid renderer drawing kernel")
val ir = processing_ir_fill_rect_u32(3, 2, 3, 2, 1, 1, 1, 0xff010203u32)
val artifact = compile_processing_backend_artifact(ir, ProcessingBackendTarget.VulkanSpirv)
expect(artifact.valid).to_equal(true)
expect(artifact.semantic_key).to_contain("x=2|y=1|rect_width=1|rect_height=1")
```

</details>

#### should reject an out-of-bounds drawing kernel before submission

- Verify: should reject an out-of-bounds drawing kernel before submission
- Reject unsupported or lossy drawing access
   - Expected: artifact.valid is false
   - Expected: artifact.reason equals `drawing-rectangle-out-of-bounds`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-001 REQ-002 REQ-006 REQ-007 REQ-008 REQ-010 REQ-011
step("Verify: should reject an out-of-bounds drawing kernel before submission")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
step("Reject unsupported or lossy drawing access")
val ir = processing_ir_fill_rect_u32(3, 2, 3, 2, 1, 2, 1, 7u32)
val artifact = compile_processing_backend_artifact(ir, ProcessingBackendTarget.VulkanSpirv)
expect(artifact.valid).to_equal(false)
expect(artifact.reason).to_equal("drawing-rectangle-out-of-bounds")
```

</details>

#### should accept a complete immutable artifact contract

- Verify: should accept a complete immutable artifact contract
- Compile and validate the backend artifact
   - Expected: evidence.artifact_valid is true
   - Expected: evidence.reason equals `ok`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-001 REQ-002 REQ-006 REQ-007 REQ-008 REQ-010 REQ-011
step("Verify: should accept a complete immutable artifact contract")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
step("Compile and validate the backend artifact")
val ir = processing_ir_fill_u32(8, 9u32)
val artifact = compile_processing_backend_artifact(ir, ProcessingBackendTarget.VulkanSpirv)
val evidence = validate_processing_backend_artifact(ir, artifact)
expect(evidence.artifact_valid).to_equal(true)
expect(evidence.reason).to_equal("ok")
```

</details>

#### should invalidate an artifact when ProcessingIR semantics change

- Verify: should invalidate an artifact when ProcessingIR semantics change
- Invalidate cached material after a semantic change
   - Expected: evidence.artifact_valid is false
   - Expected: evidence.reason equals `artifact-semantic-key-mismatch`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-001 REQ-002 REQ-006 REQ-007 REQ-008 REQ-010 REQ-011
step("Verify: should invalidate an artifact when ProcessingIR semantics change")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
step("Invalidate cached material after a semantic change")
val original = processing_ir_fill_u32(8, 9u32)
val changed = processing_ir_fill_u32(8, 10u32)
val artifact = compile_processing_backend_artifact(original, ProcessingBackendTarget.VulkanSpirv)
val evidence = validate_processing_backend_artifact(changed, artifact)
expect(evidence.artifact_valid).to_equal(false)
expect(evidence.reason).to_equal("artifact-semantic-key-mismatch")
```

</details>

#### should not promote a missing artifact payload to device evidence

- Verify: should not promote a missing artifact payload to device evidence
- Fail closed before native device access
   - Expected: readback.submitted is false
   - Expected: readback.device_origin is false
   - Expected: readback.reason equals `artifact-payload-missing`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-001 REQ-002 REQ-006 REQ-007 REQ-008 REQ-010 REQ-011
step("Verify: should not promote a missing artifact payload to device evidence")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
step("Fail closed before native device access")
val ir = processing_ir_fill_u32(8, 9u32)
val artifact = ProcessingBackendArtifact(target: ProcessingBackendTarget.VulkanSpirv,
    format: "spirv", entry_point: "main", source: "", binary: [],
    semantic_key: processing_backend_semantic_key(ir, ProcessingBackendTarget.VulkanSpirv),
    valid: true, reason: "ok")
val readback = run_processing_backend_device_probe(ir, artifact)
expect(readback.submitted).to_equal(false)
expect(readback.device_origin).to_equal(false)
expect(readback.reason).to_equal("artifact-payload-missing")
```

</details>

#### should document startup hot paths cache invalidation and resource targets

- Verify: should document startup hot paths cache invalidation and resource targets
- Review the processing architecture contract


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-001 REQ-002 REQ-006 REQ-007 REQ-008 REQ-010 REQ-011
step("Verify: should document startup hot paths cache invalidation and resource targets")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
step("Review the processing architecture contract")
val architecture = rt_file_read_text("doc/04_architecture/compiler/backend/processing_backend.md")
expect(architecture).to_contain("Startup probes")
expect(architecture).to_contain("hot path")
expect(architecture).to_contain("semantic key")
expect(architecture).to_contain("below 1 ms")
expect(architecture).to_contain("4 MiB")
```

</details>

#### should document exact compiler and production web evidence commands

- Verify: should document exact compiler and production web evidence commands
- Review the operator evidence commands


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-001 REQ-002 REQ-006 REQ-007 REQ-008 REQ-010 REQ-011
step("Verify: should document exact compiler and production web evidence commands")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
step("Review the operator evidence commands")
val guide = rt_file_read_text("doc/07_guide/compiler/backends/processing_backend.md")
val manual = rt_file_read_text("doc/06_spec/03_system/app/simple_2d/feature/gpu_renderer_processing_backends_spec.md")
expect(guide).to_contain("vulkan_compiler_fill_rect_live_spec.spl")
expect(manual).to_contain("web_vulkan_production_readback_spec.spl")
expect(manual).to_contain("device_readback")
```

</details>

#### should retain cooperative ownership and final review requirements

- Verify: should retain cooperative ownership and final review requirements
- Confirm unrelated work and generated manuals remain review-gated


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-001 REQ-002 REQ-006 REQ-007 REQ-008 REQ-010 REQ-011
step("Verify: should retain cooperative ownership and final review requirements")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
step("Confirm unrelated work and generated manuals remain review-gated")
val state = rt_file_read_text(".spipe/gpu_renderer_processing_backends/state.md")
expect(state).to_contain("Merge owner and final normal/highest-capability reviewer: root Codex agent")
expect(state).to_contain("Generated-manual review owner: root Codex agent")
expect(state).to_contain("Integration preserves unrelated dirty work")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `2f6b0944a09acf5e45db56e941afbd365f3ce6d139ad3d4cfd69ad93fa4da7e5`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `2f6b0944a09acf5e45db56e941afbd365f3ce6d139ad3d4cfd69ad93fa4da7e5`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `2f6b0944a09acf5e45db56e941afbd365f3ce6d139ad3d4cfd69ad93fa4da7e5`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/03_system/app/simple_2d/feature/gpu_renderer_processing_backends_spec.spl
mirror: doc/06_spec/03_system/app/simple_2d/feature/gpu_renderer_processing_backends_spec.md (current)
findings: 9 blockers: 0
  narrative=100 structure=70 oracle=100
  traceability=100 evidence=85 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/app/simple_2d/feature/gpu_renderer_processing_backends_spec.md:1:1: warning SSDOC-EVD-002 [evidence] (-15): source steps are not visible in the generated manual
  why: Source tokens alone do not prove reader-visible workflow structure.
  improve: Use supported literal step calls and regenerate the manual.
doc/06_spec/03_system/app/simple_2d/feature/gpu_renderer_processing_backends_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/app/simple_2d/feature/gpu_renderer_processing_backends_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: assumptions/preconditions, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/app/simple_2d/feature/gpu_renderer_processing_backends_spec.spl:35:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should validate SPIR-V and return device-origin FillRect parity' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/simple_2d/feature/gpu_renderer_processing_backends_spec.spl:71:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should preserve a one-pixel half-open drawing edge in the shared oracle' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/simple_2d/feature/gpu_renderer_processing_backends_spec.spl:81:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should reject an out-of-bounds drawing kernel before submission' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/simple_2d/feature/gpu_renderer_processing_backends_spec.spl:91:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should accept a complete immutable artifact contract' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/simple_2d/feature/gpu_renderer_processing_backends_spec.spl:102:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should invalidate an artifact when ProcessingIR semantics change' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/simple_2d/feature/gpu_renderer_processing_backends_spec.spl:114:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should not promote a missing artifact payload to device evidence' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->

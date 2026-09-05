# backend_contract_spec

> Shared ProcessingIR backend artifacts fail closed and invalidate on drawing semantics.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# backend_contract_spec

Shared ProcessingIR backend artifacts fail closed and invalidate on drawing semantics.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/processing/backend_contract_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Shared ProcessingIR backend artifacts fail closed and invalidate on drawing semantics.

## Scenarios

### shared ProcessingIR backend contract

#### should use one target vocabulary and deterministic artifact formats

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- should use one target vocabulary and deterministic artifact formats
- Select representative renderer processing kernels
   - Expected: processing_backend_target_name(ProcessingBackendTarget.VulkanSpirv) equals `vulkan-spirv`
   - Expected: processing_backend_target_format(ProcessingBackendTarget.VulkanSpirv) equals `spirv`
   - Expected: processing_backend_target_format(ProcessingBackendTarget.CudaPtx) equals `ptx`
   - Expected: processing_backend_target_format(ProcessingBackendTarget.MetalMsl) equals `msl`
   - Expected: processing_backend_target_format(ProcessingBackendTarget.DirectXHlsl) equals `hlsl`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("should use one target vocabulary and deterministic artifact formats")
step("Select representative renderer processing kernels")
val ir = processing_ir_fill_u32(8, 42u32)
expect(processing_backend_target_name(ProcessingBackendTarget.VulkanSpirv)).to_equal("vulkan-spirv")
expect(processing_backend_target_format(ProcessingBackendTarget.VulkanSpirv)).to_equal("spirv")
expect(processing_backend_target_format(ProcessingBackendTarget.CudaPtx)).to_equal("ptx")
expect(processing_backend_target_format(ProcessingBackendTarget.MetalMsl)).to_equal("msl")
expect(processing_backend_target_format(ProcessingBackendTarget.DirectXHlsl)).to_equal("hlsl")
expect(processing_backend_semantic_key(ir, ProcessingBackendTarget.VulkanSpirv)).to_contain("processing-ir-v2")
```

</details>

#### should reject invalid payload format and semantic identity

- should reject invalid payload format and semantic identity
- Lower shared ProcessingIR for the selected backend
   - Expected: processing_backend_artifact_validate(ir, wrong_format) equals `artifact-format-mismatch`
   - Expected: processing_backend_artifact_validate(ir, stale) equals `artifact-semantic-key-mismatch`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("should reject invalid payload format and semantic identity")
step("Lower shared ProcessingIR for the selected backend")
val ir = processing_ir_fill_u32(8, 42u32)
val wrong_format = ProcessingBackendArtifact(target: ProcessingBackendTarget.VulkanSpirv,
    format: "ptx", entry_point: "processing_fill_u32", source: "payload", binary: [],
    semantic_key: processing_backend_semantic_key(ir, ProcessingBackendTarget.VulkanSpirv),
    valid: true, reason: "ok")
expect(processing_backend_artifact_validate(ir, wrong_format)).to_equal("artifact-format-mismatch")
val stale = ProcessingBackendArtifact(target: ProcessingBackendTarget.VulkanSpirv,
    format: "spirv", entry_point: "processing_fill_u32", source: "payload", binary: [],
    semantic_key: "stale", valid: true, reason: "ok")
expect(processing_backend_artifact_validate(ir, stale)).to_equal("artifact-semantic-key-mismatch")
```

</details>

#### should preserve half-open row-major drawing coordinates in the CPU oracle

- should preserve half-open row-major drawing coordinates in the CPU oracle
- Translate drawing access for the destination backend
   - Expected: processing_ir_validate(draw).reason equals `ok`
   - Expected: pixels equals `[`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("should preserve half-open row-major drawing coordinates in the CPU oracle")
step("Translate drawing access for the destination backend")
val draw = processing_ir_fill_rect_u32(4, 3, 4, 1, 1, 2, 1, 0xaabbccddu32)
expect(processing_ir_validate(draw).reason).to_equal("ok")
val pixels = processing_ir_cpu_execute(draw)
expect(pixels).to_equal([
    0u32, 0u32, 0u32, 0u32,
    0u32, 0xaabbccddu32, 0xaabbccddu32, 0u32,
    0u32, 0u32, 0u32, 0u32])
val moved = processing_ir_fill_rect_u32(4, 3, 4, 2, 1, 1, 1, 0xaabbccddu32)
expect(processing_backend_semantic_key(draw, ProcessingBackendTarget.VulkanSpirv) ==
    processing_backend_semantic_key(moved, ProcessingBackendTarget.VulkanSpirv)).to_equal(false)
```

</details>

#### should reject out-of-bounds drawing access

- should reject out-of-bounds drawing access
   - Expected: processing_ir_validate(draw).reason equals `drawing-rectangle-out-of-bounds`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("should reject out-of-bounds drawing access")
val draw = processing_ir_fill_rect_u32(4, 3, 4, 3, 1, 2, 1, 7u32)
expect(processing_ir_validate(draw).reason).to_equal("drawing-rectangle-out-of-bounds")
```

</details>

#### should exercise success branches for source and binary payloads

- should exercise success branches for source and binary payloads
- Exercise success branches
   - Expected: processing_backend_artifact_validate(ir, source) equals `ok`
   - Expected: processing_backend_artifact_validate(ir, binary) equals `ok`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("should exercise success branches for source and binary payloads")
step("Exercise success branches")
val ir = processing_ir_fill_u32(4, 3u32)
val source = ProcessingBackendArtifact(target: ProcessingBackendTarget.CudaPtx,
    format: "ptx", entry_point: "processing_fill_u32", source: "ptx", binary: [],
    semantic_key: processing_backend_semantic_key(ir, ProcessingBackendTarget.CudaPtx),
    valid: true, reason: "ok")
val binary = ProcessingBackendArtifact(target: ProcessingBackendTarget.VulkanSpirv,
    format: "spirv", entry_point: "main", source: "", binary: [3u8, 2u8, 35u8, 7u8],
    semantic_key: processing_backend_semantic_key(ir, ProcessingBackendTarget.VulkanSpirv),
    valid: true, reason: "ok")
expect(processing_backend_artifact_validate(ir, source)).to_equal("ok")
expect(processing_backend_artifact_validate(ir, binary)).to_equal("ok")
```

</details>

#### should exercise boundary branches for drawing extents and size

- should exercise boundary branches for drawing extents and size
- Exercise boundary branches
   - Expected: processing_ir_validate(invalid_extent).reason equals `invalid-drawing-extent`
   - Expected: processing_ir_validate(wrong_size).reason equals `drawing-size-mismatch`
   - Expected: processing_ir_validate(invalid_rect).reason equals `invalid-drawing-rectangle`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("should exercise boundary branches for drawing extents and size")
step("Exercise boundary branches")
val invalid_extent = ProcessingIr(op: PROCESSING_IR_OP_FILL_RECT_U32,
    element_count: 4, value: 1u32, width: 4, height: 1, stride: 3,
    x: 0, y: 0, rect_width: 1, rect_height: 1)
val wrong_size = ProcessingIr(op: PROCESSING_IR_OP_FILL_RECT_U32,
    element_count: 5, value: 1u32, width: 4, height: 1, stride: 4,
    x: 0, y: 0, rect_width: 1, rect_height: 1)
val invalid_rect = ProcessingIr(op: PROCESSING_IR_OP_FILL_RECT_U32,
    element_count: 4, value: 1u32, width: 4, height: 1, stride: 4,
    x: -1, y: 0, rect_width: 1, rect_height: 1)
expect(processing_ir_validate(invalid_extent).reason).to_equal("invalid-drawing-extent")
expect(processing_ir_validate(wrong_size).reason).to_equal("drawing-size-mismatch")
expect(processing_ir_validate(invalid_rect).reason).to_equal("invalid-drawing-rectangle")
```

</details>

#### should exercise rejection branches for invalid artifact states

- should exercise rejection branches for invalid artifact states
- Exercise rejection branches
   - Expected: processing_backend_artifact_validate(ir, invalid) equals `artifact-invalid`
   - Expected: processing_backend_artifact_validate(ir, missing_entry) equals `artifact-payload-missing`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("should exercise rejection branches for invalid artifact states")
step("Exercise rejection branches")
val ir = processing_ir_fill_u32(4, 3u32)
val invalid = ProcessingBackendArtifact(target: ProcessingBackendTarget.VulkanSpirv,
    format: "spirv", entry_point: "main", source: "", binary: [1u8],
    semantic_key: processing_backend_semantic_key(ir, ProcessingBackendTarget.VulkanSpirv),
    valid: false, reason: "")
val missing_entry = ProcessingBackendArtifact(target: ProcessingBackendTarget.VulkanSpirv,
    format: "spirv", entry_point: "", source: "", binary: [1u8],
    semantic_key: processing_backend_semantic_key(ir, ProcessingBackendTarget.VulkanSpirv),
    valid: true, reason: "ok")
expect(processing_backend_artifact_validate(ir, invalid)).to_equal("artifact-invalid")
expect(processing_backend_artifact_validate(ir, missing_entry)).to_equal("artifact-payload-missing")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
- `REQ-001`
- `REQ-006`
- `REQ-007`
- `REQ-011`
- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `7cf1e29d64b683419597933fb198ac6ee00ec92ea3934eb4f1004d1ac05684f0`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `7cf1e29d64b683419597933fb198ac6ee00ec92ea3934eb4f1004d1ac05684f0`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `7cf1e29d64b683419597933fb198ac6ee00ec92ea3934eb4f1004d1ac05684f0`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **82/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/lib/common/processing/backend_contract_spec.spl
mirror: doc/06_spec/01_unit/lib/common/processing/backend_contract_spec.md (current)
findings: 12 blockers: 1
  narrative=100 structure=70 oracle=100
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=82; blocker cap makes effective=49
doc/06_spec/01_unit/lib/common/processing/backend_contract_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/processing/backend_contract_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/processing/backend_contract_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 5 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/lib/common/processing/backend_contract_spec.spl:18:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should use one target vocabulary and deterministic artifact formats' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/lib/common/processing/backend_contract_spec.spl:18:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should use one target vocabulary and deterministic artifact formats' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/processing/backend_contract_spec.spl:30:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should reject invalid payload format and semantic identity' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/lib/common/processing/backend_contract_spec.spl:30:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should reject invalid payload format and semantic identity' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/processing/backend_contract_spec.spl:45:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should preserve half-open row-major drawing coordinates in the CPU oracle' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/lib/common/processing/backend_contract_spec.spl:45:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should preserve half-open row-major drawing coordinates in the CPU oracle' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/processing/backend_contract_spec.spl:60:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should reject out-of-bounds drawing access' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/lib/common/processing/backend_contract_spec.spl:66:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should exercise success branches for source and binary payloads' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/lib/common/processing/backend_contract_spec.spl:82:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should exercise boundary branches for drawing extents and size' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->

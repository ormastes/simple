# processing_metal_branch_coverage_spec

> Purpose: This spec proves measured Metal processing branch coverage.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# processing_metal_branch_coverage_spec

Purpose: This spec proves measured Metal processing branch coverage.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/02_integration/rendering/processing_metal_branch_coverage_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: This spec proves measured Metal processing branch coverage.
Audience: Maintainers of the Simple integration suite reviewing this behavior.

## Scenarios

### measured Metal processing branch coverage

#### should exercise success branches

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- Exercise success branches
   - Expected: artifact.reason equals `ok`
   - Expected: validate_processing_backend_artifact(fill, artifact).reason equals `ok`
   - Expected: emulated.reason equals `ok`
   - Expected: emulated.dispatch_count equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-004
# @req: REQ-005
# @req: REQ-006
# @req: REQ-007
# @req: REQ-011
# @req: REQ-013
# @req: REQ-015
step("Exercise success branches")
val fill = processing_ir_fill_u32(8, 7u32)
val artifact = compile_processing_backend_artifact(fill, ProcessingBackendTarget.MetalMsl)
expect(artifact.reason).to_equal("ok")
expect(validate_processing_backend_artifact(fill, artifact).reason).to_equal("ok")
val emulated = processing_metal_emulate(fill, artifact, zeros(8), 0, 1, 2, 8, 1, 0)
expect(emulated.reason).to_equal("ok")
expect(emulated.dispatch_count).to_equal(1)
expect(processing_metal_device_identity("qualified-metal", 1024)).to_be_greater_than(0)
```

</details>

#### should exercise boundary branches

- should exercise boundary branches
- Exercise boundary branches
   - Expected: processing_metal_drawing_validate(edge) equals `ok`
   - Expected: processing_metal_drawing_cpu_oracle(edge) equals `[0xFFFFFFFFu32]`
   - Expected: processing_metal_device_identity("", 1024) equals `0`
   - Expected: processing_metal_device_identity("qualified-metal", 0) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("should exercise boundary branches")
step("Exercise boundary branches")
val edge = processing_metal_drawing_fill_rect(1, 1, 0, 0, 1, 1, 0xFFFFFFFFu32)
expect(processing_metal_drawing_validate(edge)).to_equal("ok")
expect(processing_metal_drawing_cpu_oracle(edge)).to_equal([0xFFFFFFFFu32])
expect(processing_metal_device_identity("", 1024)).to_equal(0)
expect(processing_metal_device_identity("qualified-metal", 0)).to_equal(0)
```

</details>

#### should exercise rejection branches

- should exercise rejection branches
- Exercise rejection branches
   - Expected: processing_metal_source(invalid_ir) equals ``
   - Expected: compile_processing_backend_artifact(invalid_ir, ProcessingBackendTarget.MetalMsl).reason equals `unsupported-op`
   - Expected: processing_ir_execute_metal_artifact(invalid_ir, "", "").reason equals `unsupported-op`
   - Expected: processing_metal_drawing_validate(invalid_extent) equals `invalid-drawing-extent`
   - Expected: processing_metal_drawing_validate(overflow) equals `drawing-output-size-overflow`
   - Expected: processing_metal_drawing_validate(invalid_rect) equals `invalid-drawing-rectangle`
   - Expected: processing_metal_drawing_validate(out_of_bounds) equals `drawing-rectangle-out-of-bounds`
   - Expected: processing_metal_drawing_source(invalid_extent) equals ``
   - Expected: processing_metal_drawing_cpu_oracle(invalid_extent).len() equals `0`
   - Expected: processing_ir_execute_metal_artifact(fill, "", artifact.entry_point).reason equals `metal-artifact-source-mismatch`
   - Expected: processing_ir_execute_metal_artifact(fill, artifact.source, "wrong").reason equals `metal-artifact-entry-mismatch`
   - Expected: processing_ir_execute_metal_artifact(fill, artifact.source, artifact.entry_point).reason equals `metal-unavailable`
   - Expected: processing_metal_emulate(fill, wrong_target, zeros(8), 0, 1, 2, 8, 1, 0).reason equals `metal-emulator-target-mismatch`
   - Expected: processing_metal_emulate(invalid_ir, artifact, zeros(8), 0, 1, 2, 8, 1, 0).reason equals `unsupported-op`
   - Expected: processing_metal_emulate(fill, artifact, zeros(8), 0, 1, 2, 0, 1, 0).reason equals `metal-emulator-invalid-dispatch`
- Measure branch coverage
   - Expected: rejected_probe.reason equals `artifact-semantic-key-mismatch`
   - Expected: rejected_probe.device_identity equals `0`
   - Expected: rejected_probe.values.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 38 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("should exercise rejection branches")
step("Exercise rejection branches")
val invalid_ir = unsupported_ir()
expect(processing_metal_source(invalid_ir)).to_equal("")
expect(compile_processing_backend_artifact(invalid_ir, ProcessingBackendTarget.MetalMsl).reason).to_equal("unsupported-op")
expect(processing_ir_execute_metal_artifact(invalid_ir, "", "").reason).to_equal("unsupported-op")

val invalid_extent = processing_metal_drawing_fill_rect(0, 8, 0, 0, 1, 1, 1u32)
expect(processing_metal_drawing_validate(invalid_extent)).to_equal("invalid-drawing-extent")
val overflow = processing_metal_drawing_fill_rect(1048577, 1, 0, 0, 1, 1, 1u32)
expect(processing_metal_drawing_validate(overflow)).to_equal("drawing-output-size-overflow")
val invalid_rect = processing_metal_drawing_fill_rect(8, 8, -1, 0, 1, 1, 1u32)
expect(processing_metal_drawing_validate(invalid_rect)).to_equal("invalid-drawing-rectangle")
val out_of_bounds = processing_metal_drawing_fill_rect(8, 8, 7, 7, 2, 2, 1u32)
expect(processing_metal_drawing_validate(out_of_bounds)).to_equal("drawing-rectangle-out-of-bounds")
expect(processing_metal_drawing_source(invalid_extent)).to_equal("")
expect(processing_metal_drawing_cpu_oracle(invalid_extent).len()).to_equal(0)

val fill = processing_ir_fill_u32(8, 7u32)
val artifact = processing_metal_generate_artifact(fill)
expect(processing_ir_execute_metal_artifact(fill, "", artifact.entry_point).reason).to_equal("metal-artifact-source-mismatch")
expect(processing_ir_execute_metal_artifact(fill, artifact.source, "wrong").reason).to_equal("metal-artifact-entry-mismatch")
expect(processing_ir_execute_metal_artifact(fill, artifact.source, artifact.entry_point).reason).to_equal("metal-unavailable")

var wrong_target = artifact
wrong_target.target = ProcessingBackendTarget.CudaPtx
expect(processing_metal_emulate(fill, wrong_target, zeros(8), 0, 1, 2, 8, 1, 0).reason).to_equal("metal-emulator-target-mismatch")
expect(processing_metal_emulate(invalid_ir, artifact, zeros(8), 0, 1, 2, 8, 1, 0).reason).to_equal("unsupported-op")
expect(processing_metal_emulate(fill, artifact, zeros(8), 0, 1, 2, 0, 1, 0).reason).to_equal("metal-emulator-invalid-dispatch")

var invalid_artifact = artifact
invalid_artifact.semantic_key = "wrong"
val rejected_probe = run_processing_backend_device_probe(fill, invalid_artifact)
step("Measure branch coverage")
expect(rejected_probe.reason).to_equal("artifact-semantic-key-mismatch")
expect(rejected_probe.device_identity).to_equal(0)
expect(rejected_probe.values.len()).to_equal(0)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-INTEGRATION`
- `REQ-004`
- `REQ-005`
- `REQ-006`
- `REQ-007`
- `REQ-011`
- `REQ-013`
- `REQ-015`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `2bb159fb25a29d00df67f46de04e4c9e7f5c6a4eba6365df9290ba1ca07b8585`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `2bb159fb25a29d00df67f46de04e4c9e7f5c6a4eba6365df9290ba1ca07b8585`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `2bb159fb25a29d00df67f46de04e4c9e7f5c6a4eba6365df9290ba1ca07b8585`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **84/100**; effective score: **84/100**; blockers: **0**.

SSpec documentization score: 84/100
source: test/02_integration/rendering/processing_metal_branch_coverage_spec.spl
mirror: doc/06_spec/02_integration/rendering/processing_metal_branch_coverage_spec.md (current)
findings: 9 blockers: 0
  narrative=100 structure=85 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/02_integration/rendering/processing_metal_branch_coverage_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/02_integration/rendering/processing_metal_branch_coverage_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/02_integration/rendering/processing_metal_branch_coverage_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 6 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/02_integration/rendering/processing_metal_branch_coverage_spec.spl:39:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should exercise success branches' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/02_integration/rendering/processing_metal_branch_coverage_spec.spl:39:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should exercise success branches' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/02_integration/rendering/processing_metal_branch_coverage_spec.spl:57:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should exercise boundary branches' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/02_integration/rendering/processing_metal_branch_coverage_spec.spl:57:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should exercise boundary branches' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/02_integration/rendering/processing_metal_branch_coverage_spec.spl:67:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should exercise rejection branches' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/02_integration/rendering/processing_metal_branch_coverage_spec.spl:67:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should exercise rejection branches' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

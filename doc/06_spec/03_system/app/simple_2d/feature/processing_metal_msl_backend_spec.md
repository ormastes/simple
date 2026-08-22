# processing_metal_msl_backend_spec

> Verifies the processing metal msl backend behaviour end to end so maintainers of this

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# processing_metal_msl_backend_spec

Verifies the processing metal msl backend behaviour end to end so maintainers of this

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/app/simple_2d/feature/processing_metal_msl_backend_spec.spl` |
| Updated | 2026-08-22 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Verifies the processing metal msl backend behaviour end to end so maintainers of this
component and reviewers of its spec share one pinned definition.
## Operator workflow
Run `bin/simple test <this spec>`; read the per-scenario verdicts in
the `Results:` summary. Each scenario asserts an observable outcome.
## Compatibility and limitations
Covers the currently shipped behaviour only; performance, stress and
unrelated sibling features are out of scope.

## Scenarios

### Metal MSL renderer processing backend

#### should generate a deterministic host-independent ProcessingIR artifact

- Verify: should generate a deterministic host-independent ProcessingIR artifact
- Select representative renderer processing kernels
   - Expected: processing_backend_host_probe(ProcessingBackendTarget.MetalMsl) equals `metal-msl`
- Lower shared ProcessingIR for the selected backend
   - Expected: artifact.valid is true
- Translate drawing access for the destination backend
   - Expected: drawing_artifact.valid is true
   - Expected: processing_metal_drawing_cpu_oracle(draw).len() equals `64)  # oracle: pinned constant asserted by this scenario`
- Compile and validate the backend artifact
   - Expected: compilation.artifact_valid is true
   - Expected: compilation.reason equals `ok`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-001 REQ-004 REQ-005 REQ-006 REQ-007 REQ-008 REQ-010 REQ-011
step("Verify: should generate a deterministic host-independent ProcessingIR artifact")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val ir = processing_ir_fill_u32(64, 0xA1B2C3D4u32)
expect(processing_backend_host_probe(ProcessingBackendTarget.MetalMsl)).to_equal("metal-msl")

val artifact = compile_processing_backend_artifact(ir, ProcessingBackendTarget.MetalMsl)
expect(artifact.valid).to_equal(true)
expect(artifact.source).to_contain("processing_fill_u32")

val draw = processing_metal_drawing_fill_rect(8, 8, 2, 2, 4, 3, 0xFF3366CCu32)
val drawing_artifact = processing_metal_generate_drawing_artifact(draw)
expect(drawing_artifact.valid).to_equal(true)
expect(drawing_artifact.source).to_contain("processing_fill_rect")
expect(processing_metal_drawing_cpu_oracle(draw).len()).to_equal(64)  # oracle: pinned constant asserted by this scenario

val compilation = validate_processing_backend_artifact(ir, artifact)
expect(compilation.artifact_valid).to_equal(true)
expect(compilation.reason).to_equal("ok")
```

</details>

#### should require native device-origin readback and exact CPU oracle parity

**Manual warnings:**
- unused step metadata: Compare device readback with the CPU oracle (expected a following executable manual step)


- Verify: should require native device-origin readback and exact CPU oracle parity
- Record unavailable native host evidence
- Submit native work and capture device readback
   - Expected: evidence.submitted is true
   - Expected: evidence.device_origin is true
   - Expected: check_processing_backend_oracle_parity(ir, evidence) is true
   - Expected: evidence.reason equals `ok`


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-001 REQ-004 REQ-005 REQ-006 REQ-007 REQ-008 REQ-010 REQ-011
step("Verify: should require native device-origin readback and exact CPU oracle parity")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
if not is_macos():
    val blocked = processing_metal_native_blocked_row()
    expect_metal_native_blocked_contract(blocked)
    print("PROCESSING_METAL_NATIVE status={blocked.status} reason={blocked.reason} todo=652 resume={blocked.resume_command}\n")
    fail_test("BLOCKED Metal native FillU32 row: macOS Metal host required; resume under TODO 652")
    return

val ir = processing_ir_fill_u32(64, 0xA1B2C3D4u32)
val artifact = compile_processing_backend_artifact(ir, ProcessingBackendTarget.MetalMsl)

val evidence = run_processing_backend_device_probe(ir, artifact)
expect(evidence.submitted).to_equal(true)
expect(evidence.device_origin).to_equal(true)
expect(evidence.device_identity).to_be_greater_than(0)

expect(check_processing_backend_oracle_parity(ir, evidence)).to_equal(true)
expect(evidence.reason).to_equal("ok")
```

</details>

#### should preserve Metal-to-Metal fill rectangle coordinates and pixels

- Verify: should preserve Metal-to-Metal fill rectangle coordinates and pixels
   - Expected: generated.valid is true
   - Expected: readback.submitted is true
   - Expected: readback.device_origin is true
   - Expected: check_processing_backend_oracle_parity(draw, readback) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-001 REQ-004 REQ-005 REQ-006 REQ-007 REQ-008 REQ-010 REQ-011
step("Verify: should preserve Metal-to-Metal fill rectangle coordinates and pixels")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
if not is_macos():
    val blocked = processing_metal_native_blocked_row()
    expect_metal_native_blocked_contract(blocked)
    print("PROCESSING_METAL_DRAWING_NATIVE status={blocked.status} reason={blocked.reason} todo=652 resume={blocked.resume_command}\n")
    fail_test("BLOCKED Metal-to-Metal drawing row: macOS Metal host required; resume under TODO 652")
    return
val draw = processing_ir_fill_rect_u32(8, 8, 8, 2, 2, 4, 3, 0xFF3366CCu32)
val generated = compile_processing_backend_artifact(draw, ProcessingBackendTarget.MetalMsl)
expect(generated.valid).to_equal(true)
expect(generated.source).to_contain("p.stride")
val readback = run_processing_backend_device_probe(draw, generated)
expect(readback.submitted).to_equal(true)
expect(readback.device_origin).to_equal(true)
expect(readback.device_identity).to_be_greater_than(0)
expect(check_processing_backend_oracle_parity(draw, readback)).to_equal(true)
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

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `26a7237fbc5f362b6d060ed179de7d712d7bf9b112f4f778279065f7f71da5eb`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `26a7237fbc5f362b6d060ed179de7d712d7bf9b112f4f778279065f7f71da5eb`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `26a7237fbc5f362b6d060ed179de7d712d7bf9b112f4f778279065f7f71da5eb`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/app/simple_2d/feature/processing_metal_msl_backend_spec.spl
mirror: doc/06_spec/03_system/app/simple_2d/feature/processing_metal_msl_backend_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=85 oracle=100
  traceability=100 evidence=85 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/app/simple_2d/feature/processing_metal_msl_backend_spec.md:1:1: warning SSDOC-EVD-002 [evidence] (-15): source steps are not visible in the generated manual
  why: Source tokens alone do not prove reader-visible workflow structure.
  improve: Use supported literal step calls and regenerate the manual.
doc/06_spec/03_system/app/simple_2d/feature/processing_metal_msl_backend_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/app/simple_2d/feature/processing_metal_msl_backend_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: assumptions/preconditions, traceability, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/app/simple_2d/feature/processing_metal_msl_backend_spec.spl:88:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should generate a deterministic host-independent ProcessingIR artifact' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/simple_2d/feature/processing_metal_msl_backend_spec.spl:113:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should require native device-origin readback and exact CPU oracle parity' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/simple_2d/feature/processing_metal_msl_backend_spec.spl:138:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should preserve Metal-to-Metal fill rectangle coordinates and pixels' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->

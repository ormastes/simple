# Processing Metal Msl Backend Specification

> Tests covering Metal MSL renderer processing backend.

## Host-independent NFR gate

Run `SIMPLE_LIB=src bin/simple test test/05_perf/processing/metal_msl_generation_perf_spec.spl --mode=interpreter` with the admitted pure-selfhost binary. It requires 512 deterministic generations, average latency below 10 ms, procfs `VmHWM` incremental peak RSS below 8 MiB, and semantic-key invalidation for changed ProcessingIR values/counts. Seed-runner measurements are diagnostic only.

# Processing Metal Msl Backend Specification

## Scenarios

### Metal MSL renderer processing backend

#### should generate a deterministic host-independent ProcessingIR artifact

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- should generate a deterministic host-independent ProcessingIR artifact
- Select representative renderer processing kernels
   - Expected: processing_backend_host_probe(ProcessingBackendTarget.MetalMsl) equals `metal-msl`
- Lower shared ProcessingIR for the selected backend
   - Expected: artifact.valid is true
- Translate drawing access for the destination backend
   - Expected: drawing_artifact.valid is true
   - Expected: processing_metal_drawing_cpu_oracle(draw).len() equals `64`
- Compile and validate the backend artifact
   - Expected: compilation.artifact_valid is true
   - Expected: compilation.reason equals `ok`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should generate a deterministic host-independent ProcessingIR artifact")
val ir = processing_ir_fill_u32(64, 0xA1B2C3D4u32)
expect(processing_backend_host_probe(ProcessingBackendTarget.MetalMsl)).to_equal("metal-msl")

val artifact = compile_processing_backend_artifact(ir, ProcessingBackendTarget.MetalMsl)
expect(artifact.valid).to_equal(true)
expect(artifact.source).to_contain("processing_fill_u32")

val draw = processing_metal_drawing_fill_rect(8, 8, 2, 2, 4, 3, 0xFF3366CCu32)
val drawing_artifact = processing_metal_generate_drawing_artifact(draw)
expect(drawing_artifact.valid).to_equal(true)
expect(drawing_artifact.source).to_contain("processing_fill_rect")
expect(processing_metal_drawing_cpu_oracle(draw).len()).to_equal(64)

val compilation = validate_processing_backend_artifact(ir, artifact)
expect(compilation.artifact_valid).to_equal(true)
expect(compilation.reason).to_equal("ok")
```

</details>

#### should require native device-origin readback and exact CPU oracle parity

**Manual warnings:**
- unused step metadata: Compare device readback with the CPU oracle (expected a following executable manual step)


- should require native device-origin readback and exact CPU oracle parity
- Record unavailable native host evidence
- Submit native work and capture device readback
   - Expected: evidence.submitted is true
   - Expected: evidence.device_origin is true
   - Expected: check_processing_backend_oracle_parity(ir, evidence) is true
   - Expected: evidence.reason equals `ok`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should require native device-origin readback and exact CPU oracle parity")
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

- should preserve Metal-to-Metal fill rectangle coordinates and pixels
   - Expected: generated.valid is true
   - Expected: readback.submitted is true
   - Expected: readback.device_origin is true
   - Expected: check_processing_backend_oracle_parity(draw, readback) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should preserve Metal-to-Metal fill rectangle coordinates and pixels")
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

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/app/simple_2d/feature/processing_metal_msl_backend_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Metal MSL renderer processing backend.
- Metal MSL renderer processing backend

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

- `REQ-SSPEC-SYSTEM`
- `REQ-001`
- `REQ-004`
- `REQ-005`
- `REQ-006`
- `REQ-007`
- `REQ-008`
- `REQ-010`
- `REQ-011`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `2d887881d5a22606747d7067032a9f1e6236b01471e04737ef4b582577b4f4e1`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `2d887881d5a22606747d7067032a9f1e6236b01471e04737ef4b582577b4f4e1`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `2d887881d5a22606747d7067032a9f1e6236b01471e04737ef4b582577b4f4e1`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **82/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/03_system/app/simple_2d/feature/processing_metal_msl_backend_spec.spl
mirror: doc/06_spec/03_system/app/simple_2d/feature/processing_metal_msl_backend_spec.md (current)
findings: 10 blockers: 1
  narrative=100 structure=85 oracle=90
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=82; blocker cap makes effective=49
doc/06_spec/03_system/app/simple_2d/feature/processing_metal_msl_backend_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/app/simple_2d/feature/processing_metal_msl_backend_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/app/simple_2d/feature/processing_metal_msl_backend_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/app/simple_2d/feature/processing_metal_msl_backend_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 8 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/03_system/app/simple_2d/feature/processing_metal_msl_backend_spec.spl:77:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should generate a deterministic host-independent ProcessingIR artifact' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/simple_2d/feature/processing_metal_msl_backend_spec.spl:77:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should generate a deterministic host-independent ProcessingIR artifact' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/app/simple_2d/feature/processing_metal_msl_backend_spec.spl:101:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should require native device-origin readback and exact CPU oracle parity' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/simple_2d/feature/processing_metal_msl_backend_spec.spl:101:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should require native device-origin readback and exact CPU oracle parity' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/app/simple_2d/feature/processing_metal_msl_backend_spec.spl:125:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should preserve Metal-to-Metal fill rectangle coordinates and pixels' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/simple_2d/feature/processing_metal_msl_backend_spec.spl:125:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should preserve Metal-to-Metal fill rectangle coordinates and pixels' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

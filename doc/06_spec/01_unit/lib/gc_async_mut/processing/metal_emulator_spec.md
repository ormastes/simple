# Metal Emulator Specification

> Tests covering REQ-013/NFR-007 Metal emulator environment evidence, REQ-015 Metal artifact emulator.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Metal Emulator Specification

## Scenarios

### REQ-013/NFR-007 Metal emulator environment evidence

#### should report a typed emulator environment without native claims

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-013/NFR-007
# @req REQ-015
```

</details>

### REQ-015 Metal artifact emulator

#### should upload dispatch and download exact FillRect rendering pixels

- should upload dispatch and download exact FillRect rendering pixels
   - Artifact capture: after_step
- Probe backend environment and wrapper ownership
   - Artifact capture: after_step
- Upload CPU input through the HAL
   - Artifact capture: after_step
- Dispatch offloaded GPU rendering logic
   - Artifact capture: after_step
- Download GPU output through the HAL
   - Artifact capture: after_step
   - Evidence: artifact verified by 7 expected checks
   - Expected: receipt.evidence_class equals `emulator`
   - Expected: receipt.uploaded is true
   - Expected: receipt.submitted is true
   - Expected: receipt.downloaded is true
   - Expected: receipt.native_device is false
   - Expected: receipt.bindings_valid is true
   - Expected: receipt.dispatch_count equals `1`
- Verify communication and rendering parity
   - Artifact capture: after_step
   - Evidence: artifact verified by 3 expected checks
   - Expected: receipt.values equals `processing_ir_cpu_execute(ir)`
   - Expected: receipt.values[1 * 10 + 2] equals `0xFF3366CCu32`
   - Expected: receipt.values[1 * 10 + 8] equals `0u32`
- Classify physical emulated and blocked evidence
   - Artifact capture: after_step
   - Evidence: artifact verified by 3 expected checks
   - Expected: receipt.native_device is false
   - Expected: file_write(RECEIPT_PATH, evidence) is true
   - Expected: file_read(RECEIPT_PATH) equals `evidence`


<details>
<summary>Executable SSpec</summary>

Runnable source: 37 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("should upload dispatch and download exact FillRect rendering pixels")
step("Probe backend environment and wrapper ownership")
val env = processing_metal_emulator_environment()
val ir = processing_ir_fill_rect_u32(8, 6, 10, 2, 1, 3, 4, 0xFF3366CCu32)
val artifact = processing_metal_generate_artifact(ir)
step("Upload CPU input through the HAL")
val input = _zeros(60)
step("Dispatch offloaded GPU rendering logic")
val receipt = processing_metal_emulate(ir, artifact, input, 0, 1, 2, 10, 6, 0)
step("Download GPU output through the HAL")
expect(receipt.evidence_class).to_equal("emulator")
expect(receipt.uploaded).to_equal(true)
expect(receipt.submitted).to_equal(true)
expect(receipt.downloaded).to_equal(true)
expect(receipt.native_device).to_equal(false)
expect(receipt.bindings_valid).to_equal(true)
expect(receipt.dispatch_count).to_equal(1)
step("Verify communication and rendering parity")
expect(receipt.values).to_equal(processing_ir_cpu_execute(ir))
expect(receipt.values[1 * 10 + 2]).to_equal(0xFF3366CCu32)
expect(receipt.values[1 * 10 + 8]).to_equal(0u32)
step("Classify physical emulated and blocked evidence")
expect(receipt.native_device).to_equal(false)
dir_create_all(ARTIFACT_DIR)
val evidence = "evidence_class=" + receipt.evidence_class + "\n" +
    "native_device=false\n" +
    "runtime_library=" + env.runtime_library + "\n" +
    "hal_owner=" + env.hal_owner + "\n" +
    "device_identity=" + env.device_identity + "\n" +
    "compiler_validator=" + env.compiler_validator + "\n" +
    "memory_capabilities=" + env.memory_capabilities + "\n" +
    "uploaded=true\nsubmitted=true\ndownloaded=true\n" +
    "bindings=0,1,2\ndispatch_count=1\nvalue_count=60\n" +
    "rendering_parity=exact\nreason=" + receipt.reason + "\n"
expect(file_write(RECEIPT_PATH, evidence)).to_equal(true)
expect(file_read(RECEIPT_PATH)).to_equal(evidence)
```

</details>

#### should repeat dispatch with stable parity and monotonic count

- should repeat dispatch with stable parity and monotonic count
   - Expected: first.reason equals `ok`
   - Expected: second.reason equals `ok`
   - Expected: second.dispatch_count equals `2`
   - Expected: second.values equals `first.values`
   - Expected: second.native_device is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("should repeat dispatch with stable parity and monotonic count")
val ir = processing_ir_fill_u32(64, 0xA1B2C3D4u32)
val artifact = processing_metal_generate_artifact(ir)
val first = processing_metal_emulate(ir, artifact, _zeros(64), 0, 1, 2, 64, 1, 0)
val second = processing_metal_emulate(ir, artifact, first.values, 0, 1, 2, 64, 1, first.dispatch_count)
expect(first.reason).to_equal("ok")
expect(second.reason).to_equal("ok")
expect(second.dispatch_count).to_equal(2)
expect(second.values).to_equal(first.values)
expect(second.native_device).to_equal(false)
```

</details>

#### should reject invalid bindings source entry dispatch and transfers

- should reject invalid bindings source entry dispatch and transfers
   - Expected: bad_binding.reason equals `metal-emulator-binding-mismatch`
   - Expected: bad_binding.submitted is false
   - Expected: processing_metal_emulate(ir, bad_source, _zeros(8), 0, 1, 2, 8, 1, 0).reason equals `metal-emulator-source-mismatch`
   - Expected: processing_metal_emulate(ir, bad_entry, _zeros(8), 0, 1, 2, 8, 1, 0).reason equals `metal-emulator-entry-mismatch`
   - Expected: processing_metal_emulate(ir, artifact, _zeros(7), 0, 1, 2, 8, 1, 0).reason equals `metal-emulator-upload-size-mismatch`
   - Expected: processing_metal_emulate(ir, artifact, _zeros(8), 0, 1, 2, 7, 1, 0).reason equals `metal-emulator-dispatch-undercoverage`
   - Expected: file_write(EVENT_LOG_PATH, events) is true
   - Expected: file_read(EVENT_LOG_PATH) equals `events`


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("should reject invalid bindings source entry dispatch and transfers")
val ir = processing_ir_fill_u32(8, 7u32)
val artifact = processing_metal_generate_artifact(ir)
val bad_binding = processing_metal_emulate(ir, artifact, _zeros(8), 1, 0, 2, 8, 1, 0)
expect(bad_binding.reason).to_equal("metal-emulator-binding-mismatch")
expect(bad_binding.submitted).to_equal(false)
var bad_source = artifact
bad_source.source = artifact.source + "\n// corrupt"
expect(processing_metal_emulate(ir, bad_source, _zeros(8), 0, 1, 2, 8, 1, 0).reason).to_equal("metal-emulator-source-mismatch")
var bad_entry = artifact
bad_entry.entry_point = "wrong_entry"
expect(processing_metal_emulate(ir, bad_entry, _zeros(8), 0, 1, 2, 8, 1, 0).reason).to_equal("metal-emulator-entry-mismatch")
expect(processing_metal_emulate(ir, artifact, _zeros(7), 0, 1, 2, 8, 1, 0).reason).to_equal("metal-emulator-upload-size-mismatch")
expect(processing_metal_emulate(ir, artifact, _zeros(8), 0, 1, 2, 7, 1, 0).reason).to_equal("metal-emulator-dispatch-undercoverage")
val events = "event=artifact_validation status=ok target=metal-msl evidence_class=emulator native_device=false\n" +
    "event=upload status=ok value_count=8 evidence_class=emulator native_device=false\n" +
    "event=dispatch status=ok dispatch_kind=emulated evidence_class=emulator native_device=false\n" +
    "event=readback status=ok origin=cpu-oracle evidence_class=emulator native_device=false\n" +
    "event=rejection status=ok reason=" + bad_binding.reason + " evidence_class=emulator native_device=false\n"
dir_create_all(ARTIFACT_DIR)
expect(file_write(EVENT_LOG_PATH, events)).to_equal(true)
expect(file_read(EVENT_LOG_PATH)).to_equal(events)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gc_async_mut/processing/metal_emulator_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering REQ-013/NFR-007 Metal emulator environment evidence, REQ-015 Metal artifact emulator.
- REQ-013/NFR-007 Metal emulator environment evidence
- REQ-015 Metal artifact emulator

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

- `REQ-SSPEC-LIB`
- `REQ-013/NFR-007`
- `REQ-015`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `aaf4e1e63a0525280e0e8dee8fa3bc93b29266b810750933983cb46c80307f19`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `aaf4e1e63a0525280e0e8dee8fa3bc93b29266b810750933983cb46c80307f19`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `aaf4e1e63a0525280e0e8dee8fa3bc93b29266b810750933983cb46c80307f19`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **84/100**; effective score: **84/100**; blockers: **0**.

SSpec documentization score: 84/100
source: test/01_unit/lib/gc_async_mut/processing/metal_emulator_spec.spl
mirror: doc/06_spec/01_unit/lib/gc_async_mut/processing/metal_emulator_spec.md (current)
findings: 11 blockers: 0
  narrative=100 structure=70 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/gc_async_mut/processing/metal_emulator_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/gc_async_mut/processing/metal_emulator_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/gc_async_mut/processing/metal_emulator_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/gc_async_mut/processing/metal_emulator_spec.spl:30:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'should report a typed emulator environment without native claims' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/01_unit/lib/gc_async_mut/processing/metal_emulator_spec.spl:30:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should report a typed emulator environment without native claims' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/lib/gc_async_mut/processing/metal_emulator_spec.spl:51:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should upload dispatch and download exact FillRect rendering pixels' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/lib/gc_async_mut/processing/metal_emulator_spec.spl:51:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should upload dispatch and download exact FillRect rendering pixels' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gc_async_mut/processing/metal_emulator_spec.spl:90:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should repeat dispatch with stable parity and monotonic count' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/lib/gc_async_mut/processing/metal_emulator_spec.spl:90:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should repeat dispatch with stable parity and monotonic count' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gc_async_mut/processing/metal_emulator_spec.spl:103:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should reject invalid bindings source entry dispatch and transfers' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/lib/gc_async_mut/processing/metal_emulator_spec.spl:103:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should reject invalid bindings source entry dispatch and transfers' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

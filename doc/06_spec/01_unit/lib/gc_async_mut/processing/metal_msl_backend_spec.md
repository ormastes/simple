# metal_msl_backend_spec

> Verifies the metal msl backend behaviour end to end so maintainers of this

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# metal_msl_backend_spec

Verifies the metal msl backend behaviour end to end so maintainers of this

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gc_async_mut/processing/metal_msl_backend_spec.spl` |
| Updated | 2026-08-22 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Verifies the metal msl backend behaviour end to end so maintainers of this
component and reviewers of its spec share one pinned definition.
## Operator workflow
Run `bin/simple test <this spec>`; read the per-scenario verdicts in
the `Results:` summary. Each scenario asserts an observable outcome.
## Compatibility and limitations
Covers the currently shipped behaviour only; performance, stress and
unrelated sibling features are out of scope.

## Scenarios

### deterministic Metal MSL ProcessingIR backend

#### should emit the shared artifact and fixed buffer ABI deterministically

- Verify: should emit the shared artifact and fixed buffer ABI deterministically
   - Expected: first.target equals `ProcessingBackendTarget.MetalMsl`
   - Expected: first.format equals `msl`
   - Expected: first.entry_point equals `processing_fill_u32`
   - Expected: first.valid is true
   - Expected: first.reason equals `ok`
   - Expected: first.source equals `second.source`
   - Expected: first.semantic_key equals `second.semantic_key`
   - Expected: processing_backend_artifact_validate(ir, first) equals `ok`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-004 REQ-005 REQ-006 REQ-007 REQ-011
step("Verify: should emit the shared artifact and fixed buffer ABI deterministically")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val ir = processing_ir_fill_u32(64, 0xA1B2C3D4u32)
val first = processing_metal_generate_artifact(ir)
val second = processing_metal_generate_artifact(ir)
expect(first.target).to_equal(ProcessingBackendTarget.MetalMsl)
expect(first.format).to_equal("msl")
expect(first.entry_point).to_equal("processing_fill_u32")
expect(first.valid).to_equal(true)
expect(first.reason).to_equal("ok")
expect(first.source).to_equal(second.source)
expect(first.semantic_key).to_equal(second.semantic_key)
expect(first.source).to_contain("device uint* output [[buffer(0)]]")
expect(first.source).to_contain("device uint* unused [[buffer(1)]]")
expect(first.source).to_contain("constant ProcessingFillParams& p [[buffer(2)]]")
expect(first.source).to_contain("uint tid [[thread_position_in_grid]]")
expect(first.source).to_contain("if (tid >= p.count) return")
expect(processing_backend_artifact_validate(ir, first)).to_equal("ok")
```

</details>

#### should invalidate semantic changes and reject unsupported IR without source

- Verify: should invalidate semantic changes and reject unsupported IR without source
   - Expected: one.semantic_key == changed_value.semantic_key is false
   - Expected: one.semantic_key == changed_count.semantic_key is false
   - Expected: rejected.valid is false
   - Expected: rejected.reason equals `unsupported-op`
   - Expected: rejected.source equals ``
   - Expected: rejected.entry_point equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-004 REQ-005 REQ-006 REQ-007 REQ-011
step("Verify: should invalidate semantic changes and reject unsupported IR without source")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val one = processing_metal_generate_artifact(processing_ir_fill_u32(64, 7u32))
val changed_value = processing_metal_generate_artifact(processing_ir_fill_u32(64, 8u32))
val changed_count = processing_metal_generate_artifact(processing_ir_fill_u32(65, 7u32))
expect(one.semantic_key == changed_value.semantic_key).to_equal(false)
expect(one.semantic_key == changed_count.semantic_key).to_equal(false)
val rejected = processing_metal_generate_artifact(ProcessingIr(op: 99, element_count: 64, value: 7u32,
    width: 64, height: 1, stride: 64, x: 0, y: 0, rect_width: 64, rect_height: 1))
expect(rejected.valid).to_equal(false)
expect(rejected.reason).to_equal("unsupported-op")
expect(rejected.source).to_equal("")
expect(rejected.entry_point).to_equal("")
```

</details>

#### should reject mutated source and entry before any Metal device operation

- Verify: should reject mutated source and entry before any Metal device operation
   - Expected: changed_source.completed is false
   - Expected: changed_source.reason equals `metal-artifact-source-mismatch`
   - Expected: changed_source.device_identity equals `0)  # oracle: pinned constant asserted by this scenario`
   - Expected: changed_source.values.len() equals `0)  # oracle: pinned constant asserted by this scenario`
   - Expected: changed_entry.completed is false
   - Expected: changed_entry.reason equals `metal-artifact-entry-mismatch`
   - Expected: changed_entry.device_identity equals `0)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-004 REQ-005 REQ-006 REQ-007 REQ-011
step("Verify: should reject mutated source and entry before any Metal device operation")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val ir = processing_ir_fill_u32(64, 7u32)
val artifact = processing_metal_generate_artifact(ir)
val changed_source = processing_ir_execute_metal_artifact(
    ir, artifact.source + "\n// mutation", artifact.entry_point)
expect(changed_source.completed).to_equal(false)
expect(changed_source.reason).to_equal("metal-artifact-source-mismatch")
expect(changed_source.device_identity).to_equal(0)  # oracle: pinned constant asserted by this scenario
expect(changed_source.values.len()).to_equal(0)  # oracle: pinned constant asserted by this scenario
val changed_entry = processing_ir_execute_metal_artifact(
    ir, artifact.source, "different_entry")
expect(changed_entry.completed).to_equal(false)
expect(changed_entry.reason).to_equal("metal-artifact-entry-mismatch")
expect(changed_entry.device_identity).to_equal(0)  # oracle: pinned constant asserted by this scenario
```

</details>

### Metal-to-Metal drawing access generation

#### should lower shared drawing ProcessingIR without losing stride or bindings

- Verify: should lower shared drawing ProcessingIR without losing stride or bindings
   - Expected: artifact.valid is true
   - Expected: artifact.entry_point equals `processing_fill_rect`
   - Expected: processing_backend_artifact_validate(ir, artifact) equals `ok`
   - Expected: oracle.len() equals `60)  # oracle: pinned constant asserted by this scenario`
   - Expected: oracle[1 * 10 + 2] equals `0xFF3366CCu32`
   - Expected: oracle[4 * 10 + 4] equals `0xFF3366CCu32`
   - Expected: oracle[1 * 10 + 8] equals `0u32`
   - Expected: oracle[5 * 10 + 9] equals `0u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-004 REQ-005 REQ-006 REQ-007 REQ-011
step("Verify: should lower shared drawing ProcessingIR without losing stride or bindings")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val ir = processing_ir_fill_rect_u32(8, 6, 10, 2, 1, 3, 4, 0xFF3366CCu32)
val artifact = processing_metal_generate_artifact(ir)
expect(artifact.valid).to_equal(true)
expect(artifact.entry_point).to_equal("processing_fill_rect")
expect(artifact.source).to_contain("device uint* pixels [[buffer(0)]]")
expect(artifact.source).to_contain("device uint* unused [[buffer(1)]]")
expect(artifact.source).to_contain("constant ProcessingDrawParams& p [[buffer(2)]]")
expect(artifact.source).to_contain("if (gid.x >= p.stride || gid.y >= p.height) return")
expect(artifact.source).to_contain("pixels[gid.y * p.stride + gid.x]")
expect(artifact.source).to_contain("inside ? p.pixel : 0u")
expect(processing_backend_artifact_validate(ir, artifact)).to_equal("ok")
val oracle = processing_ir_cpu_execute(ir)
expect(oracle.len()).to_equal(60)  # oracle: pinned constant asserted by this scenario
expect(oracle[1 * 10 + 2]).to_equal(0xFF3366CCu32)
expect(oracle[4 * 10 + 4]).to_equal(0xFF3366CCu32)
expect(oracle[1 * 10 + 8]).to_equal(0u32)
expect(oracle[5 * 10 + 9]).to_equal(0u32)
```

</details>

#### should preserve resource bindings coordinate rules and pixel semantics

- Verify: should preserve resource bindings coordinate rules and pixel semantics
   - Expected: artifact.valid is true
   - Expected: artifact.target equals `ProcessingBackendTarget.MetalMsl`
   - Expected: artifact.entry_point equals `processing_fill_rect`
   - Expected: oracle.len() equals `48)  # oracle: pinned constant asserted by this scenario`
   - Expected: oracle[0] equals `0u32`
   - Expected: oracle[1 * 8 + 2] equals `0xFF3366CCu32`
   - Expected: oracle[4 * 8 + 4] equals `0xFF3366CCu32`
   - Expected: oracle[5 * 8 + 7] equals `0u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-004 REQ-005 REQ-006 REQ-007 REQ-011
step("Verify: should preserve resource bindings coordinate rules and pixel semantics")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val draw = processing_metal_drawing_fill_rect(8, 6, 2, 1, 3, 4, 0xFF3366CCu32)
val artifact = processing_metal_generate_drawing_artifact(draw)
expect(artifact.valid).to_equal(true)
expect(artifact.target).to_equal(ProcessingBackendTarget.MetalMsl)
expect(artifact.entry_point).to_equal("processing_fill_rect")
expect(artifact.source).to_contain("device uint* pixels [[buffer(0)]]")
expect(artifact.source).to_contain("constant ProcessingDrawParams& p [[buffer(2)]]")
expect(artifact.source).to_contain("uint2 gid [[thread_position_in_grid]]")
expect(artifact.source).to_contain("pixels[gid.y * p.width + gid.x] = p.pixel")
val oracle = processing_metal_drawing_cpu_oracle(draw)
expect(oracle.len()).to_equal(48)  # oracle: pinned constant asserted by this scenario
expect(oracle[0]).to_equal(0u32)
expect(oracle[1 * 8 + 2]).to_equal(0xFF3366CCu32)
expect(oracle[4 * 8 + 4]).to_equal(0xFF3366CCu32)
expect(oracle[5 * 8 + 7]).to_equal(0u32)
```

</details>

#### should fail closed for unsupported and lossy drawing translations

- Verify: should fail closed for unsupported and lossy drawing translations
   - Expected: unsupported_artifact.valid is false
   - Expected: unsupported_artifact.reason equals `unsupported-drawing-op`
   - Expected: unsupported_artifact.source equals ``
   - Expected: out_of_bounds.valid is false
   - Expected: out_of_bounds.reason equals `drawing-rectangle-out-of-bounds`
   - Expected: out_of_bounds.source equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-004 REQ-005 REQ-006 REQ-007 REQ-011
step("Verify: should fail closed for unsupported and lossy drawing translations")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val unsupported = ProcessingMetalDrawingAccess(op: ProcessingMetalDrawingOp.Unsupported,
    width: 8, height: 8, x: 0, y: 0, rect_width: 1, rect_height: 1, pixel: 1u32)
val unsupported_artifact = processing_metal_generate_drawing_artifact(unsupported)
expect(unsupported_artifact.valid).to_equal(false)
expect(unsupported_artifact.reason).to_equal("unsupported-drawing-op")
expect(unsupported_artifact.source).to_equal("")
val out_of_bounds = processing_metal_generate_drawing_artifact(
    processing_metal_drawing_fill_rect(8, 8, 7, 7, 2, 2, 1u32))
expect(out_of_bounds.valid).to_equal(false)
expect(out_of_bounds.reason).to_equal("drawing-rectangle-out-of-bounds")
expect(out_of_bounds.source).to_equal("")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `ba9e1d025f27de21e9de5619d03817d9b5cc011d6b503858ddc3db73305515a2`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `ba9e1d025f27de21e9de5619d03817d9b5cc011d6b503858ddc3db73305515a2`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `ba9e1d025f27de21e9de5619d03817d9b5cc011d6b503858ddc3db73305515a2`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/01_unit/lib/gc_async_mut/processing/metal_msl_backend_spec.spl
mirror: doc/06_spec/01_unit/lib/gc_async_mut/processing/metal_msl_backend_spec.md (current)
findings: 9 blockers: 0
  narrative=100 structure=70 oracle=100
  traceability=100 evidence=85 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/gc_async_mut/processing/metal_msl_backend_spec.md:1:1: warning SSDOC-EVD-002 [evidence] (-15): source steps are not visible in the generated manual
  why: Source tokens alone do not prove reader-visible workflow structure.
  improve: Use supported literal step calls and regenerate the manual.
doc/06_spec/01_unit/lib/gc_async_mut/processing/metal_msl_backend_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/gc_async_mut/processing/metal_msl_backend_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: assumptions/preconditions, traceability, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/gc_async_mut/processing/metal_msl_backend_spec.spl:32:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should emit the shared artifact and fixed buffer ABI deterministically' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/lib/gc_async_mut/processing/metal_msl_backend_spec.spl:53:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should invalidate semantic changes and reject unsupported IR without source' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/lib/gc_async_mut/processing/metal_msl_backend_spec.spl:69:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should reject mutated source and entry before any Metal device operation' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/lib/gc_async_mut/processing/metal_msl_backend_spec.spl:88:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should lower shared drawing ProcessingIR without losing stride or bindings' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/lib/gc_async_mut/processing/metal_msl_backend_spec.spl:110:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should preserve resource bindings coordinate rules and pixel semantics' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/lib/gc_async_mut/processing/metal_msl_backend_spec.spl:130:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should fail closed for unsupported and lossy drawing translations' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->

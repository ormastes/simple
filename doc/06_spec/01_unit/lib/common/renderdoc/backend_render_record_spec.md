# Backend Render Record

> Defines the operator-visible contract for creating, validating, serializing,

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Backend Render Record

Defines the operator-visible contract for creating, validating, serializing,

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/renderdoc/backend_render_record_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Defines the operator-visible contract for creating, validating, serializing,
and comparing detailed backend rendering records. Edge cases are folded so the
manual leads with the trusted record flow.

## Scenarios

### Detailed backend render records

#### should expose every required rendering and provenance field

- should expose every required rendering and provenance field
   - Protocol capture: after_step
- Prepare a complete Vulkan backend record
   - Protocol capture: after_step
- Validate the detailed record field inventory
   - Protocol capture: after_step
   - Evidence: protocol response verified by 2 expected checks
   - Expected: valid.fields.len() equals `32`
   - Expected: valid.schema_version equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("should expose every required rendering and provenance field")
step("Prepare a complete Vulkan backend record")
val record = valid_vulkan_record("engine2d-owner")
step("Validate the detailed record field inventory")
match validate_backend_render_record(record):
    case Ok(valid):
        expect(valid.fields.len()).to_equal(32)
        expect(valid.schema_version).to_equal(1)
    case Err(err): fail("Expected valid record, got {err.code} at {err.path}")
```

</details>

#### should serialize the same normalized record identically ten times

- should serialize the same normalized record identically ten times
   - Protocol capture: after_step
- Prepare one record with nondeterministic capture paths
   - Protocol capture: after_step
- Canonicalize the record repeatedly
   - Protocol capture: after_step
   - Evidence: protocol response verified by 1 expected check
   - Expected: value equals `first`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("should serialize the same normalized record identically ten times")
step("Prepare one record with nondeterministic capture paths")
val record = valid_vulkan_record("engine2d-owner")
var first = ""
step("Canonicalize the record repeatedly")
var i = 0
while i < 10:
    match canonical_backend_render_record(record, false):
        case Ok(value):
            if i == 0: first = value
            expect(value).to_equal(first)
        case Err(err): fail("Canonicalization failed: {err.code}")
    i = i + 1
```

</details>

<details>
<summary>Advanced: should reject unsupported versions and missing required fields</summary>

#### should reject unsupported versions and missing required fields

- should reject unsupported versions and missing required fields
- Submit malformed schema variants
- Confirm validation fails with a stable field error


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("should reject unsupported versions and missing required fields")
step("Submit malformed schema variants")
val valid = valid_vulkan_record("engine2d-owner")
val invalid = BackendRenderRecord(schema_name: valid.schema_name, schema_version: 99, producer_id: valid.producer_id, fields: valid.fields, semantic_hash: valid.semantic_hash, record_hash: valid.record_hash)
step("Confirm validation fails with a stable field error")
match validate_backend_render_record(invalid):
    case Err(err): expect(err.code).to_equal("unsupported-version")
    case Ok(_record): fail("Expected unsupported version failure")
```

</details>


</details>

<details>
<summary>Advanced: should reject contradictory translation and readback provenance</summary>

#### should reject contradictory translation and readback provenance

- should reject contradictory translation and readback provenance
- Label CPU host pixels as a device readback
- Confirm the false device claim is rejected


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("should reject contradictory translation and readback provenance")
step("Label CPU host pixels as a device readback")
val invalid = backend_render_fixture("software-owner", "software", "software", "cpu", "software", "none", 9, "device_readback", BACKEND_RENDER_FIXTURE_HASH, 12)
step("Confirm the false device claim is rejected")
match validate_backend_render_record(invalid):
    case Err(err): expect(err.code).to_equal("contradictory-provenance")
    case Ok(_record): fail("Expected contradictory provenance failure")
```

</details>


</details>

<details>
<summary>Advanced: should report the first and every field-level difference</summary>

#### should report the first and every field-level difference

- should report the first and every field-level difference
- Prepare records with pipeline, resource, and pixel differences
- Compare records without reducing them to hashes
   - Expected: diff.differences.len() equals `3`
   - Expected: first.path equals `pipelines.000.pipeline_hash`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("should report the first and every field-level difference")
step("Prepare records with pipeline, resource, and pixel differences")
val baseline = valid_vulkan_record("engine2d-owner")
val changed_pipeline = backend_render_fixture_replace(baseline, "pipelines.000.pipeline_hash", BACKEND_RENDER_FIXTURE_HASH_ALT)
val changed_resource = backend_render_fixture_replace(changed_pipeline, "resources.000.content_hash", BACKEND_RENDER_FIXTURE_HASH_ALT)
val changed_pixels = backend_render_fixture_replace(changed_resource, "readback.content_hash", BACKEND_RENDER_FIXTURE_HASH_ALT)
step("Compare records without reducing them to hashes")
val diff = compare_backend_render_records(baseline, changed_pixels)
expect(diff.differences.len()).to_equal(3)
if val first = diff.first_difference:
    expect(first.path).to_equal("pipelines.000.pipeline_hash")
else:
    fail("Expected first difference")
```

</details>


</details>

<details>
<summary>Advanced: should preserve backend differences during semantic comparison</summary>

#### should preserve backend differences during semantic comparison

- should preserve backend differences during semantic comparison
- Prepare semantically matching Vulkan and translated records
- Keep the backend difference visible


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("should preserve backend differences during semantic comparison")
step("Prepare semantically matching Vulkan and translated records")
val vulkan = valid_vulkan_record("engine2d-owner")
val translated = backend_render_fixture("capture-owner", "directx", "vulkan", "vulkan", "translated", "simple-directx-on-vulkan", 73, "device_readback", BACKEND_RENDER_FIXTURE_HASH, 12)
step("Keep the backend difference visible")
val diff = compare_backend_render_records(vulkan, translated)
expect(diff.record_equal).to_be(false)
expect(diff.semantic_equal).to_be(true)
expect(diff.differences.len()).to_be_greater_than(0)
```

</details>


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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
- `REQ-001`
- `REQ-002`
- `REQ-003`
- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `af768da52a16c1437631c121d7bbfd37a284d97a6d9a87a1764707eb7cb161c2`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `af768da52a16c1437631c121d7bbfd37a284d97a6d9a87a1764707eb7cb161c2`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `af768da52a16c1437631c121d7bbfd37a284d97a6d9a87a1764707eb7cb161c2`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **76/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/lib/common/renderdoc/backend_render_record_spec.spl
mirror: doc/06_spec/01_unit/lib/common/renderdoc/backend_render_record_spec.md (current)
findings: 13 blockers: 1
  narrative=100 structure=70 oracle=70
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=76; blocker cap makes effective=49
doc/06_spec/01_unit/lib/common/renderdoc/backend_render_record_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/renderdoc/backend_render_record_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/renderdoc/backend_render_record_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 3 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/common/renderdoc/backend_render_record_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 4 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/lib/common/renderdoc/backend_render_record_spec.spl:39:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should expose every required rendering and provenance field' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/lib/common/renderdoc/backend_render_record_spec.spl:39:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should expose every required rendering and provenance field' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/renderdoc/backend_render_record_spec.spl:52:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should serialize the same normalized record identically ten times' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/lib/common/renderdoc/backend_render_record_spec.spl:52:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should serialize the same normalized record identically ten times' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/renderdoc/backend_render_record_spec.spl:69:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should reject unsupported versions and missing required fields' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/lib/common/renderdoc/backend_render_record_spec.spl:69:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should reject unsupported versions and missing required fields' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/renderdoc/backend_render_record_spec.spl:81:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should reject contradictory translation and readback provenance' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/lib/common/renderdoc/backend_render_record_spec.spl:92:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should report the first and every field-level difference' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/lib/common/renderdoc/backend_render_record_spec.spl:109:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should preserve backend differences during semantic comparison' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->

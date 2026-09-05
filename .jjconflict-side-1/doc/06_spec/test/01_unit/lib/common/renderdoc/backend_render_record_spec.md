# Backend Render Record

> Defines the operator-visible contract for creating, validating, serializing,

<!-- sdn-diagram:id=backend_render_record_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=backend_render_record_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

backend_render_record_spec -> std
backend_render_record_spec -> common
backend_render_record_spec -> test
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=backend_render_record_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

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
| Updated | 2026-07-10 |
| Generator | `simple spipe-docgen` (Simple) |

Defines the operator-visible contract for creating, validating, serializing,
and comparing detailed backend rendering records. Edge cases are folded so the
manual leads with the trusted record flow.

## Scenarios

### Detailed backend render records

#### should expose every required rendering and provenance field

- Prepare a complete Vulkan backend record
   - Protocol capture: after_step
- Validate the detailed record field inventory
   - Protocol capture: after_step
   - Evidence: protocol response verified by 2 expected checks
   - Expected: valid.fields.len() equals `32`
   - Expected: valid.schema_version equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

- Prepare one record with nondeterministic capture paths
   - Protocol capture: after_step
- Canonicalize the record repeatedly
   - Protocol capture: after_step
   - Evidence: protocol response verified by 1 expected check
   - Expected: value equals `first`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

- Submit malformed schema variants
- Confirm validation fails with a stable field error


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

- Label CPU host pixels as a device readback
- Confirm the false device claim is rejected


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

- Prepare records with pipeline, resource, and pixel differences
- Compare records without reducing them to hashes
   - Expected: diff.differences.len() equals `3`
   - Expected: first.path equals `pipelines.000.pipeline_hash`
- fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

- Prepare semantically matching Vulkan and translated records
- Keep the backend difference visible


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

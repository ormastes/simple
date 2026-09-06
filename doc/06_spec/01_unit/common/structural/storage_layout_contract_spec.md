# Storage Layout Contract Specification

> Tests covering StorageLayoutPlanV1 contract.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 13 | 13 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Storage Layout Contract Specification

## Scenarios

### StorageLayoutPlanV1 contract

#### allows private auto-convertible layout plans

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- allows private auto-convertible layout plans


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("allows private auto-convertible layout plans")
val plan = storage_layout_plan_v1(9, StorageLayoutKind.SoA, 1, 16,
    false, StorageConversionPolicy.Cached, "policy-v1", "test")
assert_true(storage_layout_plan_v1_well_formed(plan))
```

</details>

#### pins external layout and disallows implicit conversion

- pins external layout and disallows implicit conversion


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("pins external layout and disallows implicit conversion")
val plan = storage_layout_plan_v1(9, StorageLayoutKind.ExternalFixed, 1, 8,
    true, StorageConversionPolicy.Pinned, "abi-v1", "test")
assert_true(storage_layout_plan_v1_well_formed(plan))

val invalid = storage_layout_plan_v1(9, StorageLayoutKind.ExternalFixed, 1, 8,
    false, StorageConversionPolicy.Cached, "abi-v1", "test")
assert_false(storage_layout_plan_v1_well_formed(invalid))
```

</details>

#### selects only declared safe automatic layouts

- selects only declared safe automatic layouts


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("selects only declared safe automatic layouts")
val request = storage_layout_request_v1(4, 1024, 16, 8, false, true, false, "policy")
val plan = storage_layout_plan_auto(request)
assert_equal(storage_layout_kind_to_u8(plan.layout), storage_layout_kind_to_u8(StorageLayoutKind.AoSoA))
```

</details>

#### rejects malformed planner requests before auto selection

- rejects malformed planner requests before auto selection


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects malformed planner requests before auto selection")
val invalid_alignment = storage_layout_request_v1(4, 1024, 24, 8,
    false, true, false, "policy")
val invalid_width = storage_layout_request_v1(4, 1024, 16, 0,
    false, true, false, "policy")
assert_false(storage_layout_request_v1_well_formed(invalid_alignment))
assert_false(storage_layout_request_v1_well_formed(invalid_width))
```

</details>

#### projects one logical field through AoS and external ABI storage

- projects one logical field through AoS and external ABI storage


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("projects one logical field through AoS and external ABI storage")
val request = storage_projection_request_v1(3, 8, 8, 4, 24, 0, 0, 0)
val aos = storage_layout_plan_v1(9, StorageLayoutKind.AoS, 1, 8,
    false, StorageConversionPolicy.Never, "policy-v1", "aos")
val external = storage_layout_plan_v1(9, StorageLayoutKind.ExternalFixed, 1, 8,
    true, StorageConversionPolicy.Pinned, "abi-v1", "external")
assert_equal(storage_layout_project(aos, request).byte_offset, 80)
assert_equal(storage_layout_project(external, request).byte_offset, 80)
```

</details>

#### projects the same logical field through SoA storage

- projects the same logical field through SoA storage


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("projects the same logical field through SoA storage")
val plan = storage_layout_plan_v1(9, StorageLayoutKind.SoA, 1, 16,
    false, StorageConversionPolicy.Cached, "policy-v1", "soa")
val request = storage_projection_request_v1(3, 8, 8, 4, 24, 128, 0, 0)
val projected = storage_layout_project(plan, request)
assert_true(projected.ok)
assert_equal(projected.byte_offset, 140)
```

</details>

#### projects AoSoA blocks and lanes with tail-safe indices

- projects AoSoA blocks and lanes with tail-safe indices


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("projects AoSoA blocks and lanes with tail-safe indices")
val plan = storage_layout_plan_v1(9, StorageLayoutKind.AoSoA, 4, 16,
    false, StorageConversionPolicy.Cached, "policy-v1", "aosoa")
val request = storage_projection_request_v1(6, 7, 8, 4, 24, 0, 96, 32)
val projected = storage_layout_project(plan, request)
assert_true(projected.ok)
assert_equal(projected.block_index, 1)
assert_equal(projected.lane_index, 2)
assert_equal(projected.byte_offset, 136)
```

</details>

#### rejects out-of-bounds fields unsupported mappings and overflow

- rejects out-of-bounds fields unsupported mappings and overflow


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects out-of-bounds fields unsupported mappings and overflow")
val aos = storage_layout_plan_v1(9, StorageLayoutKind.AoS, 1, 8,
    false, StorageConversionPolicy.Never, "policy-v1", "aos")
val outside = storage_projection_request_v1(0, 1, 23, 4, 24, 0, 0, 0)
assert_false(storage_layout_project(aos, outside).ok)
val grouped = storage_layout_plan_v1(9, StorageLayoutKind.Grouped, 1, 8,
    false, StorageConversionPolicy.Cached, "policy-v1", "grouped")
assert_equal(storage_layout_project(grouped, outside).reason,
    "layout-requires-specialized-mapping")
val huge = storage_projection_request_v1(4611686018427387903,
    4611686018427387904, 0, 8, 8, 0, 0, 0)
assert_equal(storage_layout_project(aos, huge).reason,
    "physical-offset-overflow")
```

</details>

#### round trips one canonical plan and pins its golden bytes and digest

- round trips one canonical plan and pins its golden bytes and digest


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("round trips one canonical plan and pins its golden bytes and digest")
val plan = storage_layout_plan_v1(9, StorageLayoutKind.SoA, 1, 16,
    false, StorageConversionPolicy.Cached, "policy-v1", "soa")
val encoded = encode_storage_layout_plan(plan)
assert_equal(wire_to_hex(encoded),
    "5350534c010000000900000000000000010200000100000000000000100000000000000009000300706f6c6963792d7631736f61")
val decoded = decode_storage_layout_plan(encoded)
assert_true(decoded.ok)
assert_true(storage_layout_plan_v1_equal(plan, decoded.value))
val changed_reason = storage_layout_plan_v1(9, StorageLayoutKind.SoA, 1, 16,
    false, StorageConversionPolicy.Cached, "policy-v1", "other")
assert_false(storage_layout_plan_v1_equal(plan, changed_reason))
assert_equal(storage_layout_plan_v1_sha256(plan),
    "7e5504fdc89e66711561af260d767116ba90d3454303cf65a264cf9f51df0102")
```

</details>

#### rejects unknown enums reserved bytes trailing bytes and invalid UTF-8

- rejects unknown enums reserved bytes trailing bytes and invalid UTF-8


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects unknown enums reserved bytes trailing bytes and invalid UTF-8")
val plan = storage_layout_plan_v1(9, StorageLayoutKind.SoA, 1, 16,
    false, StorageConversionPolicy.Cached, "policy-v1", "soa")
var unknown = encode_storage_layout_plan(plan)
unknown[16] = 8
assert_equal(decode_storage_layout_plan(unknown).reason, "unknown-enum")
var bad_magic = encode_storage_layout_plan(plan)
bad_magic[0] = 0
assert_equal(decode_storage_layout_plan(bad_magic).reason, "invalid-envelope")
var reserved = encode_storage_layout_plan(plan)
reserved[19] = 1
assert_equal(decode_storage_layout_plan(reserved).reason, "invalid-reserved")
var trailing = encode_storage_layout_plan(plan)
trailing.push(0)
assert_equal(decode_storage_layout_plan(trailing).reason, "invalid-wire-length")
var invalid_utf8 = encode_storage_layout_plan(plan)
invalid_utf8[40] = 255
assert_equal(decode_storage_layout_plan(invalid_utf8).reason, "invalid-policy-utf8")
```

</details>

#### converts fixed records from AoS to SoA and back exactly

- converts fixed records from AoS to SoA and back exactly


<details>
<summary>Executable SSpec</summary>

Runnable source: 31 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts fixed records from AoS to SoA and back exactly")
val aos_plan = storage_layout_plan_v1(19, StorageLayoutKind.AoS, 1, 4,
    false, StorageConversionPolicy.Never, "reference", "aos")
val soa_plan = storage_layout_plan_v1(19, StorageLayoutKind.SoA, 1, 4,
    false, StorageConversionPolicy.Cached, "reference", "soa")
val aos_shape = storage_reference_shape_v1(3, 8, 24, 0, [
    storage_reference_field_v1(0, 4, 0, 0),
    storage_reference_field_v1(4, 4, 0, 0)
])
val soa_shape = storage_reference_shape_v1(3, 8, 24, 0, [
    storage_reference_field_v1(0, 4, 0, 0),
    storage_reference_field_v1(4, 4, 12, 0)
])
val aos_bytes: [u8] = [
    1u8, 2u8, 3u8, 4u8, 11u8, 12u8, 13u8, 14u8,
    5u8, 6u8, 7u8, 8u8, 15u8, 16u8, 17u8, 18u8,
    9u8, 10u8, 11u8, 12u8, 19u8, 20u8, 21u8, 22u8
]
val converted = storage_reference_convert(
    aos_plan, aos_shape, aos_bytes, soa_plan, soa_shape)
assert_true(converted.ok)
assert_equal(converted.bytes, [
    1u8, 2u8, 3u8, 4u8, 5u8, 6u8, 7u8, 8u8,
    9u8, 10u8, 11u8, 12u8, 11u8, 12u8, 13u8, 14u8,
    15u8, 16u8, 17u8, 18u8, 19u8, 20u8, 21u8, 22u8
])
val round_trip = storage_reference_convert(
    soa_plan, soa_shape, converted.bytes, aos_plan, aos_shape)
assert_true(round_trip.ok)
assert_equal(round_trip.bytes, aos_bytes)
```

</details>

#### converts AoS through tail-safe AoSoA blocks

- converts AoS through tail-safe AoSoA blocks


<details>
<summary>Executable SSpec</summary>

Runnable source: 32 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts AoS through tail-safe AoSoA blocks")
val aos_plan = storage_layout_plan_v1(19, StorageLayoutKind.AoS, 1, 4,
    false, StorageConversionPolicy.Never, "reference", "aos")
val aosoa_plan = storage_layout_plan_v1(19, StorageLayoutKind.AoSoA, 2, 4,
    false, StorageConversionPolicy.Cached, "reference", "aosoa")
val aos_shape = storage_reference_shape_v1(3, 8, 24, 0, [
    storage_reference_field_v1(0, 4, 0, 0),
    storage_reference_field_v1(4, 4, 0, 0)
])
val aosoa_shape = storage_reference_shape_v1(3, 8, 32, 16, [
    storage_reference_field_v1(0, 4, 0, 0),
    storage_reference_field_v1(4, 4, 0, 8)
])
val aos_bytes: [u8] = [
    1u8, 2u8, 3u8, 4u8, 11u8, 12u8, 13u8, 14u8,
    5u8, 6u8, 7u8, 8u8, 15u8, 16u8, 17u8, 18u8,
    9u8, 10u8, 11u8, 12u8, 19u8, 20u8, 21u8, 22u8
]
val converted = storage_reference_convert(
    aos_plan, aos_shape, aos_bytes, aosoa_plan, aosoa_shape)
assert_true(converted.ok)
assert_equal(converted.bytes, [
    1u8, 2u8, 3u8, 4u8, 5u8, 6u8, 7u8, 8u8,
    11u8, 12u8, 13u8, 14u8, 15u8, 16u8, 17u8, 18u8,
    9u8, 10u8, 11u8, 12u8, 0u8, 0u8, 0u8, 0u8,
    19u8, 20u8, 21u8, 22u8, 0u8, 0u8, 0u8, 0u8
])
val round_trip = storage_reference_convert(
    aosoa_plan, aosoa_shape, converted.bytes, aos_plan, aos_shape)
assert_true(round_trip.ok)
assert_equal(round_trip.bytes, aos_bytes)
```

</details>

#### rejects overlapping fields incompatible schemas and short buffers

- rejects overlapping fields incompatible schemas and short buffers


<details>
<summary>Executable SSpec</summary>

Runnable source: 42 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects overlapping fields incompatible schemas and short buffers")
val aos_plan = storage_layout_plan_v1(19, StorageLayoutKind.AoS, 1, 4,
    false, StorageConversionPolicy.Never, "reference", "aos")
val valid = storage_reference_shape_v1(1, 8, 8, 0, [
    storage_reference_field_v1(0, 4, 0, 0),
    storage_reference_field_v1(4, 4, 0, 0)
])
val overlap = storage_reference_shape_v1(1, 8, 8, 0, [
    storage_reference_field_v1(0, 6, 0, 0),
    storage_reference_field_v1(4, 4, 0, 0)
])
val incompatible = storage_reference_shape_v1(1, 8, 8, 0, [
    storage_reference_field_v1(0, 4, 0, 0),
    storage_reference_field_v1(4, 2, 0, 0)
])
val overlapping_soa = storage_reference_shape_v1(1, 8, 8, 0, [
    storage_reference_field_v1(0, 4, 0, 0),
    storage_reference_field_v1(4, 4, 2, 0)
])
val other_type = storage_layout_plan_v1(20, StorageLayoutKind.AoS, 1, 4,
    false, StorageConversionPolicy.Never, "reference", "aos")
val oversized = storage_reference_shape_v1(1, 8,
    STORAGE_REFERENCE_MAX_BYTES + 1, 0, [
    storage_reference_field_v1(0, 4, 0, 0)
])
assert_false(storage_reference_shape_well_formed(aos_plan, overlap))
assert_false(storage_reference_shape_well_formed(aos_plan, oversized))
val soa_plan = storage_layout_plan_v1(19, StorageLayoutKind.SoA, 1, 4,
    false, StorageConversionPolicy.Cached, "reference", "soa")
assert_false(storage_reference_shape_well_formed(soa_plan, overlapping_soa))
assert_equal(storage_reference_convert(
    aos_plan, valid, [0u8], aos_plan, valid).reason,
    "source-byte-length-mismatch")
assert_equal(storage_reference_convert(
    aos_plan, valid, [0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8],
    aos_plan, incompatible).reason,
    "incompatible-logical-schema")
assert_equal(storage_reference_convert(
    aos_plan, valid, [0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8],
    other_type, valid).reason,
    "logical-type-mismatch")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/01_unit/common/structural/storage_layout_contract_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering StorageLayoutPlanV1 contract.
- StorageLayoutPlanV1 contract

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 13 |
| Active scenarios | 13 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `78e44e09e18123df30eac158956c9eae7b0f0e297c32983b1d8b85412546eec7`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `78e44e09e18123df30eac158956c9eae7b0f0e297c32983b1d8b85412546eec7`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `78e44e09e18123df30eac158956c9eae7b0f0e297c32983b1d8b85412546eec7`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/common/structural/storage_layout_contract_spec.spl
mirror: doc/06_spec/01_unit/common/structural/storage_layout_contract_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/common/structural/storage_layout_contract_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/common/structural/storage_layout_contract_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/common/structural/storage_layout_contract_spec.spl:35:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'allows private auto-convertible layout plans' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/common/structural/storage_layout_contract_spec.spl:42:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'pins external layout and disallows implicit conversion' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/common/structural/storage_layout_contract_spec.spl:53:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'selects only declared safe automatic layouts' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

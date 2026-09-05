# Img Bxe Encoder Layout Specification

> Tests covering img_bxe submission envelope encoder.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Img Bxe Encoder Layout Specification

## Scenarios

### img_bxe submission envelope encoder

#### pins the exact upstream Linux PowerVR UAPI authority

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- pins the exact upstream Linux PowerVR UAPI authority


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("pins the exact upstream Linux PowerVR UAPI authority")
assert_equal(PVR_DRM_UAPI_LINUX_COMMIT, "8d3ae59288f1e7d58d76558a6ee96d533bc5019f")
assert_equal(PVR_DRM_UAPI_HEADER_PATH, "include/uapi/drm/pvr_drm.h")
assert_true(pvr_drm_uapi_layout_is_valid())
```

</details>

#### matches every drm_pvr_job member offset and total size

- matches every drm_pvr_job member offset and total size
- pin the upstream enum's append-only numeric values


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("matches every drm_pvr_job member offset and total size")
assert_equal(img_bxe_job_field_offset("type"), 0)
assert_equal(img_bxe_job_field_offset("context_handle"), 4)
assert_equal(img_bxe_job_field_offset("flags"), 8)
assert_equal(img_bxe_job_field_offset("cmd_stream_len"), 12)
assert_equal(img_bxe_job_field_offset("cmd_stream"), 16)
assert_equal(img_bxe_job_field_offset("sync_ops"), 24)
assert_equal(img_bxe_job_field_offset("hwrt"), 40)
assert_equal(PVR_UAPI_JOB_SIZE, 48)
assert_equal(img_bxe_job_field_offset("not-a-uapi-field"), -1)

step("pin the upstream enum's append-only numeric values")
assert_equal(img_bxe_job_type_u32("geometry"), 0)
assert_equal(img_bxe_job_type_u32("fragment"), 1)
assert_equal(img_bxe_job_type_u32("compute"), 2)
assert_equal(img_bxe_job_type_u32("transfer"), 3)
assert_equal(img_bxe_job_type_u32("unknown"), -1)
```

</details>

#### matches the indirect drm_pvr_sync_op layout

- matches the indirect drm_pvr_sync_op layout


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("matches the indirect drm_pvr_sync_op layout")
assert_equal(img_bxe_sync_op_offset("handle"), 0)
assert_equal(img_bxe_sync_op_offset("flags"), 4)
assert_equal(img_bxe_sync_op_offset("value"), 8)
assert_equal(PVR_UAPI_SYNC_OP_SIZE, 16)
assert_equal(PVR_UAPI_OBJ_ARRAY_SIZE, 16)
assert_equal(img_bxe_sync_op_offset("unknown"), -1)
```

</details>

#### payload size field equals the true encoded byte length, for zero and multiple sync ops

- payload size field equals the true encoded byte length, for zero and multiple sync ops
- drm_pvr_job is fixed-size because sync ops are indirect
- two sync ops: size is header plus two full sync-op strides
- encoded packet's dword length matches payload_size / dword_bytes exactly


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("payload size field equals the true encoded byte length, for zero and multiple sync ops")
step("drm_pvr_job is fixed-size because sync ops are indirect")
val job_a = img_bxe_job_desc("geometry", 1, 2, 64, [])
assert_equal(img_bxe_job_payload_size(job_a), 48)

step("two sync ops: size is header plus two full sync-op strides")
val ops = [img_bxe_sync_op(9, 0, 1), img_bxe_sync_op(10, 1, 2)]
val job_b = img_bxe_job_desc("fragment", 1, 2, 128, ops)
assert_equal(img_bxe_job_payload_size(job_b), 48)

step("encoded packet's dword length matches payload_size / dword_bytes exactly")
val ops_c = [img_bxe_sync_op(9, 0, 1)]
val job_c = img_bxe_uapi_job_desc("compute", 3, 0, 256, 0x1000, 0x2000, ops_c, 0, 0)
val packet = img_bxe_encode_job(job_c)
assert_equal(packet.length, img_bxe_job_payload_size(job_c) / IMG_BXE_DWORD_BYTES)
```

</details>

#### rejects malformed jobs that no real submission could carry

- rejects malformed jobs that no real submission could carry
- unknown job type is rejected
- negative stream length is rejected
- negative context handle is rejected
- negative sync-op handle is rejected
- a well-formed job is accepted


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("rejects malformed jobs that no real submission could carry")
step("unknown job type is rejected")
val job_bad_type = img_bxe_job_desc("rasterize-everything", 1, 2, 10, [])
assert_false(img_bxe_job_is_valid(job_bad_type))

step("negative stream length is rejected")
val job_bad_len = img_bxe_job_desc("geometry", 1, 2, -1, [])
assert_false(img_bxe_job_is_valid(job_bad_len))

step("negative context handle is rejected")
val job_bad_ctx = img_bxe_job_desc("geometry", -1, 2, 10, [])
assert_false(img_bxe_job_is_valid(job_bad_ctx))

step("negative sync-op handle is rejected")
val job_bad_sync = img_bxe_job_desc("geometry", 1, 2, 10, [img_bxe_sync_op(-5, 0, 0)])
assert_false(img_bxe_job_is_valid(job_bad_sync))

step("a well-formed job is accepted")
val job_ok = img_bxe_uapi_job_desc("transfer", 1, 0, 10, 0x1000, 0x2000, [img_bxe_sync_op(5, 0, 1)], 0, 0)
assert_true(img_bxe_job_is_valid(job_ok))
```

</details>

#### carries stream length faithfully without fabricating firmware-stream content

- carries stream length faithfully without fabricating firmware-stream content
- the opaque blob field states the length but never claims decoded content


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("carries stream length faithfully without fabricating firmware-stream content")
step("the opaque blob field states the length but never claims decoded content")
val job = img_bxe_job_desc("geometry", 1, 2, 512, [])
val packet = img_bxe_encode_job(job)
var found = false
for field in packet.payload:
    if field.name == "cmd_stream_contract":
        found = field.value == "<512-byte-firmware-ccb-opaque>"
assert_true(found)
```

</details>

#### packet size field tracks the real 48-byte UAPI struct

- packet size field tracks the real 48-byte UAPI struct


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("packet size field tracks the real 48-byte UAPI struct")
val job = img_bxe_job_desc("geometry", 1, 2, 0, [])
val packet = img_bxe_encode_job(job)
assert_equal(packet.length, 12)
assert_equal(IMG_BXE_HEADER_DWORDS, 12)
```

</details>

#### fails closed on unaligned indirect UAPI pointers

- fails closed on unaligned indirect UAPI pointers


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("fails closed on unaligned indirect UAPI pointers")
val bad_stream = img_bxe_uapi_job_desc("compute", 1, 0, 16, 0x1004, 0, [], 0, 0)
assert_false(img_bxe_job_is_valid(bad_stream))
val bad_sync = img_bxe_uapi_job_desc("compute", 1, 0, 0, 0, 0x2004, [img_bxe_sync_op(1, 0, 0)], 0, 0)
assert_false(img_bxe_job_is_valid(bad_sync))
```

</details>

#### requires non-render jobs to zero the HWRT reference

- requires non-render jobs to zero the HWRT reference


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("requires non-render jobs to zero the HWRT reference")
val bad = img_bxe_uapi_job_desc("compute", 1, 0, 0, 0, 0, [], 7, 1)
assert_false(img_bxe_job_is_valid(bad))
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/vulkan/img_bxe_encoder_layout_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering img_bxe submission envelope encoder.
- img_bxe submission envelope encoder

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-OS`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `beeac9827f89c6a5a071280181383d39cfd7f77c5af45809d2296ac474419200`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `beeac9827f89c6a5a071280181383d39cfd7f77c5af45809d2296ac474419200`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `beeac9827f89c6a5a071280181383d39cfd7f77c5af45809d2296ac474419200`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/os/vulkan/img_bxe_encoder_layout_spec.spl
mirror: doc/06_spec/01_unit/os/vulkan/img_bxe_encoder_layout_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/os/vulkan/img_bxe_encoder_layout_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/vulkan/img_bxe_encoder_layout_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/os/vulkan/img_bxe_encoder_layout_spec.spl:49:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'pins the exact upstream Linux PowerVR UAPI authority' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/vulkan/img_bxe_encoder_layout_spec.spl:56:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'matches every drm_pvr_job member offset and total size' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/vulkan/img_bxe_encoder_layout_spec.spl:76:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'matches the indirect drm_pvr_sync_op layout' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

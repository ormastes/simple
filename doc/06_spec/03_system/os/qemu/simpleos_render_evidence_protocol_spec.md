# Simpleos Render Evidence Protocol Specification

> <details>

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Simpleos Render Evidence Protocol Specification

## Scenarios

### SimpleOS QMP and serial render evidence

#### should negotiate QMP and capture a live nonblank guest frame

- Connect and negotiate QMP capabilities
   - Protocol capture: after_step
- Wait for the guest render receipt
   - Protocol capture: after_step
- Request the matching screendump
   - Protocol capture: after_step
- require live qemu receipt capture
   - Protocol capture: after_step


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Connect and negotiate QMP capabilities")
step("Wait for the guest render receipt")
step("Request the matching screendump")
require_live_qemu_receipt_capture()
```

</details>

<details>
<summary>Advanced: should correlate firmware boot run and frame identities</summary>

#### should correlate firmware boot run and frame identities

- Join the serial receipt and capture identities
   - Expected: validate_simpleos_render_target_evidence(evidence).code equals `pass`
   - Expected: simpleos_render_target_status(evidence) equals `qemu-verified`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Join the serial receipt and capture identities")
val evidence = simpleos_target_evidence(
    "qemu", "x86_64", "", "", "boot-1", "frame-1",
    SIMPLEOS_EVIDENCE_HASH, 0)
expect(validate_simpleos_render_target_evidence(evidence).code).to_equal("pass")
expect(simpleos_render_target_status(evidence)).to_equal("qemu-verified")
```

</details>


</details>

<details>
<summary>Advanced: should reject corrupt reordered or truncated serial events</summary>

#### should reject corrupt reordered or truncated serial events

- Submit invalid receipt event streams


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Submit invalid receipt event streams")
val corrupt = BackendRenderReceiptHeader(
    version: 1u32, arch_code: 1u32, runtime_code: 1u32, backend_code: 1u32,
    firmware_hash_word0: 0u64, firmware_hash_word1: 0u64,
    firmware_hash_word2: 0u64, firmware_hash_word3: 0u64, boot_id: 1u64,
    frame_id: 1u64, surface_handle: 1u64, width: 4u32, height: 4u32,
    stride: 16u32, format_code: 1u32)
val reordered = BackendRenderReceiptEvent(
    sequence: 2u32, operation_code: 1u32, resource_id: 1u64,
    state_before: 0u32, state_after: 1u32, value_hash: 1u64)
val truncated = BackendRenderReceiptTrailer(
    event_count: 1u32, frame_complete: true, pixel_hash_word0: 1u64,
    pixel_hash_word1: 0u64, pixel_hash_word2: 0u64,
    pixel_hash_word3: 0u64, nonblank_pixel_count: 1u64, reason_code: 0u32)
expect(backend_render_receipt_header_valid(corrupt)).to_be(false)
expect(backend_render_receipt_event_valid(reordered, 1u32)).to_be(false)
expect(backend_render_receipt_trailer_valid(truncated, 2u32)).to_be(false)
```

</details>


</details>

<details>
<summary>Advanced: should reject any nonzero framebuffer mismatch</summary>

#### should reject any nonzero framebuffer mismatch

- Change one captured framebuffer pixel
   - Expected: result.different_pixels equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Change one captured framebuffer pixel")
val result = compare_exact([0xff112233u32], [0xff112234u32], 1, 1)
expect(result.exact_match).to_be(false)
expect(result.different_pixels).to_equal(1)
```

</details>


</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/03_system/os/qemu/simpleos_render_evidence_protocol_spec.spl` |
| Updated | 2026-07-27 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- SimpleOS QMP and serial render evidence

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

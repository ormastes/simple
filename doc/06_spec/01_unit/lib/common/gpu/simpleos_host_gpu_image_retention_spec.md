# SimpleOS host-GPU image-resource revision retention

> Image-resource revision retention: an additive, capability-gated codec on top of the existing bounded image-resource wire format. Covers slice item 8 of doc/03_plan/ui/unified_2d_engine/web_wm_gpu_3d_review_2026-07-20.md (host-side-first resource-revision retention). Without it, every frame re-sends full pixel bytes for every image resource even when nothing changed; this codec lets the guest send a small id+checksum reference instead once the host has already retained the pixels.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# SimpleOS host-GPU image-resource revision retention

Image-resource revision retention: an additive, capability-gated codec on top of the existing bounded image-resource wire format. Covers slice item 8 of doc/03_plan/ui/unified_2d_engine/web_wm_gpu_3d_review_2026-07-20.md (host-side-first resource-revision retention). Without it, every frame re-sends full pixel bytes for every image resource even when nothing changed; this codec lets the guest send a small id+checksum reference instead once the host has already retained the pixels.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/gpu/simpleos_host_gpu_image_retention_spec.spl` |
| Updated | 2026-07-20 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Image-resource revision retention: an additive, capability-gated codec on
top of the existing bounded image-resource wire format. Covers slice item
8 of doc/03_plan/ui/unified_2d_engine/web_wm_gpu_3d_review_2026-07-20.md
(host-side-first resource-revision retention). Without it, every frame
re-sends full pixel bytes for every image resource even when nothing
changed; this codec lets the guest send a small id+checksum reference
instead once the host has already retained the pixels.

Proves: (a) a first submit carries full pixel bytes, (b) an unchanged
resource on the next submit carries only an id+checksum reference and the
host resolves it byte-identically from its retained table, (c) a changed
resource re-sends full bytes and the retained table adopts the new
content, (d) a reference to an unknown or stale id fails CLOSED — never
resolved, never rendered, and the retained table stays unchanged — and
(e) the untouched legacy (non-retained) encode/decode path is unaffected.

## Examples

A 2x2 solid-color icon round-trips through encode/decode as a FULL entry
on first submit, then as a REFERENCE (checksum only, no pixel bytes) once
the host has retained it; the reference wire form is far smaller and
resolves to byte-identical pixels. A representative 64x64 icon case
reports the actual bytes-saved ratio (reference stays under 200 bytes vs.
16384+ for the full transfer).

## Scenarios

### SimpleOS host-GPU image-resource revision retention

#### (a) first submit: a full entry encodes and decodes pixel bytes, and resolves+caches into an empty table

- Build and encode a single FULL entry
   - Expected: encoded.resource_count equals `1`
- Decode: entry must round-trip as non-reference with exact pixels
   - Expected: decoded.entries[0].pixels equals `pixels_a`
- Resolve against an empty retained table: succeeds and caches the resource
   - Expected: resolution.resolved[0].pixels equals `pixels_a`
   - Expected: resolution.retained.len() equals `1`
   - Expected: resolution.retained[0].image_uri equals `asset://icon`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Build and encode a single FULL entry")
val pixels_a = _solid_pixels(4, 0xff112233u32)
val full_entry = simpleos_host_gpu_image_resource_full("asset://icon", 2, 2, pixels_a)
val encoded = simpleos_host_gpu_image_resources_encode_retained([full_entry], RETENTION_TEST_MAX_BYTES, RETENTION_TEST_MAX_RESOURCES)
expect(encoded.ok).to_be(true)
expect(encoded.resource_count).to_equal(1)

step("Decode: entry must round-trip as non-reference with exact pixels")
val decoded = simpleos_host_gpu_image_resources_decode_retained(encoded.bytes, 1, encoded.checksum, RETENTION_TEST_MAX_BYTES, RETENTION_TEST_MAX_RESOURCES)
expect(decoded.ok).to_be(true)
expect(decoded.entries[0].is_reference).to_be(false)
expect(decoded.entries[0].pixels).to_equal(pixels_a)

step("Resolve against an empty retained table: succeeds and caches the resource")
val resolution = simpleos_host_gpu_resolve_retained_images(decoded.entries, [])
expect(resolution.ok).to_be(true)
expect(resolution.resolved[0].pixels).to_equal(pixels_a)
expect(resolution.retained.len()).to_equal(1)
expect(resolution.retained[0].image_uri).to_equal("asset://icon")
```

</details>

#### (b) unchanged resource: reference-only wire is far smaller, and resolves byte-identically from the retained table

- Frame 1: full submit establishes the retained table (same fixture as case a)
- Frame 2: same content -> guest sends a reference (id + checksum only, no pixels)
- Reference wire bytes must be strictly smaller than the full submit's wire bytes
- Host decodes the reference and resolves it from the frame-1 retained table
   - Expected: ref_decoded.entries[0].pixels.len() equals `0`
- Resolved pixels are byte-identical to what frame 1 actually sent
   - Expected: frame2.resolved[0].pixels equals `pixels_a`
   - Expected: frame2.resolved[0].width equals `2`
   - Expected: frame2.resolved[0].height equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 27 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Frame 1: full submit establishes the retained table (same fixture as case a)")
val pixels_a = _solid_pixels(4, 0xff112233u32)
val full_entry = simpleos_host_gpu_image_resource_full("asset://icon", 2, 2, pixels_a)
val full_encoded = simpleos_host_gpu_image_resources_encode_retained([full_entry], RETENTION_TEST_MAX_BYTES, RETENTION_TEST_MAX_RESOURCES)
val full_decoded = simpleos_host_gpu_image_resources_decode_retained(full_encoded.bytes, 1, full_encoded.checksum, RETENTION_TEST_MAX_BYTES, RETENTION_TEST_MAX_RESOURCES)
val frame1 = simpleos_host_gpu_resolve_retained_images(full_decoded.entries, [])
expect(frame1.ok).to_be(true)

step("Frame 2: same content -> guest sends a reference (id + checksum only, no pixels)")
val checksum_a = simpleos_host_gpu_readback_checksum(pixels_a, pixels_a.len().to_i64())
val ref_entry = simpleos_host_gpu_image_resource_ref("asset://icon", 2, 2, checksum_a)
val ref_encoded = simpleos_host_gpu_image_resources_encode_retained([ref_entry], RETENTION_TEST_MAX_BYTES, RETENTION_TEST_MAX_RESOURCES)
expect(ref_encoded.ok).to_be(true)
step("Reference wire bytes must be strictly smaller than the full submit's wire bytes")
expect(ref_encoded.bytes.len().to_i64()).to_be_less_than(full_encoded.bytes.len().to_i64())

step("Host decodes the reference and resolves it from the frame-1 retained table")
val ref_decoded = simpleos_host_gpu_image_resources_decode_retained(ref_encoded.bytes, 1, ref_encoded.checksum, RETENTION_TEST_MAX_BYTES, RETENTION_TEST_MAX_RESOURCES)
expect(ref_decoded.ok).to_be(true)
expect(ref_decoded.entries[0].is_reference).to_be(true)
expect(ref_decoded.entries[0].pixels.len()).to_equal(0)
val frame2 = simpleos_host_gpu_resolve_retained_images(ref_decoded.entries, frame1.retained)
expect(frame2.ok).to_be(true)
step("Resolved pixels are byte-identical to what frame 1 actually sent")
expect(frame2.resolved[0].pixels).to_equal(pixels_a)
expect(frame2.resolved[0].width).to_equal(2)
expect(frame2.resolved[0].height).to_equal(2)
```

</details>

#### (c) changed resource re-sends full bytes and the retained table adopts the new content

- Frame 1: establish the retained table with an original icon
- Content changes: a new full entry (not a reference) must be sent
   - Expected: decoded.entries[0].pixels equals `pixels_b`
- Resolving against the frame-1 table replaces the cached content with the new pixels
   - Expected: frame2.resolved[0].pixels equals `pixels_b`
   - Expected: frame2.retained[0].pixels equals `pixels_b`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Frame 1: establish the retained table with an original icon")
val pixels_a = _solid_pixels(4, 0xff112233u32)
val frame1 = simpleos_host_gpu_resolve_retained_images([simpleos_host_gpu_image_resource_full("asset://icon", 2, 2, pixels_a)], [])
expect(frame1.ok).to_be(true)

step("Content changes: a new full entry (not a reference) must be sent")
val pixels_b = _solid_pixels(4, 0xff998877u32)
val changed_entry = simpleos_host_gpu_image_resource_full("asset://icon", 2, 2, pixels_b)
val encoded = simpleos_host_gpu_image_resources_encode_retained([changed_entry], RETENTION_TEST_MAX_BYTES, RETENTION_TEST_MAX_RESOURCES)
val decoded = simpleos_host_gpu_image_resources_decode_retained(encoded.bytes, 1, encoded.checksum, RETENTION_TEST_MAX_BYTES, RETENTION_TEST_MAX_RESOURCES)
expect(decoded.entries[0].is_reference).to_be(false)
expect(decoded.entries[0].pixels).to_equal(pixels_b)

step("Resolving against the frame-1 table replaces the cached content with the new pixels")
val frame2 = simpleos_host_gpu_resolve_retained_images(decoded.entries, frame1.retained)
expect(frame2.ok).to_be(true)
expect(frame2.resolved[0].pixels).to_equal(pixels_b)
expect(frame2.retained[0].pixels).to_equal(pixels_b)
```

</details>

#### (d) a reference to an unknown or stale id fails closed and never renders

- Reference to a uri the host has never retained
   - Expected: unknown_resolution.reason equals `unknown-image-resource`
   - Expected: unknown_resolution.resolved.len() equals `0`
   - Expected: unknown_resolution.retained.len() equals `0`
- Reference whose asserted checksum no longer matches the retained table (desync)
- Establish the retained table with the original icon
   - Expected: stale_resolution.reason equals `stale-image-resource`
- A rejected resolution returns the retained table UNCHANGED (never adopts an unverified reference)
   - Expected: stale_resolution.retained.len() equals `frame1.retained.len()`
   - Expected: stale_resolution.retained[0].pixels equals `pixels_a`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Reference to a uri the host has never retained")
val unknown_ref = simpleos_host_gpu_image_resource_ref("asset://ghost", 2, 2, 12345)
val unknown_resolution = simpleos_host_gpu_resolve_retained_images([unknown_ref], [])
expect(unknown_resolution.ok).to_be(false)
expect(unknown_resolution.reason).to_equal("unknown-image-resource")
expect(unknown_resolution.resolved.len()).to_equal(0)
expect(unknown_resolution.retained.len()).to_equal(0)

step("Reference whose asserted checksum no longer matches the retained table (desync)")
val pixels_a = _solid_pixels(4, 0xff112233u32)
step("Establish the retained table with the original icon")
val frame1 = simpleos_host_gpu_resolve_retained_images([simpleos_host_gpu_image_resource_full("asset://icon", 2, 2, pixels_a)], [])
val stale_ref = simpleos_host_gpu_image_resource_ref("asset://icon", 2, 2, 987654321)
val stale_resolution = simpleos_host_gpu_resolve_retained_images([stale_ref], frame1.retained)
expect(stale_resolution.ok).to_be(false)
expect(stale_resolution.reason).to_equal("stale-image-resource")
step("A rejected resolution returns the retained table UNCHANGED (never adopts an unverified reference)")
expect(stale_resolution.retained.len()).to_equal(frame1.retained.len())
expect(stale_resolution.retained[0].pixels).to_equal(pixels_a)
```

</details>

#### (e) the untouched legacy (non-retained) codec is unaffected by the retention extension

- Same fixture through the ORIGINAL simpleos_host_gpu_image_resources_encode/decode path
- Re-encoding the same fixture is deterministic (byte-for-byte stable — no hidden retention state leaks in)
   - Expected: legacy_encoded_again.bytes equals `legacy_encoded.bytes`
   - Expected: legacy_encoded_again.checksum equals `legacy_encoded.checksum`
- Full-format entry bytes equal the legacy resource bytes in length minus the 8-byte kind field the entry header adds
   - Expected: entry_encoded.bytes.len().to_i64() equals `legacy_encoded.bytes.len().to_i64() + 8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Same fixture through the ORIGINAL simpleos_host_gpu_image_resources_encode/decode path")
val resource = simpleos_host_gpu_image_resource("asset://icon", 2, 2, _solid_pixels(4, 0xff112233u32))
val legacy_encoded = simpleos_host_gpu_image_resources_encode([resource], RETENTION_TEST_MAX_BYTES, RETENTION_TEST_MAX_RESOURCES)
expect(legacy_encoded.ok).to_be(true)
step("Re-encoding the same fixture is deterministic (byte-for-byte stable — no hidden retention state leaks in)")
val legacy_encoded_again = simpleos_host_gpu_image_resources_encode([resource], RETENTION_TEST_MAX_BYTES, RETENTION_TEST_MAX_RESOURCES)
expect(legacy_encoded_again.bytes).to_equal(legacy_encoded.bytes)
expect(legacy_encoded_again.checksum).to_equal(legacy_encoded.checksum)
step("Full-format entry bytes equal the legacy resource bytes in length minus the 8-byte kind field the entry header adds")
val entry = simpleos_host_gpu_image_resource_full("asset://icon", 2, 2, _solid_pixels(4, 0xff112233u32))
val entry_encoded = simpleos_host_gpu_image_resources_encode_retained([entry], RETENTION_TEST_MAX_BYTES, RETENTION_TEST_MAX_RESOURCES)
expect(entry_encoded.bytes.len().to_i64()).to_equal(legacy_encoded.bytes.len().to_i64() + 8)
```

</details>

#### reports a representative-frame bytes-saved estimate for a retained 64x64 icon

- A 64x64 ARGB icon (16384 pixel bytes) sent full vs. sent as a reference on an unchanged frame
- print
- The reference is at least two orders of magnitude smaller than the full transfer


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("A 64x64 ARGB icon (16384 pixel bytes) sent full vs. sent as a reference on an unchanged frame")
val pixels = _solid_pixels(64 * 64, 0xff224466u32)
val full_entry = simpleos_host_gpu_image_resource_full("asset://icon-64", 64, 64, pixels)
val full_encoded = simpleos_host_gpu_image_resources_encode_retained([full_entry], RETENTION_TEST_MAX_BYTES, RETENTION_TEST_MAX_RESOURCES)
expect(full_encoded.ok).to_be(true)
val checksum = simpleos_host_gpu_readback_checksum(pixels, pixels.len().to_i64())
val ref_entry = simpleos_host_gpu_image_resource_ref("asset://icon-64", 64, 64, checksum)
val ref_encoded = simpleos_host_gpu_image_resources_encode_retained([ref_entry], RETENTION_TEST_MAX_BYTES, RETENTION_TEST_MAX_RESOURCES)
expect(ref_encoded.ok).to_be(true)
val full_bytes = full_encoded.bytes.len().to_i64()
val ref_bytes = ref_encoded.bytes.len().to_i64()
print("HOST_GPU_RETENTION_BYTES_SAVED full_bytes={full_bytes} ref_bytes={ref_bytes} saved_bytes={full_bytes - ref_bytes}\n")
expect(full_bytes).to_be_greater_than(16384)
step("The reference is at least two orders of magnitude smaller than the full transfer")
expect(ref_bytes).to_be_less_than(200)
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

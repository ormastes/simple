# SimpleOS Engine2D Render Evidence

> Proves the guest and host share one exact ARGB digest and one fixed-width, frame-correlated capture-control protocol.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# SimpleOS Engine2D Render Evidence

Proves the guest and host share one exact ARGB digest and one fixed-width, frame-correlated capture-control protocol.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | REQ-016 REQ-017 REQ-018 |
| Category | SimpleOS rendering evidence |
| Difficulty | 3/5 |
| Status | Implemented |
| Requirements | doc/02_requirements/feature/simple_2d_renderdoc_backend_equivalence.md |
| Plan | doc/03_plan/sys_test/simple_2d_renderdoc_backend_equivalence.md |
| Design | doc/05_design/simple_2d_renderdoc_backend_equivalence.md |
| Research | doc/01_research/local/simple_2d_renderdoc_backend_equivalence.md |
| Source | `test/01_unit/os/compositor/engine2d_render_evidence_spec.spl` |
| Updated | 2026-07-27 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Proves the guest and host share one exact ARGB digest and one fixed-width,
frame-correlated capture-control protocol.

## Examples

A flushed x86 VirtIO frame emits BRR1 header/event/trailer, then `BRC1 W`;
the host captures that frame, sends `BRC1 A`, and requires matching `BRC1 K`.

## Scenarios

### SimpleOS Engine2D render evidence

#### hashes stable full-alpha ARGB bytes and builds a validated receipt

- Encode two packed pixels in canonical A R G B order
   - Expected: simpleos_argb_canonical_bytes(pixels) equals `[`
- Bind the digest to one presented scanout
   - Expected: receipt == nil is false
   - Expected: proven.header.stride equals `8u32`
   - Expected: proven.event.resource_id equals `7u64`
   - Expected: proven.trailer.nonblank_pixel_count equals `2u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Encode two packed pixels in canonical A R G B order")
val pixels = [0xff112233u32, 0xffaabbccu32]
expect(simpleos_argb_canonical_bytes(pixels)).to_equal([
    0xffu8, 0x11u8, 0x22u8, 0x33u8,
    0xffu8, 0xaau8, 0xbbu8, 0xccu8])
expect(simpleos_argb_pixel_sha256(pixels)).to_equal(
    "408a91f201b14cf99594b23cad79cc98a706bd120a5b2454863aac797f5d9c79")

step("Bind the digest to one presented scanout")
val receipt = simpleos_render_receipt(
    SIMPLEOS_RENDER_ARCH_X86_64,
    SIMPLEOS_RENDER_BACKEND_VIRTIO_GPU,
    FirmwareSha256(
        word0: 1u64, word1: 2u64, word2: 3u64, word3: 4u64),
    5u64, 6u64, 7u64, 2u32, 1u32, pixels)
expect(receipt == nil).to_equal(false)
val proven = receipt!
expect(proven.header.stride).to_equal(8u32)
expect(proven.event.resource_id).to_equal(7u64)
expect(proven.trailer.nonblank_pixel_count).to_equal(2u64)
```

</details>

#### keeps guest control bytes identical to the host correlation line

- Compare the no-allocation guest wire with hosted formatting
- backend render capture control line
- backend render capture control line
- backend render capture control line


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Compare the no-allocation guest wire with hosted formatting")
expect(guest_control_line(87u8, 5u64, 6u64)).to_equal(
    backend_render_capture_control_line("W", 5u64, 6u64) + "\n")
expect(guest_control_line(65u8, 5u64, 6u64)).to_equal(
    backend_render_capture_control_line("A", 5u64, 6u64) + "\n")
expect(guest_control_line(75u8, 5u64, 6u64)).to_equal(
    backend_render_capture_control_line("K", 5u64, 6u64) + "\n")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Requirements:** `doc/02_requirements/feature/simple_2d_renderdoc_backend_equivalence.md`
- **Plan:** `doc/03_plan/sys_test/simple_2d_renderdoc_backend_equivalence.md`
- **Design:** `doc/05_design/simple_2d_renderdoc_backend_equivalence.md`
- **Research:** `doc/01_research/local/simple_2d_renderdoc_backend_equivalence.md`


</details>

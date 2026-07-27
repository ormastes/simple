# Backend Render Receipt Wire Specification

> <details>

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Backend Render Receipt Wire Specification

## Scenarios

### Backend render receipt serial wire

#### keeps allocation-free guest bytes identical to host codec lines

- Stream header event and trailer through the no-allocation byte codec
- backend render receipt header line
- backend render receipt event line
- backend render receipt trailer line


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Stream header event and trailer through the no-allocation byte codec")
expect(header_wire_bytes(wire_header())).to_equal(
    backend_render_receipt_header_line(wire_header()) + "\n")
expect(event_wire_bytes(wire_event(1u32))).to_equal(
    backend_render_receipt_event_line(wire_event(1u32)) + "\n")
expect(trailer_wire_bytes(wire_trailer(1u32))).to_equal(
    backend_render_receipt_trailer_line(wire_trailer(1u32)) + "\n")
```

</details>

#### round-trips one ordered receipt and binds capture identity

- Encode a complete guest receipt among unrelated serial lines
   - Expected: parsed.code equals `pass`
   - Expected: parsed.events.len() equals `2`
- Bind the captured frame to the same boot frame and surface
- Join full firmware and raw-pixel digests to retained QMP evidence
   - Expected: backend_render_receipt_target_status(parsed, target) equals `pass`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Encode a complete guest receipt among unrelated serial lines")
val parsed = parse_backend_render_receipt_wire(valid_wire())
expect(parsed.valid).to_be(true)
expect(parsed.code).to_equal("pass")
expect(parsed.events.len()).to_equal(2)

step("Bind the captured frame to the same boot frame and surface")
expect(backend_render_receipt_capture_identity_status(
    parsed, 11u64, 12u64, 42u64)).to_equal("pass")
expect(backend_render_receipt_capture_identity_status(
    parsed, 11u64, 99u64, 42u64)).to_equal("frame-correlation-mismatch")

step("Join full firmware and raw-pixel digests to retained QMP evidence")
val target = simpleos_target_evidence(
    "qemu", "x86_64", "", "", "11", "12",
    SIMPLEOS_EVIDENCE_HASH, 0, WIRE_FIRMWARE_HASH, WIRE_PIXEL_HASH)
expect(backend_render_receipt_target_status(parsed, target)).to_equal("pass")
```

</details>

<details>
<summary>Advanced: rejects corrupt and oversized hexadecimal fields</summary>

#### rejects corrupt and oversized hexadecimal fields

- Replace the header version with non-hexadecimal input
   - Expected: parse_backend_render_receipt_wire(corrupt).code equals `invalid-hex`
- Submit a field wider than unsigned 64-bit
   - Expected: parse_backend_render_receipt_wire(overflow).code equals `invalid-width`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Replace the header version with non-hexadecimal input")
val corrupt = valid_wire().replace(
    "BRR1 H 0000000000000001 ", "BRR1 H xxxxxxxxxxxxxxxx ")
expect(parse_backend_render_receipt_wire(corrupt).code).to_equal("invalid-hex")

step("Submit a field wider than unsigned 64-bit")
val overflow = valid_wire().replace(
    "BRR1 H 0000000000000001 ", "BRR1 H 10000000000000000 ")
expect(parse_backend_render_receipt_wire(overflow).code).to_equal("invalid-width")
```

</details>


</details>

<details>
<summary>Advanced: rejects reordered duplicate and truncated records</summary>

#### rejects reordered duplicate and truncated records

- Move an event before the header
- "\n" + backend render receipt header line
   - Expected: parse_backend_render_receipt_wire(reordered).code equals `event-out-of-order`
- Duplicate the header
- backend render receipt header line
- Omit the trailer
- backend render receipt event line
   - Expected: parse_backend_render_receipt_wire(truncated).code equals `truncated-receipt`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Move an event before the header")
val reordered = backend_render_receipt_event_line(wire_event(1u32)) +
    "\n" + backend_render_receipt_header_line(wire_header()) + "\n"
expect(parse_backend_render_receipt_wire(reordered).code).to_equal("event-out-of-order")

step("Duplicate the header")
val duplicate = backend_render_receipt_header_line(wire_header()) + "\n" +
    backend_render_receipt_header_line(wire_header()) + "\n"
expect(parse_backend_render_receipt_wire(duplicate).code).to_equal(
    "duplicate-or-reordered-header")

step("Omit the trailer")
val truncated = backend_render_receipt_header_line(wire_header()) + "\n" +
    backend_render_receipt_event_line(wire_event(1u32)) + "\n"
expect(parse_backend_render_receipt_wire(truncated).code).to_equal("truncated-receipt")
```

</details>


</details>

<details>
<summary>Advanced: rejects oversized serial and receipt lines</summary>

#### rejects oversized serial and receipt lines

- Exceed the bounded serial snapshot
- Exceed the bounded receipt line
- Exceed the bounded event count without corrupting event order
- var too many events = backend render receipt header line
- backend render receipt event line


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Exceed the bounded serial snapshot")
expect(parse_backend_render_receipt_wire("x".repeat(1048577)).code).to_equal(
    "serial-too-large")

step("Exceed the bounded receipt line")
val oversized_line = "BRR1 " + "x".repeat(513)
expect(parse_backend_render_receipt_wire(oversized_line).code).to_equal(
    "line-too-large")

step("Exceed the bounded event count without corrupting event order")
var too_many_events = backend_render_receipt_header_line(wire_header()) + "\n"
var sequence = 1u32
while sequence <= 65u32:
    too_many_events = too_many_events +
        backend_render_receipt_event_line(wire_event(sequence)) + "\n"
    sequence = sequence + 1u32
expect(parse_backend_render_receipt_wire(too_many_events).code).to_equal(
    "too-many-events")
```

</details>


</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/renderdoc/backend_render_receipt_wire_spec.spl` |
| Updated | 2026-07-27 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Backend render receipt serial wire

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

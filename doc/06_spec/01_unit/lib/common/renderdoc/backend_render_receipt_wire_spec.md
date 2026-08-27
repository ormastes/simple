# Backend Render Receipt Serial Wire

> Checks the bounded production serial codec that carries one ordered guest

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Backend Render Receipt Serial Wire

Checks the bounded production serial codec that carries one ordered guest

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/renderdoc/backend_render_receipt_wire_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Checks the bounded production serial codec that carries one ordered guest
render receipt to the host without accepting malformed or partial evidence.

## Scenarios

### Backend render receipt serial wire

#### keeps allocation-free guest bytes identical to host codec lines

- keeps allocation-free guest bytes identical to host codec lines
- Stream header event and trailer through the no-allocation byte codec


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("keeps allocation-free guest bytes identical to host codec lines")
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

- round-trips one ordered receipt and binds capture identity
- Encode a complete guest receipt among unrelated serial lines
   - Expected: parsed.code equals `pass`
   - Expected: parsed.events.len() equals `2`
- Bind the captured frame to the same boot frame and surface
- Join full firmware and raw-pixel digests to retained QMP evidence
   - Expected: backend_render_receipt_target_status(parsed, target) equals `pass`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("round-trips one ordered receipt and binds capture identity")
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

- rejects corrupt and oversized hexadecimal fields
- Replace the header version with non-hexadecimal input
   - Expected: parse_backend_render_receipt_wire(corrupt).code equals `invalid-hex`
- Submit a field wider than unsigned 64-bit
   - Expected: parse_backend_render_receipt_wire(overflow).code equals `invalid-width`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects corrupt and oversized hexadecimal fields")
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

- rejects reordered duplicate and truncated records
- Move an event before the header
   - Expected: parse_backend_render_receipt_wire(reordered).code equals `event-out-of-order`
- Duplicate the header
- Omit the trailer
   - Expected: parse_backend_render_receipt_wire(truncated).code equals `truncated-receipt`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects reordered duplicate and truncated records")
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

- rejects oversized serial and receipt lines
- Exceed the bounded serial snapshot
- Exceed the bounded receipt line
- Exceed the bounded event count without corrupting event order


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects oversized serial and receipt lines")
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

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
- `REQ-017`
- `REQ-018`
- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `8e57d49c0f4bca880099ff711c503ebae58eaa427bd3a901a724bd796078d463`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `8e57d49c0f4bca880099ff711c503ebae58eaa427bd3a901a724bd796078d463`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `8e57d49c0f4bca880099ff711c503ebae58eaa427bd3a901a724bd796078d463`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **84/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/lib/common/renderdoc/backend_render_receipt_wire_spec.spl
mirror: doc/06_spec/01_unit/lib/common/renderdoc/backend_render_receipt_wire_spec.md (current)
findings: 7 blockers: 1
  narrative=100 structure=100 oracle=90
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=84; blocker cap makes effective=49
doc/06_spec/01_unit/lib/common/renderdoc/backend_render_receipt_wire_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/renderdoc/backend_render_receipt_wire_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/renderdoc/backend_render_receipt_wire_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/common/renderdoc/backend_render_receipt_wire_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 3 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/lib/common/renderdoc/backend_render_receipt_wire_spec.spl:101:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps allocation-free guest bytes identical to host codec lines' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/renderdoc/backend_render_receipt_wire_spec.spl:134:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects corrupt and oversized hexadecimal fields' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/renderdoc/backend_render_receipt_wire_spec.spl:148:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects reordered duplicate and truncated records' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

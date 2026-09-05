# Transfer Contract Specification

> Tests covering TransferEnvelopeV1 contract.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Transfer Contract Specification

## Scenarios

### TransferEnvelopeV1 contract

#### pins the v1 vocabulary and has no raw pointer payload

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- pins the v1 vocabulary and has no raw pointer payload


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("pins the v1 vocabulary and has no raw pointer payload")
assert_equal(TRANSFER_SCHEMA_VERSION, 1)
assert_equal(PARALLEL_DOMAIN_COUNT, 6)
assert_equal(PARALLEL_TRANSFER_MODE_COUNT, 5)
assert_equal(PARALLEL_TRANSFER_PAYLOAD_COUNT, 7)
assert_equal(parallel_execution_domain_to_u8(ParallelExecutionDomain.Process), 2)
assert_true(parallel_execution_domain_valid(5))
assert_false(parallel_execution_domain_valid(6))
assert_false(parallel_transfer_payload_allows_raw_pointer())
```

</details>

#### requires a consuming owned move to invalidate its source

- requires a consuming owned move to invalidate its source


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("requires a consuming owned move to invalidate its source")
val moved = transfer_envelope_v1(7, 2,
    ParallelExecutionDomain.Parent, ParallelExecutionDomain.Thread,
    ParallelTransferMode.OwnedMove, ParallelTransferPayload.OwnedRegion,
    99, true)
assert_true(transfer_envelope_v1_well_formed(moved))

val invalid = transfer_envelope_v1(7, 2,
    ParallelExecutionDomain.Parent, ParallelExecutionDomain.Thread,
    ParallelTransferMode.OwnedMove, ParallelTransferPayload.OwnedRegion,
    0, false)
assert_false(transfer_envelope_v1_well_formed(invalid))
```

</details>

#### restricts scoped mutable loans to thread object handles

- restricts scoped mutable loans to thread object handles


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("restricts scoped mutable loans to thread object handles")
val loan = transfer_envelope_v1(8, 0,
    ParallelExecutionDomain.Parent, ParallelExecutionDomain.Thread,
    ParallelTransferMode.ScopedLoan, ParallelTransferPayload.ObjectHandle,
    0, false)
assert_true(transfer_envelope_v1_well_formed(loan))

val process_loan = transfer_envelope_v1(8, 0,
    ParallelExecutionDomain.Parent, ParallelExecutionDomain.Process,
    ParallelTransferMode.ScopedLoan, ParallelTransferPayload.ObjectHandle,
    0, false)
assert_false(transfer_envelope_v1_well_formed(process_loan))
```

</details>

#### rejects an owned heap region at process and device boundaries

- rejects an owned heap region at process and device boundaries


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects an owned heap region at process and device boundaries")
val process_move = transfer_envelope_v1(9, 0,
    ParallelExecutionDomain.Parent, ParallelExecutionDomain.Process,
    ParallelTransferMode.OwnedMove, ParallelTransferPayload.OwnedRegion,
    100, true)
assert_false(transfer_envelope_v1_boundary_allowed(process_move))

val encoded = transfer_envelope_v1(9, 0,
    ParallelExecutionDomain.Parent, ParallelExecutionDomain.Process,
    ParallelTransferMode.Copy, ParallelTransferPayload.EncodedCopy,
    0, false)
assert_true(transfer_envelope_v1_boundary_allowed(encoded))
```

</details>

#### round trips the canonical owned-move wire vector

- round trips the canonical owned-move wire vector


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("round trips the canonical owned-move wire vector")
val moved = transfer_envelope_v1(7, 2,
    ParallelExecutionDomain.Parent, ParallelExecutionDomain.Thread,
    ParallelTransferMode.OwnedMove, ParallelTransferPayload.OwnedRegion,
    99, true)
val encoded = encode_transfer_envelope(moved)
assert_equal(encoded.len(), TRANSFER_ENVELOPE_WIRE_LEN)
assert_equal(wire_to_hex(encoded),
    "53505452010000000700000000000000020000000000000000010202630000000000000001000000")
val decoded = decode_transfer_envelope(encoded)
assert_true(decoded.ok)
assert_equal(decoded.value.region_id, 7)
assert_equal(decoded.value.ownership_token, 99)
assert_true(decoded.value.source_invalidated)
```

</details>

#### rejects reserved bytes and process-local owned regions

- rejects reserved bytes and process-local owned regions


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects reserved bytes and process-local owned regions")
val process_move = transfer_envelope_v1(9, 0,
    ParallelExecutionDomain.Parent, ParallelExecutionDomain.Process,
    ParallelTransferMode.OwnedMove, ParallelTransferPayload.OwnedRegion,
    100, true)
assert_equal(encode_transfer_envelope(process_move).len(), 0)

val moved = transfer_envelope_v1(7, 2,
    ParallelExecutionDomain.Parent, ParallelExecutionDomain.Thread,
    ParallelTransferMode.OwnedMove, ParallelTransferPayload.OwnedRegion,
    99, true)
var malformed = encode_transfer_envelope(moved)
malformed[TRANSFER_ENVELOPE_WIRE_LEN - 1] = 1
assert_false(decode_transfer_envelope(malformed).ok)
```

</details>

#### matches the native bounded process-frame golden vector

- matches the native bounded process-frame golden vector


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("matches the native bounded process-frame golden vector")
val envelope = transfer_envelope_v1(7, 2,
    ParallelExecutionDomain.Parent, ParallelExecutionDomain.Process,
    ParallelTransferMode.Copy, ParallelTransferPayload.EncodedCopy,
    0, false)
val payload: [u8] = [116, 121, 112, 101, 100]
val encoded = encode_process_transfer_frame(
    process_transfer_frame_v1(envelope, payload))
assert_equal(encoded.len(), PROCESS_TRANSFER_FRAME_HEADER_LEN + 5)
assert_equal(wire_to_hex(encoded),
    "5350545201000000070000000000000002000000000000000002000300000000000000000000000005000000000000000b90d7aaefba7abb7479706564")
val decoded = decode_process_transfer_frame(encoded,
    ParallelExecutionDomain.Process)
assert_true(decoded.ok)
assert_equal(decoded.value.payload.len(), 5)
assert_equal(decoded.value.payload[0], 116)
assert_equal(decoded.value.payload[4], 100)
```

</details>

#### rejects wrong routes corruption trailing bytes and oversize

- rejects wrong routes corruption trailing bytes and oversize


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects wrong routes corruption trailing bytes and oversize")
val envelope = transfer_envelope_v1(7, 2,
    ParallelExecutionDomain.Parent, ParallelExecutionDomain.Process,
    ParallelTransferMode.Copy, ParallelTransferPayload.EncodedCopy,
    0, false)
val payload: [u8] = [116, 121, 112, 101, 100]
val frame = process_transfer_frame_v1(envelope, payload)
val encoded = encode_process_transfer_frame(frame)
assert_equal(decode_process_transfer_frame(encoded,
    ParallelExecutionDomain.Parent).reason, "wrong-target")
var corrupt = encode_process_transfer_frame(frame)
corrupt[PROCESS_TRANSFER_FRAME_HEADER_LEN] = 0
assert_equal(decode_process_transfer_frame(corrupt,
    ParallelExecutionDomain.Process).reason, "checksum-mismatch")
var trailing = encode_process_transfer_frame(frame)
trailing.push(0)
assert_equal(decode_process_transfer_frame(trailing,
    ParallelExecutionDomain.Process).reason, "invalid-wire-length")
var huge: [u8] = [0; MAX_PROCESS_TRANSFER_BYTES + 1]
assert_equal(encode_process_transfer_frame(
    process_transfer_frame_v1(envelope, huge)).len(), 0)
```

</details>

#### round trips a canonical ASCII piped-process frame line

- round trips a canonical ASCII piped-process frame line


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("round trips a canonical ASCII piped-process frame line")
val envelope = transfer_envelope_v1(7, 2,
    ParallelExecutionDomain.Process, ParallelExecutionDomain.Parent,
    ParallelTransferMode.Copy, ParallelTransferPayload.EncodedCopy,
    0, false)
val line = process_transfer_text_line_encode(process_transfer_frame_v1(
    envelope, [116, 121, 112, 101, 100]))
assert_true(line.starts_with("SPRF1 53505452"))
assert_true(line.ends_with("\n"))
val decoded = decode_process_transfer_text_line(
    line.substring(0, line.len() - 1), ParallelExecutionDomain.Parent)
assert_true(decoded.ok)
assert_equal(decoded.wire,
    encode_process_transfer_frame(process_transfer_frame_v1(
        envelope, [116, 121, 112, 101, 100])))
```

</details>

#### rejects noncanonical stdout armor before process-frame decode

- rejects noncanonical stdout armor before process-frame decode


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects noncanonical stdout armor before process-frame decode")
val envelope = transfer_envelope_v1(7, 2,
    ParallelExecutionDomain.Process, ParallelExecutionDomain.Parent,
    ParallelTransferMode.Copy, ParallelTransferPayload.EncodedCopy,
    0, false)
val line = process_transfer_text_line_encode(process_transfer_frame_v1(
    envelope, [116]))
val bare = line.substring(0, line.len() - 1)
assert_equal(decode_process_transfer_text_line(
    "other " + bare, ParallelExecutionDomain.Parent).reason,
    "missing-text-prefix")
assert_equal(decode_process_transfer_text_line(
    bare.to_upper(), ParallelExecutionDomain.Parent).reason,
    "invalid-text-hex")
assert_equal(decode_process_transfer_text_line(
    "SPRF1 0", ParallelExecutionDomain.Parent).reason,
    "invalid-text-hex-length")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/01_unit/common/structural/transfer_contract_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering TransferEnvelopeV1 contract.
- TransferEnvelopeV1 contract

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 10 |
| Active scenarios | 10 |
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

- Canonical SPipe generation for source `b93a4ea09cbb47be706e1a9747927b96e3c541b38166258e16223eb7dbd0e87a`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `b93a4ea09cbb47be706e1a9747927b96e3c541b38166258e16223eb7dbd0e87a`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `b93a4ea09cbb47be706e1a9747927b96e3c541b38166258e16223eb7dbd0e87a`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/common/structural/transfer_contract_spec.spl
mirror: doc/06_spec/01_unit/common/structural/transfer_contract_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/common/structural/transfer_contract_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/common/structural/transfer_contract_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/common/structural/transfer_contract_spec.spl:43:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'pins the v1 vocabulary and has no raw pointer payload' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/common/structural/transfer_contract_spec.spl:55:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'requires a consuming owned move to invalidate its source' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/common/structural/transfer_contract_spec.spl:70:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'restricts scoped mutable loans to thread object handles' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

# Ssh Recv Ring Specification

> Tests covering SSH receive ring accumulates linearly, SSH receive ring frames fragmented input, SSH receive ring fails closed at its bound, SSH session reads its packet length from the ring.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 15 | 15 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Ssh Recv Ring Specification

## Scenarios

### SSH receive ring accumulates linearly

#### does one byte write per byte when fed one byte at a time

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- does one byte write per byte when fed one byte at a time


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does one byte write per byte when fed one byte at a time")
expect(_fragmented_writes(4096u64, 1u64)).to_be(4096u64)
```

</details>

#### does the same total work at 8x the fragment size

- does the same total work at 8x the fragment size


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does the same total work at 8x the fragment size")
expect(_fragmented_writes(4096u64, 8u64)).to_be(4096u64)
```

</details>

#### quadruples work for 4x the bytes, not 16x

- quadruples work for 4x the bytes, not 16x


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("quadruples work for 4x the bytes, not 16x")
val small = _fragmented_writes(1024u64, 1u64)
val large = _fragmented_writes(4096u64, 1u64)
expect(large).to_be(small * 4u64)
```

</details>

#### never exceeds one write per admitted byte

- never exceeds one write per admitted byte


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("never exceeds one write per admitted byte")
expect(_fragmented_writes(8192u64, 1u64) <= 8192u64).to_be(true)
```

</details>

### SSH receive ring frames fragmented input

#### reassembles a frame delivered one byte at a time

- reassembles a frame delivered one byte at a time


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reassembles a frame delivered one byte at a time")
var ring = ssh_recv_ring_new()
var i: u64 = 0u64
while i < 32u64:
    expect(ring.push_bytes([i.to_u8()])).to_be(true)
    i = i + 1u64
val frame = ring.take_front(32u64)
expect(frame.len()).to_be(32u64)
expect(frame[0]).to_be(0u8)
expect(frame[31]).to_be(31u8)
expect(ring.len()).to_be(0u64)
```

</details>

#### reads a big-endian length that arrives split across fragments

- reads a big-endian length that arrives split across fragments


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reads a big-endian length that arrives split across fragments")
var ring = ssh_recv_ring_new()
expect(ring.push_bytes([0u8, 0u8])).to_be(true)
expect(ring.push_bytes([1u8, 0u8])).to_be(true)
val b0 = ring.byte_at(0u64).to_u32()
val b1 = ring.byte_at(1u64).to_u32()
val b2 = ring.byte_at(2u64).to_u32()
val b3 = ring.byte_at(3u64).to_u32()
val length = (b0 * 16777216u32) + (b1 * 65536u32) + (b2 * 256u32) + b3
expect(length).to_be(256u32)
```

</details>

#### keeps trailing bytes of a coalesced two-frame read

- keeps trailing bytes of a coalesced two-frame read


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps trailing bytes of a coalesced two-frame read")
var ring = ssh_recv_ring_new()
expect(ring.push_bytes([1u8, 2u8, 3u8, 4u8, 5u8, 6u8])).to_be(true)
val first = ring.take_front(4u64)
expect(first.len()).to_be(4u64)
expect(ring.len()).to_be(2u64)
expect(ring.byte_at(0u64)).to_be(5u8)
expect(ring.byte_at(1u64)).to_be(6u8)
```

</details>

#### wraps around the physical end without corrupting bytes

- wraps around the physical end without corrupting bytes


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("wraps around the physical end without corrupting bytes")
var ring = ssh_recv_ring_new()
var filler: [u8] = []
var i: u64 = 0u64
while i < SSH_RECV_RING_CAPACITY - 4u64:
    filler.push(7u8)
    i = i + 1u64
expect(ring.push_bytes(filler)).to_be(true)
ring.discard(SSH_RECV_RING_CAPACITY - 4u64)
expect(ring.len()).to_be(0u64)
expect(ring.push_bytes([9u8, 10u8, 11u8, 12u8, 13u8, 14u8])).to_be(true)
val out = ring.take_front(6u64)
expect(out[0]).to_be(9u8)
expect(out[5]).to_be(14u8)
```

</details>

### SSH receive ring fails closed at its bound

#### rejects a fragment that does not fit, writing nothing

- rejects a fragment that does not fit, writing nothing


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects a fragment that does not fit, writing nothing")
var ring = ssh_recv_ring_new()
var over: [u8] = []
var i: u64 = 0u64
while i < SSH_RECV_RING_CAPACITY + 1u64:
    over.push(1u8)
    i = i + 1u64
expect(ring.push_bytes(over)).to_be(false)
expect(ring.len()).to_be(0u64)
expect(ring.writes).to_be(0u64)
```

</details>

#### accepts exactly its capacity and then refuses one more byte

- accepts exactly its capacity and then refuses one more byte


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("accepts exactly its capacity and then refuses one more byte")
var ring = ssh_recv_ring_new()
var full: [u8] = []
var i: u64 = 0u64
while i < SSH_RECV_RING_CAPACITY:
    full.push(2u8)
    i = i + 1u64
expect(ring.push_bytes(full)).to_be(true)
expect(ring.len()).to_be(SSH_RECV_RING_CAPACITY)
expect(ring.push_bytes([3u8])).to_be(false)
expect(ring.len()).to_be(SSH_RECV_RING_CAPACITY)
```

</details>

#### refuses to take more bytes than it holds

- refuses to take more bytes than it holds


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("refuses to take more bytes than it holds")
var ring = ssh_recv_ring_new()
expect(ring.push_bytes([1u8, 2u8])).to_be(true)
expect(ring.take_front(3u64).len()).to_be(0u64)
expect(ring.len()).to_be(2u64)
```

</details>

#### holds a maximum SSH AES-GCM frame plus one socket read

- holds a maximum SSH AES-GCM frame plus one socket read


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("holds a maximum SSH AES-GCM frame plus one socket read")
expect(SSH_RECV_RING_CAPACITY >= 35020u64 + 8192u64).to_be(true)
```

</details>

### SSH session reads its packet length from the ring

#### decodes a big-endian length spanning two fragments

- decodes a big-endian length spanning two fragments


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("decodes a big-endian length spanning two fragments")
var ring = ssh_recv_ring_new()
expect(ring.push_bytes([0u8, 0u8])).to_be(true)
expect(ring.push_bytes([0u8, 32u8])).to_be(true)
expect(ssh_recv_ring_u32_be(ring, 0u64)).to_be(32u32)
```

</details>

#### returns zero rather than reading past the buffered bytes

- returns zero rather than reading past the buffered bytes


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns zero rather than reading past the buffered bytes")
var ring = ssh_recv_ring_new()
expect(ring.push_bytes([0u8, 0u8, 0u8])).to_be(true)
expect(ssh_recv_ring_u32_be(ring, 0u64)).to_be(0u32)
```

</details>

#### still rejects a short encrypted frame

- still rejects a short encrypted frame


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("still rejects a short encrypted frame")
expect(ssh_encrypted_packet_frame_allowed([0u8, 0u8, 0u8, 1u8])).to_be(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/apps/sshd/ssh_recv_ring_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering SSH receive ring accumulates linearly, SSH receive ring frames fragmented input, SSH receive ring fails closed at its bound, SSH session reads its packet length from the ring.
- SSH receive ring accumulates linearly
- SSH receive ring frames fragmented input
- SSH receive ring fails closed at its bound
- SSH session reads its packet length from the ring

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 15 |
| Active scenarios | 15 |
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

- Canonical SPipe generation for source `5f0e4c0655240d9f79cc8ece626b646cf9d2839c8bc9092c610abf9af471d321`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `5f0e4c0655240d9f79cc8ece626b646cf9d2839c8bc9092c610abf9af471d321`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `5f0e4c0655240d9f79cc8ece626b646cf9d2839c8bc9092c610abf9af471d321`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/os/apps/sshd/ssh_recv_ring_spec.spl
mirror: doc/06_spec/01_unit/os/apps/sshd/ssh_recv_ring_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/os/apps/sshd/ssh_recv_ring_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/apps/sshd/ssh_recv_ring_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/os/apps/sshd/ssh_recv_ring_spec.spl:39:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'does one byte write per byte when fed one byte at a time' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/apps/sshd/ssh_recv_ring_spec.spl:44:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'does the same total work at 8x the fragment size' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/apps/sshd/ssh_recv_ring_spec.spl:49:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'quadruples work for 4x the bytes, not 16x' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

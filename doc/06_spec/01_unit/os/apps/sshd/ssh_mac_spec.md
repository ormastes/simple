# Ssh Mac Specification

> Tests covering ssh_mac constant-time verify, ssh_mac constant-time helper property.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Ssh Mac Specification

## Scenarios

### ssh_mac constant-time verify

#### accepts a correctly computed hmac-sha2-256-etm MAC

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- accepts a correctly computed hmac-sha2-256-etm MAC
   - Expected: computed.is_ok() is true
   - Expected: ok.is_ok() is true
   - Expected: ok.unwrap() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("accepts a correctly computed hmac-sha2-256-etm MAC")
val key = _make_key_32()
val pkt = _make_packet(16)
val computed = ssh_mac_compute("hmac-sha2-256-etm@openssh.com", key, 0, pkt)
expect(computed.is_ok()).to_equal(true)
val mac = computed.unwrap()
val ok = ssh_mac_verify("hmac-sha2-256-etm@openssh.com", key, 0, pkt, mac)
expect(ok.is_ok()).to_equal(true)
expect(ok.unwrap()).to_equal(true)
```

</details>

#### rejects a tampered MAC (single-byte flip) for hmac-sha2-256-etm

- rejects a tampered MAC (single-byte flip) for hmac-sha2-256-etm
   - Expected: computed.is_ok() is true
   - Expected: ok.is_ok() is true
   - Expected: ok.unwrap() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects a tampered MAC (single-byte flip) for hmac-sha2-256-etm")
val key = _make_key_32()
val pkt = _make_packet(16)
val computed = ssh_mac_compute("hmac-sha2-256-etm@openssh.com", key, 0, pkt)
expect(computed.is_ok()).to_equal(true)
var mac = computed.unwrap()
# Flip the first byte of the MAC
var tampered: [u8] = []
tampered.push((_u8_at(mac, 0) ^ 0xFF))
var i: u64 = 1
while i < mac.len():
    tampered.push(_u8_at(mac, i))
    i = i + 1
val ok = ssh_mac_verify("hmac-sha2-256-etm@openssh.com", key, 0, pkt, tampered)
expect(ok.is_ok()).to_equal(true)
expect(ok.unwrap()).to_equal(false)
```

</details>

#### rejects a MAC of wrong length (shorter than expected)

- rejects a MAC of wrong length (shorter than expected)
   - Expected: ok.is_ok() is true
   - Expected: ok.unwrap() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects a MAC of wrong length (shorter than expected)")
val key = _make_key_32()
val pkt = _make_packet(8)
var short_mac: [u8] = []
short_mac.push(0xAB)
short_mac.push(0xCD)
val ok = ssh_mac_verify("hmac-sha2-256-etm@openssh.com", key, 0, pkt, short_mac)
expect(ok.is_ok()).to_equal(true)
expect(ok.unwrap()).to_equal(false)
```

</details>

#### rejects a MAC of wrong length (longer than expected)

- rejects a MAC of wrong length (longer than expected)
   - Expected: computed.is_ok() is true
   - Expected: ok.is_ok() is true
   - Expected: ok.unwrap() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects a MAC of wrong length (longer than expected)")
val key = _make_key_32()
val pkt = _make_packet(8)
val computed = ssh_mac_compute("hmac-sha2-256-etm@openssh.com", key, 0, pkt)
expect(computed.is_ok()).to_equal(true)
var long_mac = computed.unwrap()
long_mac.push(0x00)
val ok = ssh_mac_verify("hmac-sha2-256-etm@openssh.com", key, 0, pkt, long_mac)
expect(ok.is_ok()).to_equal(true)
expect(ok.unwrap()).to_equal(false)
```

</details>

#### accepts a correctly computed hmac-sha2-512-etm MAC

- accepts a correctly computed hmac-sha2-512-etm MAC
   - Expected: computed.is_ok() is true
   - Expected: ok.is_ok() is true
   - Expected: ok.unwrap() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("accepts a correctly computed hmac-sha2-512-etm MAC")
val key = _make_key_64()
val pkt = _make_packet(16)
val computed = ssh_mac_compute("hmac-sha2-512-etm@openssh.com", key, 0, pkt)
expect(computed.is_ok()).to_equal(true)
val mac = computed.unwrap()
val ok = ssh_mac_verify("hmac-sha2-512-etm@openssh.com", key, 0, pkt, mac)
expect(ok.is_ok()).to_equal(true)
expect(ok.unwrap()).to_equal(true)
```

</details>

#### rejects a tampered MAC for hmac-sha2-512-etm

- rejects a tampered MAC for hmac-sha2-512-etm
   - Expected: computed.is_ok() is true
   - Expected: ok.is_ok() is true
   - Expected: ok.unwrap() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects a tampered MAC for hmac-sha2-512-etm")
val key = _make_key_64()
val pkt = _make_packet(16)
val computed = ssh_mac_compute("hmac-sha2-512-etm@openssh.com", key, 0, pkt)
expect(computed.is_ok()).to_equal(true)
var mac = computed.unwrap()
var tampered: [u8] = []
tampered.push((_u8_at(mac, 0) ^ 0x01))
var i: u64 = 1
while i < mac.len():
    tampered.push(_u8_at(mac, i))
    i = i + 1
val ok = ssh_mac_verify("hmac-sha2-512-etm@openssh.com", key, 0, pkt, tampered)
expect(ok.is_ok()).to_equal(true)
expect(ok.unwrap()).to_equal(false)
```

</details>

#### verify returns Err for unknown algorithm

- verify returns Err for unknown algorithm
   - Expected: ok.is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("verify returns Err for unknown algorithm")
val key = _make_key_32()
val pkt = _make_packet(4)
var dummy_mac: [u8] = []
dummy_mac.push(0x00)
val ok = ssh_mac_verify("hmac-unknown", key, 0, pkt, dummy_mac)
expect(ok.is_err()).to_equal(true)
```

</details>

#### none algorithm accepts empty MAC

- none algorithm accepts empty MAC
   - Expected: ok.is_ok() is true
   - Expected: ok.unwrap() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("none algorithm accepts empty MAC")
val key = _make_key_32()
val pkt = _make_packet(4)
var empty: [u8] = []
val ok = ssh_mac_verify("none", key, 0, pkt, empty)
expect(ok.is_ok()).to_equal(true)
expect(ok.unwrap()).to_equal(true)
```

</details>

### ssh_mac constant-time helper property

#### equal-content equal-length buffers compare as equal via mac_verify

- equal-content equal-length buffers compare as equal via mac_verify
   - Expected: computed.is_ok() is true
   - Expected: again.is_ok() is true
   - Expected: ok.is_ok() is true
   - Expected: ok.unwrap() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("equal-content equal-length buffers compare as equal via mac_verify")
val key = _make_key_32()
val pkt = _make_packet(4)
val computed = ssh_mac_compute("hmac-sha2-256-etm@openssh.com", key, 0, pkt)
expect(computed.is_ok()).to_equal(true)
val mac = computed.unwrap()
# Verify same value compares equal
val again = ssh_mac_compute("hmac-sha2-256-etm@openssh.com", key, 0, pkt)
expect(again.is_ok()).to_equal(true)
val ok = ssh_mac_verify("hmac-sha2-256-etm@openssh.com", key, 0, pkt, again.unwrap())
expect(ok.is_ok()).to_equal(true)
expect(ok.unwrap()).to_equal(true)
```

</details>

#### all-zero MAC of correct length is rejected for a real packet

- all-zero MAC of correct length is rejected for a real packet
   - Expected: ok.is_ok() is true
   - Expected: ok.unwrap() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("all-zero MAC of correct length is rejected for a real packet")
val key = _make_key_32()
val pkt = _make_packet(4)
# Build a 32-byte all-zero fake MAC (correct length for sha2-256 but wrong content)
var zero_mac: [u8] = []
var zi: u64 = 0
while zi < 32:
    zero_mac.push(0)
    zi = zi + 1
val ok = ssh_mac_verify("hmac-sha2-256-etm@openssh.com", key, 0, pkt, zero_mac)
expect(ok.is_ok()).to_equal(true)
expect(ok.unwrap()).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/apps/sshd/ssh_mac_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering ssh_mac constant-time verify, ssh_mac constant-time helper property.
- ssh_mac constant-time verify
- ssh_mac constant-time helper property

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

- Canonical SPipe generation for source `2fd65fccf1f31c255a12e438c4f217e78817e50415da25a780f79f065f553eaf`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `2fd65fccf1f31c255a12e438c4f217e78817e50415da25a780f79f065f553eaf`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `2fd65fccf1f31c255a12e438c4f217e78817e50415da25a780f79f065f553eaf`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/os/apps/sshd/ssh_mac_spec.spl
mirror: doc/06_spec/01_unit/os/apps/sshd/ssh_mac_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/os/apps/sshd/ssh_mac_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/apps/sshd/ssh_mac_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/os/apps/sshd/ssh_mac_spec.spl:42:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'accepts a correctly computed hmac-sha2-256-etm MAC' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/apps/sshd/ssh_mac_spec.spl:54:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects a tampered MAC (single-byte flip) for hmac-sha2-256-etm' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/apps/sshd/ssh_mac_spec.spl:73:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects a MAC of wrong length (shorter than expected)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

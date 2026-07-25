# Ssh Mac Specification

> <details>

<!-- sdn-diagram:id=ssh_mac_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=ssh_mac_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

ssh_mac_spec -> std
ssh_mac_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=ssh_mac_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Ssh Mac Specification

## Scenarios

### ssh_mac constant-time verify

#### accepts a correctly computed hmac-sha2-256-etm MAC

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

- var mac = computed unwrap
- tampered push
- tampered push
   - Expected: ok.is_ok() is true
   - Expected: ok.unwrap() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

- short mac push
- short mac push
   - Expected: ok.is_ok() is true
   - Expected: ok.unwrap() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

- var long mac = computed unwrap
- long mac push
   - Expected: ok.is_ok() is true
   - Expected: ok.unwrap() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

- var mac = computed unwrap
- tampered push
- tampered push
   - Expected: ok.is_ok() is true
   - Expected: ok.unwrap() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

- dummy mac push
   - Expected: ok.is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val key = _make_key_32()
val pkt = _make_packet(4)
var dummy_mac: [u8] = []
dummy_mac.push(0x00)
val ok = ssh_mac_verify("hmac-unknown", key, 0, pkt, dummy_mac)
expect(ok.is_err()).to_equal(true)
```

</details>

#### none algorithm accepts empty MAC

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

- zero mac push
   - Expected: ok.is_ok() is true
   - Expected: ok.unwrap() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
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

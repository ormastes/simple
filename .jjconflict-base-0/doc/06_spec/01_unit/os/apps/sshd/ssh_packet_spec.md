# Ssh Packet Specification

> <details>

<!-- sdn-diagram:id=ssh_packet_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=ssh_packet_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

ssh_packet_spec -> std
ssh_packet_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=ssh_packet_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Ssh Packet Specification

## Scenarios

### SSH packet build

#### preserves a host-key aware KEXINIT payload byte-for-byte inside the packet

- ed25519 seed:  ed25519 seed
   - Expected: ssh_get_u32(packet, 0).to_u64() equals `packet.len() - 4`
   - Expected: _u8_at(packet, 4) equals `5`
   - Expected: _u8_at(packet, 5) equals `20`
   - Expected: _u8_at(packet, 5 + i) equals `_u8_at(payload, i)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val payload = ssh_build_kexinit_for_host_keys(HostKeySet(
    ed25519_seed: _ed25519_seed(),
    rsa_pkcs8: nil,
    rsa_public_blob: nil,
    ecdsa_p256_pkcs8: nil
))
val packet = ssh_packet_build(payload, 0)

expect(ssh_get_u32(packet, 0).to_u64()).to_equal(packet.len() - 4)
expect(_u8_at(packet, 4)).to_equal(5)
expect(_u8_at(packet, 5)).to_equal(20)

var i: u64 = 0
while i < payload.len():
    expect(_u8_at(packet, 5 + i)).to_equal(_u8_at(payload, i))
    i = i + 1
```

</details>

#### keeps the expected KEXINIT wire prefix after packet wrapping

- ed25519 seed:  ed25519 seed


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val payload = ssh_build_kexinit_for_host_keys(HostKeySet(
    ed25519_seed: _ed25519_seed(),
    rsa_pkcs8: nil,
    rsa_public_blob: nil,
    ecdsa_p256_pkcs8: nil
))
val packet = ssh_packet_build(payload, 0)
_expect_prefix(
    packet,
    "000000c405140000000000000000000000000000000000000039637572766532353531392d7368613235362c6578742d696e666f2d732c6b65782d7374726963742d732d763030406f70656e7373682e636f6d"
)
```

</details>

#### round-trips a host-key aware KEXINIT packet through ssh_packet_read

- ed25519 seed:  ed25519 seed
   - Expected: parsed.is_ok() is true
   - Expected: pair.consumed equals `packet.len()`
   - Expected: pair.packet.payload.len() equals `payload.len()`
   - Expected: _u8_at(pair.packet.payload, i) equals `_u8_at(payload, i)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val payload = ssh_build_kexinit_for_host_keys(HostKeySet(
    ed25519_seed: _ed25519_seed(),
    rsa_pkcs8: nil,
    rsa_public_blob: nil,
    ecdsa_p256_pkcs8: nil
))
val packet = ssh_packet_build(payload, 0)
val parsed = ssh_packet_read(packet, 0)
expect(parsed.is_ok()).to_equal(true)
val pair = parsed.unwrap()
expect(pair.consumed).to_equal(packet.len())
expect(pair.packet.payload.len()).to_equal(payload.len())

var i: u64 = 0
while i < payload.len():
    expect(_u8_at(pair.packet.payload, i)).to_equal(_u8_at(payload, i))
    i = i + 1
```

</details>

#### does not zero out payload bytes after the first length field

- ed25519 seed:  ed25519 seed
   - Expected: _u8_at(packet, 22) equals `0`
   - Expected: _u8_at(packet, 23) equals `0`
   - Expected: _u8_at(packet, 24) equals `0`
   - Expected: _u8_at(packet, 25) equals `57`
   - Expected: _u8_at(packet, 26) equals `0x63`
   - Expected: _u8_at(packet, 27) equals `0x75`
   - Expected: _u8_at(packet, 28) equals `0x72`
   - Expected: _u8_at(packet, 29) equals `0x76`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val payload = ssh_build_kexinit_for_host_keys(HostKeySet(
    ed25519_seed: _ed25519_seed(),
    rsa_pkcs8: nil,
    rsa_public_blob: nil,
    ecdsa_p256_pkcs8: nil
))
val packet = ssh_packet_build(payload, 0)

expect(_u8_at(packet, 22)).to_equal(0)
expect(_u8_at(packet, 23)).to_equal(0)
expect(_u8_at(packet, 24)).to_equal(0)
expect(_u8_at(packet, 25)).to_equal(57)
expect(_u8_at(packet, 26)).to_equal(0x63)
expect(_u8_at(packet, 27)).to_equal(0x75)
expect(_u8_at(packet, 28)).to_equal(0x72)
expect(_u8_at(packet, 29)).to_equal(0x76)
```

</details>

### SSH packet read errors

#### returns Err when fewer than 5 bytes are available

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val truncated = _hex_decode("0000009c")
val parsed = ssh_packet_read(truncated, 0)
expect(parsed.is_err()).to_equal(true)
expect(parsed.err().unwrap()).to_equal("ssh_packet_read: need at least 5 bytes")
```

</details>

#### returns Err when packet_length is smaller than 2

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val invalid = _hex_decode("0000000100")
val parsed = ssh_packet_read(invalid, 0)
expect(parsed.is_err()).to_equal(true)
expect(parsed.err().unwrap()).to_equal("ssh_packet_read: packet_length too small")
```

</details>

#### returns Err when packet bytes are incomplete

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val truncated = _hex_decode("0000001005")
val parsed = ssh_packet_read(truncated, 0)
expect(parsed.is_err()).to_equal(true)
expect(parsed.err().unwrap()).to_equal("ssh_packet_read: incomplete packet")
```

</details>

#### returns Err when padding exceeds packet_length

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val invalid = _hex_decode("000000020200")
val parsed = ssh_packet_read(invalid, 0)
expect(parsed.is_err()).to_equal(true)
expect(parsed.err().unwrap()).to_equal("ssh_packet_read: padding exceeds packet")
```

</details>

### SSH mpint encoding

#### preserves the raw X25519 byte string order for SSH mpint encoding

- encoded = ssh put mpint
-  expect prefix


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var encoded: [u8] = []
encoded = ssh_put_mpint(encoded, [0x01, 0x02, 0x03, 0x04])
_expect_prefix(encoded, "0000000401020304")
```

</details>

#### prepends a sign pad without reversing the byte string

- encoded = ssh put mpint
-  expect prefix


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var encoded: [u8] = []
encoded = ssh_put_mpint(encoded, [0x80, 0x01, 0x02, 0x03])
_expect_prefix(encoded, "000000050080010203")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/apps/sshd/ssh_packet_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- SSH packet build
- SSH packet read errors
- SSH mpint encoding

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 10 |
| Active scenarios | 10 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

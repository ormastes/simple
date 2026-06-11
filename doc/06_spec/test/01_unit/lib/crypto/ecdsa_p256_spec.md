# Ecdsa P256 Specification

> <details>

<!-- sdn-diagram:id=ecdsa_p256_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=ecdsa_p256_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

ecdsa_p256_spec -> std
ecdsa_p256_spec -> os
ecdsa_p256_spec -> test
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=ecdsa_p256_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 14 | 14 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Ecdsa P256 Specification

## Scenarios

### ECDSA-P256 SSH mpint round-trip (pure Simple)

#### fixed64_to_ssh_mpint_pair produces non-empty output for well-formed 64-byte sig

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sig = _mpint_fixed64()
val wire = fixed64_to_ssh_mpint_pair(sig)
expect(wire.len() > 0).to_equal(true)
```

</details>

#### ssh_mpint_pair_to_fixed64 inverts fixed64_to_ssh_mpint_pair

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sig = _mpint_fixed64()
val wire = fixed64_to_ssh_mpint_pair(sig)
val recovered = ssh_mpint_pair_to_fixed64(wire)
expect(recovered).to_equal(sig)
```

</details>

#### fixed64_to_ssh_mpint_pair pads high-bit-set s component with 0x00

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# s starts with 0x81 (high bit set), so mpint length must be 33
val sig = _mpint_fixed64()
val wire = fixed64_to_ssh_mpint_pair(sig)
# r: no high bit — mpint len = 32; r consumes 4+32 = 36 bytes
# s: high bit set — mpint len = 33; s offset = 36; s len prefix at [36..39]
val s_len: i64 = (wire[36u64].to_i64() << 24) | (wire[37u64].to_i64() << 16) | (wire[38u64].to_i64() << 8) | wire[39u64].to_i64()
expect(s_len).to_equal(33)
```

</details>

#### fixed64_to_ssh_mpint_pair returns empty for sig shorter than 64 bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val short_sig: [u8] = [0x01u8, 0x02u8, 0x03u8]
val result = fixed64_to_ssh_mpint_pair(short_sig)
expect(result.len()).to_equal(0)
```

</details>

#### ssh_mpint_pair_to_fixed64 returns empty for truncated wire input

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val truncated: [u8] = [0x00u8, 0x00u8, 0x00u8, 0x04u8, 0x01u8, 0x02u8, 0x03u8, 0x04u8]
val result = ssh_mpint_pair_to_fixed64(truncated)
expect(result.len()).to_equal(0)
```

</details>

### ECDSA-P256-SHA-256 round-trip sign + verify

#### sign returns a 64-byte signature

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sig = ecdsa_p256_sign_fixed(_pkcs8(), [])
expect(sig.len()).to_equal(64)
```

</details>

#### signs and verifies an empty message

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sig = ecdsa_p256_sign_fixed(_pkcs8(), [])
val ok = ecdsa_p256_verify_fixed(_spki(), [], sig)
expect(ok).to_equal(true)
```

</details>

#### signs and verifies a short ASCII message

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val msg: [u8] = [0x68u8, 0x65u8, 0x6cu8, 0x6cu8, 0x6fu8]
val sig = ecdsa_p256_sign_fixed(_pkcs8(), msg)
val ok = ecdsa_p256_verify_fixed(_spki(), msg, sig)
expect(ok).to_equal(true)
```

</details>

#### signature is rejected under a different public key

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val msg: [u8] = [0x68u8, 0x65u8, 0x6cu8, 0x6cu8, 0x6fu8]
val sig = ecdsa_p256_sign_fixed(_pkcs8(), msg)
# Use CAVP public key — different from the signer's key
val ok = ecdsa_p256_verify_fixed(_cavp_spki(), msg, sig)
expect(ok).to_equal(false)
```

</details>

#### signature is rejected when the first byte is flipped

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val msg: [u8] = [0x68u8, 0x65u8, 0x6cu8, 0x6cu8, 0x6fu8]
val sig = ecdsa_p256_sign_fixed(_pkcs8(), msg)
val bad_sig = _flip_byte(sig, 0)
val ok = ecdsa_p256_verify_fixed(_spki(), msg, bad_sig)
expect(ok).to_equal(false)
```

</details>

#### signature is rejected when the message is modified

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val msg: [u8] = [0x68u8, 0x65u8, 0x6cu8, 0x6cu8, 0x6fu8]
val sig = ecdsa_p256_sign_fixed(_pkcs8(), msg)
val bad_msg: [u8] = [0x68u8, 0x65u8, 0x6cu8, 0x6cu8, 0x6fu8, 0x21u8]
val ok = ecdsa_p256_verify_fixed(_spki(), bad_msg, sig)
expect(ok).to_equal(false)
```

</details>

### ECDSA-P256-SHA-256 NIST CAVP SigVer

#### NIST CAVP P-256 SHA-256 vector verifies (Result = P)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ok = ecdsa_p256_verify_fixed(_cavp_spki(), _cavp_msg(), _cavp_sig_fixed64())
expect(ok).to_equal(true)
```

</details>

#### NIST CAVP vector is rejected when signature r-byte is flipped

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bad_sig = _flip_byte(_cavp_sig_fixed64(), 0)
val ok = ecdsa_p256_verify_fixed(_cavp_spki(), _cavp_msg(), bad_sig)
expect(ok).to_equal(false)
```

</details>

#### NIST CAVP vector is rejected when message is truncated

1. short msg push
   - Expected: ok is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val full_msg = _cavp_msg()
var short_msg: [u8] = []
var i: i64 = 0
while i < 10:
    short_msg.push(full_msg[i.to_u64()])
    i = i + 1
val ok = ecdsa_p256_verify_fixed(_cavp_spki(), short_msg, _cavp_sig_fixed64())
expect(ok).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/crypto/ecdsa_p256_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- ECDSA-P256 SSH mpint round-trip (pure Simple)
- ECDSA-P256-SHA-256 round-trip sign + verify
- ECDSA-P256-SHA-256 NIST CAVP SigVer

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 14 |
| Active scenarios | 14 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

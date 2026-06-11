# Ecc P384 P521 Kat Specification

> <details>

<!-- sdn-diagram:id=ecc_p384_p521_kat_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=ecc_p384_p521_kat_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

ecc_p384_p521_kat_spec -> std
ecc_p384_p521_kat_spec -> os
ecc_p384_p521_kat_spec -> test
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=ecc_p384_p521_kat_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 24 | 24 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Ecc P384 P521 Kat Specification

## Scenarios

### ECDSA-P-384 NIST CAVP SigVer

#### NIST CAVP P-384 SHA-384 vector verifies (Result = P)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ok = ecdsa_p384_verify_fixed(_cavp384_pubkey(), _cavp384_msg(), _cavp384_sig_fixed96())
expect(ok).to_equal(true)
```

</details>

#### NIST CAVP P-384 vector is rejected when signature r-byte is flipped

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bad_sig = _flip_byte(_cavp384_sig_fixed96(), 0)
val ok = ecdsa_p384_verify_fixed(_cavp384_pubkey(), _cavp384_msg(), bad_sig)
expect(ok).to_equal(false)
```

</details>

#### NIST CAVP P-384 vector is rejected when signature s-byte is flipped

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bad_sig = _flip_byte(_cavp384_sig_fixed96(), 48)
val ok = ecdsa_p384_verify_fixed(_cavp384_pubkey(), _cavp384_msg(), bad_sig)
expect(ok).to_equal(false)
```

</details>

#### NIST CAVP P-384 vector is rejected when message is truncated

1. short msg push
   - Expected: ok is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val full_msg = _cavp384_msg()
var short_msg: [u8] = []
var i: i64 = 0
while i < 10:
    short_msg.push(full_msg[i.to_u64()])
    i = i + 1
val ok = ecdsa_p384_verify_fixed(_cavp384_pubkey(), short_msg, _cavp384_sig_fixed96())
expect(ok).to_equal(false)
```

</details>

#### NIST CAVP P-384 vector is rejected under wrong public key

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ok = ecdsa_p384_verify_fixed(_p384_pubkey(), _cavp384_msg(), _cavp384_sig_fixed96())
expect(ok).to_equal(false)
```

</details>

### ECDSA-P-384 round-trip sign + verify

#### sign returns a 96-byte signature

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sig = ecdsa_p384_sign_fixed(_p384_privkey(), [])
expect(sig.len()).to_equal(96)
```

</details>

#### signs and verifies an empty message

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sig = ecdsa_p384_sign_fixed(_p384_privkey(), [])
val ok = ecdsa_p384_verify_fixed(_p384_pubkey(), [], sig)
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
val sig = ecdsa_p384_sign_fixed(_p384_privkey(), msg)
val ok = ecdsa_p384_verify_fixed(_p384_pubkey(), msg, sig)
expect(ok).to_equal(true)
```

</details>

#### RFC 6979 is deterministic: same message produces same signature

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val msg: [u8] = [0x61u8, 0x62u8, 0x63u8]
val sig1 = ecdsa_p384_sign_fixed(_p384_privkey(), msg)
val sig2 = ecdsa_p384_sign_fixed(_p384_privkey(), msg)
expect(sig1.len()).to_equal(96)
expect(sig1.len()).to_equal(sig2.len())
var all_match: bool = true
var i: i64 = 0
while i < sig1.len().to_i64():
    if sig1[i.to_u64()] != sig2[i.to_u64()]:
        all_match = false
    i = i + 1
expect(all_match).to_equal(true)
```

</details>

#### signature is rejected under a different public key

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val msg: [u8] = [0x68u8, 0x65u8, 0x6cu8, 0x6cu8, 0x6fu8]
val sig = ecdsa_p384_sign_fixed(_p384_privkey(), msg)
val ok = ecdsa_p384_verify_fixed(_cavp384_pubkey(), msg, sig)
expect(ok).to_equal(false)
```

</details>

#### signature is rejected when the first r-byte is flipped

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val msg: [u8] = [0x68u8, 0x65u8, 0x6cu8, 0x6cu8, 0x6fu8]
val sig = ecdsa_p384_sign_fixed(_p384_privkey(), msg)
val bad_sig = _flip_byte(sig, 0)
val ok = ecdsa_p384_verify_fixed(_p384_pubkey(), msg, bad_sig)
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
val sig = ecdsa_p384_sign_fixed(_p384_privkey(), msg)
val bad_msg: [u8] = [0x68u8, 0x65u8, 0x6cu8, 0x6cu8, 0x6fu8, 0x21u8]
val ok = ecdsa_p384_verify_fixed(_p384_pubkey(), bad_msg, sig)
expect(ok).to_equal(false)
```

</details>

### ECDSA-P-384 SSH mpint helper

#### fixed96_to_ssh_mpint_pair returns non-empty output for 96-byte sig

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sig = ecdsa_p384_sign_fixed(_p384_privkey(), [])
val wire = fixed96_to_ssh_mpint_pair(sig)
expect(wire.len() > 0).to_equal(true)
```

</details>

#### fixed96_to_ssh_mpint_pair returns empty for wrong-length input

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val wire = fixed96_to_ssh_mpint_pair([0x01u8, 0x02u8])
expect(wire.len()).to_equal(0)
```

</details>

### ECDSA-P-521 NIST CAVP SigVer

#### NIST CAVP P-521 SHA-512 vector verifies (Result = P)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ok = ecdsa_p521_verify_fixed(_cavp521_pubkey(), _cavp521_msg(), _cavp521_sig_fixed132())
expect(ok).to_equal(true)
```

</details>

#### NIST CAVP P-521 vector is rejected when signature r-byte is flipped

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bad_sig = _flip_byte(_cavp521_sig_fixed132(), 0)
val ok = ecdsa_p521_verify_fixed(_cavp521_pubkey(), _cavp521_msg(), bad_sig)
expect(ok).to_equal(false)
```

</details>

#### NIST CAVP P-521 vector is rejected when signature s-byte is flipped

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bad_sig = _flip_byte(_cavp521_sig_fixed132(), 66)
val ok = ecdsa_p521_verify_fixed(_cavp521_pubkey(), _cavp521_msg(), bad_sig)
expect(ok).to_equal(false)
```

</details>

#### NIST CAVP P-521 vector is rejected when message is truncated

1. short msg push
   - Expected: ok is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val full_msg = _cavp521_msg()
var short_msg: [u8] = []
var i: i64 = 0
while i < 10:
    short_msg.push(full_msg[i.to_u64()])
    i = i + 1
val ok = ecdsa_p521_verify_fixed(_cavp521_pubkey(), short_msg, _cavp521_sig_fixed132())
expect(ok).to_equal(false)
```

</details>

#### NIST CAVP P-521 vector is rejected under wrong public key

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ok = ecdsa_p521_verify_fixed(_p521_pubkey(), _cavp521_msg(), _cavp521_sig_fixed132())
expect(ok).to_equal(false)
```

</details>

### ECDSA-P-521 round-trip sign + verify

#### sign returns a 132-byte signature

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sig = ecdsa_p521_sign_fixed(_p521_privkey(), [])
expect(sig.len()).to_equal(132)
```

</details>

#### signs and verifies an empty message

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sig = ecdsa_p521_sign_fixed(_p521_privkey(), [])
val ok = ecdsa_p521_verify_fixed(_p521_pubkey(), [], sig)
expect(ok).to_equal(true)
```

</details>

#### RFC 6979 is deterministic: same message produces same signature

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val msg: [u8] = [0x61u8, 0x62u8, 0x63u8]
val sig1 = ecdsa_p521_sign_fixed(_p521_privkey(), msg)
val sig2 = ecdsa_p521_sign_fixed(_p521_privkey(), msg)
expect(sig1.len()).to_equal(132)
expect(sig1.len()).to_equal(sig2.len())
var all_match: bool = true
var i: i64 = 0
while i < sig1.len().to_i64():
    if sig1[i.to_u64()] != sig2[i.to_u64()]:
        all_match = false
    i = i + 1
expect(all_match).to_equal(true)
```

</details>

#### signature is rejected under a different public key

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val msg: [u8] = [0x68u8, 0x65u8, 0x6cu8, 0x6cu8, 0x6fu8]
val sig = ecdsa_p521_sign_fixed(_p521_privkey(), msg)
val ok = ecdsa_p521_verify_fixed(_cavp521_pubkey(), msg, sig)
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
val sig = ecdsa_p521_sign_fixed(_p521_privkey(), msg)
val bad_msg: [u8] = [0x68u8, 0x65u8, 0x6cu8, 0x6cu8, 0x6fu8, 0x21u8]
val ok = ecdsa_p521_verify_fixed(_p521_pubkey(), bad_msg, sig)
expect(ok).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/crypto/ecc_p384_p521_kat_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- ECDSA-P-384 NIST CAVP SigVer
- ECDSA-P-384 round-trip sign + verify
- ECDSA-P-384 SSH mpint helper
- ECDSA-P-521 NIST CAVP SigVer
- ECDSA-P-521 round-trip sign + verify

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 24 |
| Active scenarios | 24 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

# Cert Verify Ed25519 Specification

> <details>

<!-- sdn-diagram:id=cert_verify_ed25519_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=cert_verify_ed25519_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

cert_verify_ed25519_spec -> std
cert_verify_ed25519_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=cert_verify_ed25519_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Cert Verify Ed25519 Specification

## Scenarios

### verify_certificate_verify_msg_scheme Ed25519 (0x0807)

#### verifies a valid Ed25519 CertificateVerify message

<details>
<summary>Executable SPipe</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pubkey = _pubkey_a()
val sig = _sign_content()
val result = verify_certificate_verify_msg_scheme(pubkey, 0x0807u16, _transcript_hash(), sig)
if val CertVerifyResult.Ok = result:
    expect(pubkey.len()).to_equal(32u64)
    expect(sig.len()).to_equal(64u64)
else:
    expect(false).to_equal(true)
```

</details>

#### rejects signature verified under a different public key

<details>
<summary>Executable SPipe</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val other_pubkey = _pubkey_b()
val sig = _sign_content()
val result = verify_certificate_verify_msg_scheme(other_pubkey, 0x0807u16, _transcript_hash(), sig)
if val CertVerifyResult.Err(err_msg) = result:
    expect(other_pubkey.len()).to_equal(32u64)
    expect(err_msg.len()).to_be_greater_than(40u64)
    expect(err_msg == "unsupported signature scheme").to_equal(false)
else:
    expect(false).to_equal(true)
```

</details>

#### rejects a signature with a flipped byte

<details>
<summary>Executable SPipe</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pubkey = _pubkey_a()
val sig = _sign_content()
val bad_sig = _flip_byte_at(sig, 4u64)
val result = verify_certificate_verify_msg_scheme(pubkey, 0x0807u16, _transcript_hash(), bad_sig)
if val CertVerifyResult.Err(err_msg) = result:
    expect(bad_sig.len()).to_equal(64u64)
    expect(err_msg.len()).to_be_greater_than(40u64)
    expect(err_msg == "unsupported signature scheme").to_equal(false)
else:
    expect(false).to_equal(true)
```

</details>

#### rejects an unknown sig_scheme

<details>
<summary>Executable SPipe</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pubkey = _pubkey_a()
val sig = _sign_content()
val result = verify_certificate_verify_msg_scheme(pubkey, 0x0000u16, _transcript_hash(), sig)
if val CertVerifyResult.Err(err_msg) = result:
    expect(err_msg).to_equal("unsupported signature scheme")
else:
    expect(false).to_equal(true)
```

</details>

### verify_certificate_verify_msg shim

#### delegates to Ed25519 and accepts a valid signature

<details>
<summary>Executable SPipe</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pubkey = _pubkey_a()
val sig = _sign_content()
val result = verify_certificate_verify_msg(pubkey, _transcript_hash(), sig)
if val CertVerifyResult.Ok = result:
    expect(pubkey.len()).to_equal(32u64)
    expect(sig.len()).to_equal(64u64)
else:
    expect(false).to_equal(true)
```

</details>

#### delegates to Ed25519 and rejects a bad signature

<details>
<summary>Executable SPipe</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pubkey = _pubkey_a()
val sig = _sign_content()
val bad_sig = _flip_byte_at(sig, 0u64)
val result = verify_certificate_verify_msg(pubkey, _transcript_hash(), bad_sig)
if val CertVerifyResult.Err(err_msg) = result:
    expect(bad_sig.len()).to_equal(64u64)
    expect(err_msg.len()).to_be_greater_than(40u64)
    expect(err_msg == "unsupported signature scheme").to_equal(false)
else:
    expect(false).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/tls13/cert_verify_ed25519_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- verify_certificate_verify_msg_scheme Ed25519 (0x0807)
- verify_certificate_verify_msg shim

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

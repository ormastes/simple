# Ecdsa P256 Specification

> <details>

<!-- sdn-diagram:id=ecdsa_p256_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=ecdsa_p256_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

ecdsa_p256_spec -> std
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
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Ecdsa P256 Specification

## Scenarios

### ECDSA-P256-SHA-256 common wrapper — round-trip sign+verify

#### sign returns a 64-byte signature for empty message

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sig = ecdsa_p256_sign(_pkcs8_bytes(), [])
expect(sig.len()).to_equal(64)
```

</details>

#### sign returns a 64-byte signature for short message

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sig = ecdsa_p256_sign(_pkcs8_bytes(), _hello_msg())
expect(sig.len()).to_equal(64)
```

</details>

#### signs and verifies an empty message

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sig = ecdsa_p256_sign(_pkcs8_bytes(), [])
val ok = ecdsa_p256_verify(_spki_bytes(), [], sig)
expect(ok).to_equal(true)
```

</details>

#### signs and verifies a short ASCII message

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sig = ecdsa_p256_sign(_pkcs8_bytes(), _hello_msg())
val ok = ecdsa_p256_verify(_spki_bytes(), _hello_msg(), sig)
expect(ok).to_equal(true)
```

</details>

#### signature is rejected under a different public key

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sig = ecdsa_p256_sign(_pkcs8_bytes(), _hello_msg())
val ok = ecdsa_p256_verify(_cavp_spki(), _hello_msg(), sig)
expect(ok).to_equal(false)
```

</details>

#### returns empty for invalid (empty) private key

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sig = ecdsa_p256_sign([], _hello_msg())
expect(sig.len()).to_equal(0)
```

</details>

### ECDSA-P256-SHA-256 common wrapper — NIST CAVP SigVer

#### NIST CAVP P-256 SHA-256 vector verifies (Result = P)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ok = ecdsa_p256_verify(_cavp_spki(), _cavp_msg(), _cavp_sig())
expect(ok).to_equal(true)
```

</details>

#### verify returns false for empty public key

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ok = ecdsa_p256_verify([], _cavp_msg(), _cavp_sig())
expect(ok).to_equal(false)
```

</details>

#### verify returns false for empty signature

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ok = ecdsa_p256_verify(_cavp_spki(), _cavp_msg(), [])
expect(ok).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/crypto/ecdsa_p256_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- ECDSA-P256-SHA-256 common wrapper — round-trip sign+verify
- ECDSA-P256-SHA-256 common wrapper — NIST CAVP SigVer

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

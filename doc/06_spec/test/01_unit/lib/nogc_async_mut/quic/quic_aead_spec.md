# Quic Aead Specification

> <details>

<!-- sdn-diagram:id=quic_aead_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=quic_aead_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

quic_aead_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=quic_aead_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Quic Aead Specification

## Scenarios

### QUIC packet AEAD — binary AES-128-GCM (RFC 9001 §5.3, §A.2 keys)

#### encrypts to the OpenSSL-verified ciphertext+tag

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_enc()).to_equal(_EXPECT_CT)
```

</details>

#### decrypts (round-trip) back to the plaintext

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_dec()).to_equal("01020304")
```

</details>

#### rejects a tampered ciphertext (auth failure -> empty)

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_dec_tampered()).to_equal("")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_async_mut/quic/quic_aead_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- QUIC packet AEAD — binary AES-128-GCM (RFC 9001 §5.3, §A.2 keys)

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

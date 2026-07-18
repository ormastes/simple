# Cose Rfc9052 Kat Specification

> <details>

<!-- sdn-diagram:id=cose_rfc9052_kat_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=cose_rfc9052_kat_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

cose_rfc9052_kat_spec -> std
cose_rfc9052_kat_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=cose_rfc9052_kat_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Cose Rfc9052 Kat Specification

## Scenarios

### COSE_Mac0 (RFC 9052 §6.2 / RFC 8152 C.5, HS256)

#### round-trip: create then verify succeeds with correct key

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_mac0_roundtrip_ok()).to_equal(true)
```

</details>

#### round-trip: recovered payload matches original

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_mac0_roundtrip_payload_intact()).to_equal(true)
```

</details>

#### rejects verification with wrong key (constant-time path)

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_mac0_wrong_key_rejected()).to_equal(true)
```

</details>

#### handles empty payload round-trip

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_mac0_empty_payload_ok()).to_equal(true)
```

</details>

#### KAT: wire encoding length meets RFC 8152 C.5 minimum (≥63 bytes)

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_mac0_kat_length_ok()).to_equal(true)
```

</details>

#### tampered MAC tag byte is rejected

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_mac0_tampered_tag_rejected()).to_equal(true)
```

</details>

#### tampered payload byte is rejected (MAC recompute mismatch)

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_mac0_tampered_payload_rejected()).to_equal(true)
```

</details>

#### different keys produce different COSE_Mac0 wire bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_mac0_different_keys_different_bytes()).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/crypto/cose_rfc9052_kat_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- COSE_Mac0 (RFC 9052 §6.2 / RFC 8152 C.5, HS256)

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

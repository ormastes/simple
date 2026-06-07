# P384 Public Input Validation Specification

> <details>

<!-- sdn-diagram:id=p384_public_input_validation_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=p384_public_input_validation_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

p384_public_input_validation_spec -> std
p384_public_input_validation_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=p384_public_input_validation_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# P384 Public Input Validation Specification

## Scenarios

### P-384 public input validation

#### rejects off-curve public key in ECDSA verify

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bad_pub = _tampered_pubkey()
val verified = p384_ecdsa_verify(bad_pub, _zeros(48), _zeros(96))
expect(not verified).to_equal(true)
```

</details>

#### rejects off-curve peer public key in ECDH

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bad_pub = _tampered_pubkey()
expect(p384_ecdh(_make_key(0x6B), bad_pub).len()).to_equal(0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/crypto/p384_public_input_validation_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- P-384 public input validation

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

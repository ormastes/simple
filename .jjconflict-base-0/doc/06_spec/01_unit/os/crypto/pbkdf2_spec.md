# Pbkdf2 Specification

> <details>

<!-- sdn-diagram:id=pbkdf2_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=pbkdf2_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

pbkdf2_spec -> std
pbkdf2_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=pbkdf2_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Pbkdf2 Specification

## Scenarios

### PBKDF2-HMAC-SHA-256 — KAT (RFC 2898/8018)

#### V1: password-field='password' salt='salt' c=1 dkLen=32

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val hex = _compute_v1()
expect(hex).to_equal(
    "120fb6cffcf8b32c43e7225256c4f837a86548c92ccc35480805987cb70be17b"
)
```

</details>

#### V2: password-field='password' salt='salt' c=2 dkLen=32

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val hex = _compute_v2()
expect(hex).to_equal(
    "ae4d0c95af6b46d32d0adff928f06dd02a303f8ef3c251dfd6e2d85a95474c43"
)
```

</details>

#### V3: password-field='passwd' salt='salt' c=1 dkLen=64 (RFC 7914 §11)

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val hex = _compute_v3()
expect(hex).to_equal(
    "55ac046e56e3089fec1691c22544b605f94185216dde0465e68b9d57c20dacbc49ca9cccf179b645991664b39d77ef317c71b845b1e30bd509112041d3a19783"
)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/crypto/pbkdf2_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- PBKDF2-HMAC-SHA-256 — KAT (RFC 2898/8018)

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

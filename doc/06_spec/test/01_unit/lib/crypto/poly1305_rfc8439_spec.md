# Poly1305 Rfc8439 Specification

> <details>

<!-- sdn-diagram:id=poly1305_rfc8439_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=poly1305_rfc8439_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

poly1305_rfc8439_spec -> std
poly1305_rfc8439_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=poly1305_rfc8439_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Poly1305 Rfc8439 Specification

## Scenarios

### Poly1305 RFC 8439 §2.5.2 canonical test

#### MAC of 'Cryptographic Forum Research Group' → a8061dc1305136c6c22b8baf0c0127a9

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(poly1305_mac(KEY_252, MSG_252)).to_equal(EXPECTED_TAG_252)
```

</details>

### Poly1305 RFC 8439 §A.3 additional vectors

#### Test #1: zero key + 64-byte zero message → 16-byte zero tag

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(poly1305_mac(KEY_ZERO, MSG_ZERO)).to_equal(TAG_ZERO)
```

</details>

#### Test #4: Carroll Jabberwocky quote 127 bytes → 4541669a7eaaee61e708dc7cbcc5eb62

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(poly1305_mac(KEY_TEST4, MSG_TEST4)).to_equal(EXPECTED_TAG_TEST4)
```

</details>

### Poly1305 tag length

#### poly1305_mac always returns exactly 16 bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(poly1305_mac(KEY_252, MSG_252).len()).to_equal(16)
```

</details>

#### poly1305_mac on zero key returns exactly 16 bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(poly1305_mac(KEY_ZERO, MSG_ZERO).len()).to_equal(16)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/crypto/poly1305_rfc8439_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Poly1305 RFC 8439 §2.5.2 canonical test
- Poly1305 RFC 8439 §A.3 additional vectors
- Poly1305 tag length

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

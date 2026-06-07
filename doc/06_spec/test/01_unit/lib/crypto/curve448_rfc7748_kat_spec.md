# Curve448 Rfc7748 Kat Specification

> <details>

<!-- sdn-diagram:id=curve448_rfc7748_kat_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=curve448_rfc7748_kat_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

curve448_rfc7748_kat_spec -> std
curve448_rfc7748_kat_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=curve448_rfc7748_kat_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Curve448 Rfc7748 Kat Specification

## Scenarios

### Curve448 RFC 7748 §5.2 single scalar-mult test vectors

#### TV1: scalar 3d262fdd... × u 06fce640... → ce3e4ff9...

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(x448_scalar_mult(SCALAR_TV1, U_TV1)).to_equal(EXPECTED_TV1)
```

</details>

#### TV2: scalar 203d4944... × u 0fbcc2f9... → 884a0257...

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(x448_scalar_mult(SCALAR_TV2, U_TV2)).to_equal(EXPECTED_TV2)
```

</details>

### Curve448 RFC 7748 §5.2 iterated scalar-mult (1 iteration)

#### after 1 iteration from BASE_POINT: 3f482c8a...

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(x448_scalar_mult(BASE_POINT_448, BASE_POINT_448)).to_equal(EXPECTED_ITER1)
```

</details>

### Curve448 RFC 7748 §6.2 ECDH key exchange

#### Alice public key: x448_keygen(alice_priv)[1] == alice_pub

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val kp = x448_keygen(ALICE_PRIV_448)
expect(kp[1]).to_equal(ALICE_PUB_448)
```

</details>

#### Bob public key: x448_keygen(bob_priv)[1] == bob_pub

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val kp = x448_keygen(BOB_PRIV_448)
expect(kp[1]).to_equal(BOB_PUB_448)
```

</details>

#### Alice computes shared secret: x448_dh(alice_priv, bob_pub) == shared

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(x448_dh(ALICE_PRIV_448, BOB_PUB_448)).to_equal(SHARED_SECRET_448)
```

</details>

#### Bob computes shared secret: x448_dh(bob_priv, alice_pub) == shared

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(x448_dh(BOB_PRIV_448, ALICE_PUB_448)).to_equal(SHARED_SECRET_448)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/crypto/curve448_rfc7748_kat_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Curve448 RFC 7748 §5.2 single scalar-mult test vectors
- Curve448 RFC 7748 §5.2 iterated scalar-mult (1 iteration)
- Curve448 RFC 7748 §6.2 ECDH key exchange

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

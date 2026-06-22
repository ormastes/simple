# Curve25519 Rfc7748 Specification

> <details>

<!-- sdn-diagram:id=curve25519_rfc7748_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=curve25519_rfc7748_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

curve25519_rfc7748_spec -> std
curve25519_rfc7748_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=curve25519_rfc7748_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Curve25519 Rfc7748 Specification

## Scenarios

### Curve25519 RFC 7748 §5.2 single scalar-mult test vectors

#### TV1: scalar a546e36b... × u e6db6867... → c3da5537...

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(x25519(SCALAR_TV1, U_TV1)).to_equal(EXPECTED_TV1)
```

</details>

#### TV2: scalar 4b66e9d4... × u e5210f12... → 95cbde94...

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(x25519(SCALAR_TV2, U_TV2)).to_equal(EXPECTED_TV2)
```

</details>

### Curve25519 RFC 7748 §5.2 iterated scalar-mult

#### after 1 iteration starting from BASE_POINT: 422c8e7a...

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(x25519(BASE_POINT, BASE_POINT)).to_equal(EXPECTED_AFTER_1_ITER)
```

</details>

### Curve25519 RFC 7748 §6.1 ECDH key exchange

#### Alice public key: x25519(alice_priv, base) == alice_pub

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(x25519_base(ALICE_PRIV)).to_equal(ALICE_PUB)
```

</details>

#### Bob public key: x25519(bob_priv, base) == bob_pub

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(x25519_base(BOB_PRIV)).to_equal(BOB_PUB)
```

</details>

#### Alice computes shared secret: x25519(alice_priv, bob_pub) == shared_secret

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(x25519(ALICE_PRIV, BOB_PUB)).to_equal(SHARED_SECRET)
```

</details>

#### Bob computes shared secret: x25519(bob_priv, alice_pub) == shared_secret

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(x25519(BOB_PRIV, ALICE_PUB)).to_equal(SHARED_SECRET)
```

</details>

### Curve25519 RV64 live bootstrap regression

#### small-limb shallow probes preserve bootstrap byte and base-point inputs

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(x25519_smalllimb_clamp_probe(LIVE_BOOTSTRAP_PRIV)).to_equal(LIVE_BOOTSTRAP_PRIV)
expect(x25519_smalllimb_base_point_probe()).to_equal(BASE_POINT)
expect(x25519_smalllimb_mask_probe(BASE_POINT)).to_equal(BASE_POINT)
expect(x25519_smalllimb_roundtrip_probe(BASE_POINT)).to_equal(BASE_POINT)
```

</details>

#### small-limb public API matches the live C helper bootstrap public key

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(x25519_base(LIVE_BOOTSTRAP_PRIV)).to_equal(LIVE_BOOTSTRAP_PUB)
```

</details>

#### BigInt probe matches the live C helper bootstrap public key

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(x25519_base_bigint_probe(LIVE_BOOTSTRAP_PRIV)).to_equal(LIVE_BOOTSTRAP_PUB)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/crypto/curve25519_rfc7748_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Curve25519 RFC 7748 §5.2 single scalar-mult test vectors
- Curve25519 RFC 7748 §5.2 iterated scalar-mult
- Curve25519 RFC 7748 §6.1 ECDH key exchange
- Curve25519 RV64 live bootstrap regression

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 10 |
| Active scenarios | 10 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

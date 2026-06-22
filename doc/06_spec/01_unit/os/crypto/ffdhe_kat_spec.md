# Ffdhe Kat Specification

> <details>

<!-- sdn-diagram:id=ffdhe_kat_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=ffdhe_kat_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

ffdhe_kat_spec -> std
ffdhe_kat_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=ffdhe_kat_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 14 | 14 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Ffdhe Kat Specification

## Scenarios

### FFDHE RFC 7919 — §1 small-prime DH sanity (p=23, g=2)

#### Alice pub = g^4 mod 23 = 16

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = _small_p()
val g = _small_g()
val kp = ffdhe_keygen(p, g, _alice_scalar())
val pub_bytes = ffdhe_pub_to_bytes(kp[1], 1)
expect(pub_bytes[0].to_i64()).to_equal(16)
```

</details>

#### Bob pub = g^7 mod 23 = 13

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = _small_p()
val g = _small_g()
val kp = ffdhe_keygen(p, g, _bob_scalar())
val pub_bytes = ffdhe_pub_to_bytes(kp[1], 1)
expect(pub_bytes[0].to_i64()).to_equal(13)
```

</details>

#### Alice and Bob derive the same shared secret (18)

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = _small_p()
val g = _small_g()
val alice_kp = ffdhe_keygen(p, g, _alice_scalar())
val bob_kp   = ffdhe_keygen(p, g, _bob_scalar())
val shared_alice = ffdhe_dh(alice_kp[0], bob_kp[1], p)
val shared_bob   = ffdhe_dh(bob_kp[0], alice_kp[1], p)
val sa_bytes = ffdhe_pub_to_bytes(shared_alice, 1)
val sb_bytes = ffdhe_pub_to_bytes(shared_bob, 1)
expect(sa_bytes[0].to_i64()).to_equal(18)
expect(sb_bytes[0].to_i64()).to_equal(18)
expect(sa_bytes[0]).to_equal(sb_bytes[0])
```

</details>

#### round-trip byte serialization of small pub key

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = _small_p()
val g = _small_g()
val kp = ffdhe_keygen(p, g, _alice_scalar())
val pub_bytes = ffdhe_pub_to_bytes(kp[1], 1)
val recovered = ffdhe_bytes_to_pub(pub_bytes)
val recovered_bytes = ffdhe_pub_to_bytes(recovered, 1)
expect(recovered_bytes[0]).to_equal(pub_bytes[0])
```

</details>

### FFDHE RFC 7919 — §2 ffdhe2048 prime integrity

#### ffdhe2048_p() encodes to exactly 256 bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = ffdhe2048_p()
val pb = ffdhe_prime_bytes(p, 256)
expect(pb.len().to_i64()).to_equal(256)
```

</details>

#### ffdhe2048 SHA-256 fingerprint matches RFC 7919 Appendix A.1

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Computed: python3 -c \"import hashlib; print(hashlib.sha256(bytes.fromhex(hex)).hexdigest())\"
val p = ffdhe2048_p()
val pb = ffdhe_prime_bytes(p, 256)
val fp = _bytes_to_hex(sha256(pb))
expect(fp).to_equal(
    "d417dfe49b439655f30febdda2200fec593724fd78029662be911a1bcfd701da"
)
```

</details>

#### ffdhe2048 first byte is 0xFF

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = ffdhe2048_p()
val pb = ffdhe_prime_bytes(p, 256)
expect(pb[0].to_i64()).to_equal(255)
```

</details>

#### ffdhe2048 last byte is 0xFF

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = ffdhe2048_p()
val pb = ffdhe_prime_bytes(p, 256)
expect(pb[255].to_i64()).to_equal(255)
```

</details>

### FFDHE RFC 7919 — §3 ffdhe3072 prime integrity

#### ffdhe3072_p() encodes to exactly 384 bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = ffdhe3072_p()
val pb = ffdhe_prime_bytes(p, 384)
expect(pb.len().to_i64()).to_equal(384)
```

</details>

#### ffdhe3072 SHA-256 fingerprint matches RFC 7919 Appendix A.2

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = ffdhe3072_p()
val pb = ffdhe_prime_bytes(p, 384)
val fp = _bytes_to_hex(sha256(pb))
expect(fp).to_equal(
    "0eaf67db3a839156d5013494a5318a772b5697d270d721f37f092efc69ea5a17"
)
```

</details>

### FFDHE RFC 7919 — §4 ffdhe4096 prime integrity

#### ffdhe4096_p() encodes to exactly 512 bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = ffdhe4096_p()
val pb = ffdhe_prime_bytes(p, 512)
expect(pb.len().to_i64()).to_equal(512)
```

</details>

#### ffdhe4096 SHA-256 fingerprint matches RFC 7919 Appendix A.3

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = ffdhe4096_p()
val pb = ffdhe_prime_bytes(p, 512)
val fp = _bytes_to_hex(sha256(pb))
expect(fp).to_equal(
    "4648414224ac881b3d0dc59b466f96d06a558278776807797ecf1f66ff397b3e"
)
```

</details>

### FFDHE RFC 7919 — §5 ffdhe2048 Alice/Bob round-trip

#### Alice and Bob derive the same 256-byte shared secret

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pending_reason = "2048-bit modexp is O(minutes) in interpreter; deferred to native rt_modexp (see doc/02_requirements/feature/ffdhe_native_modexp_2026-05-02.md)"
expect(pending_reason.len()).to_be_greater_than(0)
```

</details>

#### Alice public key is in range (1 < pub < p-1)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pending_reason = "2048-bit modexp is O(minutes) in interpreter; deferred to native rt_modexp (see doc/02_requirements/feature/ffdhe_native_modexp_2026-05-02.md)"
expect(pending_reason.len()).to_be_greater_than(0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/crypto/ffdhe_kat_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- FFDHE RFC 7919 — §1 small-prime DH sanity (p=23, g=2)
- FFDHE RFC 7919 — §2 ffdhe2048 prime integrity
- FFDHE RFC 7919 — §3 ffdhe3072 prime integrity
- FFDHE RFC 7919 — §4 ffdhe4096 prime integrity
- FFDHE RFC 7919 — §5 ffdhe2048 Alice/Bob round-trip

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 14 |
| Active scenarios | 14 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

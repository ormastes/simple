# Ed448 Rfc8032 Kat Specification

> <details>

<!-- sdn-diagram:id=ed448_rfc8032_kat_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=ed448_rfc8032_kat_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

ed448_rfc8032_kat_spec -> std
ed448_rfc8032_kat_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=ed448_rfc8032_kat_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Ed448 Rfc8032 Kat Specification

## Scenarios

### Ed448 RFC 8032 §7.4 test vectors

#### T1: derived public key matches RFC 8032 §7.4 Blank vector

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val kp = ed448_keygen(SEED_T1)
expect(kp.1).to_equal(PUB_T1)
```

</details>

#### T1: sign(empty) byte-matches RFC 8032 §7.4 expected signature

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val kp = ed448_keygen(SEED_T1)
val sig = ed448_sign(kp.0, kp.1, [], [])
expect(sig).to_equal(SIG_T1)
```

</details>

#### T1: signature verifies under the correct public key

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(ed448_verify(PUB_T1, [], SIG_T1, [])).to_equal(true)
```

</details>

#### T1: signature is rejected when the S half is bit-flipped

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Flip a bit inside S (offset 57 = first byte of S half) — more
# sensitive than R-flips, which can collide with a different valid R.
val bad_sig = _flip_byte(SIG_T1, 57)
expect(ed448_verify(PUB_T1, [], bad_sig, [])).to_equal(false)
```

</details>

#### T2: derived public key matches RFC 8032 §7.4 1-octet vector

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val kp = ed448_keygen(SEED_T2)
expect(kp.1).to_equal(PUB_T2)
```

</details>

#### T2: sign(0x03) byte-matches RFC 8032 §7.4 expected signature

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val kp = ed448_keygen(SEED_T2)
val sig = ed448_sign(kp.0, kp.1, MSG_T2, [])
expect(sig).to_equal(SIG_T2)
```

</details>

#### T2: signature verifies under the correct public key

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(ed448_verify(PUB_T2, MSG_T2, SIG_T2, [])).to_equal(true)
```

</details>

#### T2: signature is rejected under a different public key

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(ed448_verify(PUB_T1, MSG_T2, SIG_T2, [])).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/crypto/ed448_rfc8032_kat_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Ed448 RFC 8032 §7.4 test vectors

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

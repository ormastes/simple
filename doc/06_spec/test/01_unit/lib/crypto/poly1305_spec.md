# Poly1305 Specification

> <details>

<!-- sdn-diagram:id=poly1305_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=poly1305_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

poly1305_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=poly1305_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Poly1305 Specification

## Scenarios

### Poly1305 RFC 8439 §2.5.2 — canonical test vector

#### MAC of 'Cryptographic Forum Research Group' matches RFC 8439 §2.5.2

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tag = poly1305_mac(_key_252(), _msg_252())
expect(_bytes_eq(tag, _expected_tag_252())).to_equal(true)
```

</details>

#### tag is exactly 16 bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tag = poly1305_mac(_key_252(), _msg_252())
expect(tag.len()).to_equal(16u64)
```

</details>

### Poly1305 RFC 8439 §2.6.2 — key generation via ChaCha20

#### poly1305_key_gen produces the RFC 8439 §2.6.2 expected one-time key

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val otk = poly1305_key_gen(_key_gen_key(), _key_gen_nonce())
expect(_bytes_eq(otk, _key_gen_expected_otk())).to_equal(true)
```

</details>

#### poly1305_key_gen always returns exactly 32 bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val otk = poly1305_key_gen(_key_gen_key(), _key_gen_nonce())
expect(otk.len()).to_equal(32u64)
```

</details>

### Poly1305 RFC 8439 §A.3 — additional test vectors

#### Test #1: zero key + 64-byte zero message → zero tag

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tag = poly1305_mac(_key_a3_1(), _msg_a3_1())
expect(_bytes_eq(tag, _expected_tag_a3_1())).to_equal(true)
```

</details>

#### Test #2: r=0, s=36e5..., tag equals s regardless of message

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tag = poly1305_mac(_key_a3_2(), _msg_a3_2())
expect(_bytes_eq(tag, _expected_tag_a3_2())).to_equal(true)
```

</details>

#### Test #4: Jabberwocky 127 bytes (partial last block) → 4541669a...

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tag = poly1305_mac(_key_a3_4(), _msg_a3_4())
expect(_bytes_eq(tag, _expected_tag_a3_4())).to_equal(true)
```

</details>

### Poly1305 edge cases

#### zero-length message → tag is 16 bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val empty: [u8] = []
val tag = poly1305_mac(_key_252(), empty)
expect(tag.len()).to_equal(16u64)
```

</details>

#### zero-length message with zero key → zero tag

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val empty: [u8] = []
val tag = poly1305_mac(_key_a3_1(), empty)
expect(_bytes_eq(tag, _expected_tag_a3_1())).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/crypto/poly1305_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Poly1305 RFC 8439 §2.5.2 — canonical test vector
- Poly1305 RFC 8439 §2.6.2 — key generation via ChaCha20
- Poly1305 RFC 8439 §A.3 — additional test vectors
- Poly1305 edge cases

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

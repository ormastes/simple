# Nacl Specification

> <details>

<!-- sdn-diagram:id=nacl_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=nacl_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

nacl_spec -> std
nacl_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=nacl_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 23 | 23 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Nacl Specification

## Scenarios

### crypto_secretbox — output length

#### secretbox output is 16 + len(msg) bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val msg = _hello_msg()
val boxed = crypto_secretbox(msg, _nacl_nonce(), _nacl_key())
expect(boxed.len()).to_equal(21)
```

</details>

#### secretbox of empty message is exactly 16 bytes (tag only)

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val empty: [u8] = []
val boxed = crypto_secretbox(empty, _nacl_nonce(), _nacl_key())
expect(boxed.len()).to_equal(16)
```

</details>

#### secretbox output is not all zeros (non-trivial)

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val msg = _hello_msg()
val boxed = crypto_secretbox(msg, _nacl_nonce(), _nacl_key())
var all_zero = true
var i: u64 = 0
while i < boxed.len():
    if boxed[i] != 0u8:
        all_zero = false
    i = i + 1
expect(all_zero).to_equal(false)
```

</details>

### crypto_secretbox round-trip

#### secretbox then secretbox_open recovers original message

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val msg = _hello_msg()
val boxed = crypto_secretbox(msg, _nacl_nonce(), _nacl_key())
val recovered = crypto_secretbox_open(boxed, _nacl_nonce(), _nacl_key())
expect(_bytes_hex(recovered)).to_equal(_bytes_hex(msg))
```

</details>

#### round-trip with empty message

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val empty: [u8] = []
val boxed = crypto_secretbox(empty, _nacl_nonce(), _nacl_key())
val recovered = crypto_secretbox_open(boxed, _nacl_nonce(), _nacl_key())
expect(recovered.len()).to_equal(0)
```

</details>

#### round-trip with alt key and nonce

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val msg = _hello_msg()
val boxed = crypto_secretbox(msg, _alt_nonce(), _alt_key())
val recovered = crypto_secretbox_open(boxed, _alt_nonce(), _alt_key())
expect(_bytes_hex(recovered)).to_equal(_bytes_hex(msg))
```

</details>

#### different keys produce different ciphertexts

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val msg = _hello_msg()
val boxed1 = crypto_secretbox(msg, _nacl_nonce(), _nacl_key())
val boxed2 = crypto_secretbox(msg, _nacl_nonce(), _alt_key())
var same = true
var i: u64 = 0
while i < boxed1.len():
    if boxed1[i] != boxed2[i]:
        same = false
    i = i + 1
expect(same).to_equal(false)
```

</details>

### crypto_secretbox_open — auth failure

#### modified tag byte returns empty

1. tampered push
2. tampered push
   - Expected: result.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val msg = _hello_msg()
val boxed = crypto_secretbox(msg, _nacl_nonce(), _nacl_key())
# Flip first byte of tag
var tampered: [u8] = []
tampered.push(boxed[0] ^ 0x01u8)
var i: u64 = 1
while i < boxed.len():
    tampered.push(boxed[i])
    i = i + 1
val result = crypto_secretbox_open(tampered, _nacl_nonce(), _nacl_key())
expect(result.len()).to_equal(0)
```

</details>

#### modified ciphertext body returns empty

1. tampered push
2. tampered push
   - Expected: result.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val msg = _hello_msg()
val boxed = crypto_secretbox(msg, _nacl_nonce(), _nacl_key())
# Flip a byte in the ciphertext body (after the 16-byte tag)
var tampered: [u8] = []
var i: u64 = 0
while i < boxed.len():
    if i == 16:
        tampered.push(boxed[i] ^ 0xffu8)
    else:
        tampered.push(boxed[i])
    i = i + 1
val result = crypto_secretbox_open(tampered, _nacl_nonce(), _nacl_key())
expect(result.len()).to_equal(0)
```

</details>

#### wrong key returns empty

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val msg = _hello_msg()
val boxed = crypto_secretbox(msg, _nacl_nonce(), _nacl_key())
val result = crypto_secretbox_open(boxed, _nacl_nonce(), _alt_key())
expect(result.len()).to_equal(0)
```

</details>

#### wrong nonce returns empty

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val msg = _hello_msg()
val boxed = crypto_secretbox(msg, _nacl_nonce(), _nacl_key())
val result = crypto_secretbox_open(boxed, _alt_nonce(), _nacl_key())
expect(result.len()).to_equal(0)
```

</details>

#### too-short ciphertext returns empty

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val short: [u8] = _zeros(10)
val result = crypto_secretbox_open(short, _nacl_nonce(), _nacl_key())
expect(result.len()).to_equal(0)
```

</details>

### crypto_box_keypair

#### returns a list of two 32-byte arrays

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sk = _kp1_sk()
val pk = _kp1_pk()
val sk_len = sk.len()
val pk_len = pk.len()
expect(sk_len).to_equal(32)
expect(pk_len).to_equal(32)
```

</details>

#### secret key matches the seed

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val seed = _seed32()
val sk = _kp1_sk()
expect(_bytes_hex(sk)).to_equal(_bytes_hex(seed))
```

</details>

#### public key is non-zero

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pk = _kp1_pk()
var all_zero = true
var i: u64 = 0
while i < 32:
    if pk[i] != 0u8:
        all_zero = false
    i = i + 1
expect(all_zero).to_equal(false)
```

</details>

#### different seeds produce different public keys

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pk1 = _kp1_pk()
val pk2 = _kp2_pk()
var same = true
var i: u64 = 0
while i < 32:
    if pk1[i] != pk2[i]:
        same = false
    i = i + 1
expect(same).to_equal(false)
```

</details>

### crypto_box_beforenm

#### shared key is 32 bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sk1 = _kp1_sk()
val pk2 = _kp2_pk()
val shared_key = crypto_box_beforenm(sk1, pk2)
val shared_key_len = shared_key.len()
expect(shared_key_len).to_equal(32)
```

</details>

#### shared key is non-zero

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sk1 = _kp1_sk()
val pk2 = _kp2_pk()
val shared_key = crypto_box_beforenm(sk1, pk2)
var all_zero = true
var i: u64 = 0
while i < 32:
    if shared_key[i] != 0u8:
        all_zero = false
    i = i + 1
expect(all_zero).to_equal(false)
```

</details>

#### DH is commutative: beforenm(sk1, pk2) == beforenm(sk2, pk1)

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sk1 = _kp1_sk()
val pk2 = _kp2_pk()
val sk2 = _kp2_sk()
val pk1 = _kp1_pk()
val shared_a = crypto_box_beforenm(sk1, pk2)
val shared_b = crypto_box_beforenm(sk2, pk1)
expect(_bytes_hex(shared_a)).to_equal(_bytes_hex(shared_b))
```

</details>

### crypto_box round-trip

#### crypto_box then crypto_box_open recovers original message

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sk1 = _kp1_sk()
val pk2 = _kp2_pk()
val sk2 = _kp2_sk()
val pk1 = _kp1_pk()
val msg = _hello_msg()
val boxed = crypto_box(msg, _nacl_nonce(), sk1, pk2)
val recovered = crypto_box_open(boxed, _nacl_nonce(), sk2, pk1)
expect(_bytes_hex(recovered)).to_equal(_bytes_hex(msg))
```

</details>

#### crypto_box output length is 16 + len(msg)

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sk1 = _kp1_sk()
val pk2 = _kp2_pk()
val msg = _hello_msg()
val boxed = crypto_box(msg, _nacl_nonce(), sk1, pk2)
val boxed_len = boxed.len()
expect(boxed_len).to_equal(21)
```

</details>

### crypto_box_open — auth failure

#### modified ciphertext returns empty

1. tampered push
2. tampered push
   - Expected: result_len equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sk1 = _kp1_sk()
val pk2 = _kp2_pk()
val sk2 = _kp2_sk()
val pk1 = _kp1_pk()
val msg = _hello_msg()
val boxed = crypto_box(msg, _nacl_nonce(), sk1, pk2)
# Flip a byte in the ciphertext body
var tampered: [u8] = []
var i: u64 = 0
while i < boxed.len():
    if i == 16:
        tampered.push(boxed[i] ^ 0xffu8)
    else:
        tampered.push(boxed[i])
    i = i + 1
val result = crypto_box_open(tampered, _nacl_nonce(), sk2, pk1)
val result_len = result.len()
expect(result_len).to_equal(0)
```

</details>

#### wrong recipient key returns empty

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sk1 = _kp1_sk()
val pk2 = _kp2_pk()
val sk3 = _kp3_sk()
val pk1 = _kp1_pk()
val msg = _hello_msg()
val boxed = crypto_box(msg, _nacl_nonce(), sk1, pk2)
val result = crypto_box_open(boxed, _nacl_nonce(), sk3, pk1)
val result_len = result.len()
expect(result_len).to_equal(0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/crypto/nacl_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- crypto_secretbox — output length
- crypto_secretbox round-trip
- crypto_secretbox_open — auth failure
- crypto_box_keypair
- crypto_box_beforenm
- crypto_box round-trip
- crypto_box_open — auth failure

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 23 |
| Active scenarios | 23 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

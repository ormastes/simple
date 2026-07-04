# Hashes Specification

> <details>

<!-- sdn-diagram:id=hashes_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=hashes_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

hashes_spec -> std
hashes_spec -> lib
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=hashes_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 18 | 18 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Hashes Specification

## Scenarios

### typed hashes — sha256

#### SHA-256 of 'abc' matches FIPS KAT

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# "abc" = [0x61, 0x62, 0x63]
val data: [u8] = [97u8, 98u8, 99u8]
val span = ByteSpan.new(data)
val d = sha256(span)
expect(d.hex()).to_equal("ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad")
```

</details>

#### SHA-256 of empty input matches FIPS KAT

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val data: [u8] = []
val span = ByteSpan.new(data)
val d = sha256(span)
expect(d.hex()).to_equal("e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855")
```

</details>

#### SHA-256 output is 32 bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val data: [u8] = [1u8, 2u8, 3u8]
val d = sha256(ByteSpan.new(data))
expect(d.len()).to_equal(32)
```

</details>

#### SHA-256 ct_eq: same digest is equal

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val data: [u8] = [97u8, 98u8, 99u8]
val d1 = sha256(ByteSpan.new(data))
val d2 = sha256(ByteSpan.new(data))
expect(d1.ct_eq(d2)).to_equal(true)
```

</details>

#### SHA-256 ct_eq: different digest is not equal

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a: [u8] = [97u8, 98u8, 99u8]
val b: [u8] = [97u8, 98u8, 100u8]
val d1 = sha256(ByteSpan.new(a))
val d2 = sha256(ByteSpan.new(b))
expect(d1.ct_eq(d2)).to_equal(false)
```

</details>

### typed hashes — sha512

#### SHA-512 output is 64 bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val data: [u8] = [97u8, 98u8, 99u8]
val d = sha512(ByteSpan.new(data))
expect(d.len()).to_equal(64)
```

</details>

#### SHA-512 of empty is distinct from SHA-256 of empty

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val empty: [u8] = []
val d256 = sha256(ByteSpan.new(empty))
val d512 = sha512(ByteSpan.new(empty))
expect(d256.hex()).to_equal("e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855")
expect(d512.len()).to_equal(64)
# SHA-512("") starts with cf83e1 — first 8 hex chars
val h = d512.hex()
expect(h.starts_with("cf83e1")).to_equal(true)
```

</details>

### typed hashes — sha512_256

#### SHA-512/256 output is 32 bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val data: [u8] = [97u8, 98u8, 99u8]
val d = sha512_256(ByteSpan.new(data))
expect(d.len()).to_equal(32)
```

</details>

#### SHA-512/256 of abc differs from SHA-256 of abc

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val data: [u8] = [97u8, 98u8, 99u8]
val d256 = sha256(ByteSpan.new(data))
val d512_256 = sha512_256(ByteSpan.new(data))
expect(d512_256.ct_eq(d256)).to_equal(false)
```

</details>

### typed hashes — hmac_sha256

#### HMAC-SHA-256 RFC4231 TC2: key=Jefe data=what do ya want for nothing?

<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# key = "Jefe" = [0x4a, 0x65, 0x66, 0x65]
val key: [u8] = [74u8, 101u8, 102u8, 101u8]
# data = "what do ya want for nothing?"
# w=119 h=104 a=97 t=116 ' '=32 d=100 o=111 ' '=32 y=121 a=97 ' '=32
# w=119 a=97 n=110 t=116 ' '=32 f=102 o=111 r=114 ' '=32 n=110
# o=111 t=116 h=104 i=105 n=110 g=103 ?=63
val data: [u8] = [
    119u8, 104u8, 97u8, 116u8, 32u8,
    100u8, 111u8, 32u8, 121u8, 97u8,
    32u8, 119u8, 97u8, 110u8, 116u8,
    32u8, 102u8, 111u8, 114u8, 32u8,
    110u8, 111u8, 116u8, 104u8, 105u8,
    110u8, 103u8, 63u8
]
val tag = hmac_sha256(ByteSpan.new(key), ByteSpan.new(data))
expect(tag.hex()).to_equal("5bdcc146bf60754e6a042426089575c75a003f089d2739839dec58b964ec3843")
```

</details>

#### HMAC-SHA-256 output is 32 bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val key: [u8] = [1u8, 2u8, 3u8]
val msg: [u8] = [4u8, 5u8, 6u8]
val tag = hmac_sha256(ByteSpan.new(key), ByteSpan.new(msg))
expect(tag.len()).to_equal(32)
```

</details>

#### HMAC-SHA-256 ct_eq: same tag

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val key: [u8] = [74u8, 101u8, 102u8, 101u8]
val msg: [u8] = [97u8, 98u8, 99u8]
val t1 = hmac_sha256(ByteSpan.new(key), ByteSpan.new(msg))
val t2 = hmac_sha256(ByteSpan.new(key), ByteSpan.new(msg))
expect(t1.ct_eq(t2)).to_equal(true)
```

</details>

#### HMAC-SHA-256 ct_eq: different key yields different tag

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val key1: [u8] = [74u8, 101u8, 102u8, 101u8]
val key2: [u8] = [74u8, 101u8, 102u8, 102u8]
val msg: [u8] = [97u8, 98u8, 99u8]
val t1 = hmac_sha256(ByteSpan.new(key1), ByteSpan.new(msg))
val t2 = hmac_sha256(ByteSpan.new(key2), ByteSpan.new(msg))
expect(t1.ct_eq(t2)).to_equal(false)
```

</details>

### typed hashes — hmac_sha512

#### HMAC-SHA-512 output is 64 bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val key: [u8] = [74u8, 101u8, 102u8, 101u8]
val msg: [u8] = [97u8, 98u8, 99u8]
val tag = hmac_sha512(ByteSpan.new(key), ByteSpan.new(msg))
expect(tag.len()).to_equal(64)
```

</details>

#### HMAC-SHA-512 differs from HMAC-SHA-256 for same inputs

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val key: [u8] = [74u8, 101u8, 102u8, 101u8]
val msg: [u8] = [97u8, 98u8, 99u8]
val t256 = hmac_sha256(ByteSpan.new(key), ByteSpan.new(msg))
val t512 = hmac_sha512(ByteSpan.new(key), ByteSpan.new(msg))
# Different lengths means they cannot be ct_eq (same type check, but lens differ)
expect(t512.len()).to_equal(64)
expect(t256.len()).to_equal(32)
```

</details>

### typed hashes — hkdf_sha256

#### HKDF-SHA-256 RFC5869 A.1: L=42 OKM matches oracle

- ikm push
   - Expected: okm.hex() equals `3cb25f25faacd57a90434f64d0362f2a2d2d0a90cf1a5a4c5db02d56ecc4c5bf34007208d5b88... (full value in folded executable source)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# RFC5869 A.1: IKM=0x0b * 22, salt=0x000102...0x0c (13 bytes), info=0xf0f1...0xf9 (10 bytes)
var ikm: [u8] = []
var i = 0
while i < 22:
    ikm.push(11u8)
    i = i + 1
# salt = [0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08, 0x09, 0x0a, 0x0b, 0x0c]
val salt: [u8] = [0u8, 1u8, 2u8, 3u8, 4u8, 5u8, 6u8, 7u8, 8u8, 9u8, 10u8, 11u8, 12u8]
# info = [0xf0, 0xf1, 0xf2, 0xf3, 0xf4, 0xf5, 0xf6, 0xf7, 0xf8, 0xf9]
val info: [u8] = [240u8, 241u8, 242u8, 243u8, 244u8, 245u8, 246u8, 247u8, 248u8, 249u8]
val okm = hkdf_sha256(ByteSpan.new(salt), ByteSpan.new(ikm), ByteSpan.new(info), 42)
expect(okm.hex()).to_equal("3cb25f25faacd57a90434f64d0362f2a2d2d0a90cf1a5a4c5db02d56ecc4c5bf34007208d5b887185865")
```

</details>

#### HKDF-SHA-256 output length matches requested

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ikm: [u8] = [1u8, 2u8, 3u8]
val salt: [u8] = [0u8]
val info: [u8] = []
val okm = hkdf_sha256(ByteSpan.new(salt), ByteSpan.new(ikm), ByteSpan.new(info), 32)
expect(okm.len()).to_equal(32)
```

</details>

#### HKDF-SHA-256 different IKM yields different OKM

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ikm1: [u8] = [1u8, 2u8, 3u8]
val ikm2: [u8] = [1u8, 2u8, 4u8]
val salt: [u8] = [0u8]
val info: [u8] = []
val o1 = hkdf_sha256(ByteSpan.new(salt), ByteSpan.new(ikm1), ByteSpan.new(info), 32)
val o2 = hkdf_sha256(ByteSpan.new(salt), ByteSpan.new(ikm2), ByteSpan.new(info), 32)
expect(o1.ct_eq(o2)).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/crypto/typed/hashes_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- typed hashes — sha256
- typed hashes — sha512
- typed hashes — sha512_256
- typed hashes — hmac_sha256
- typed hashes — hmac_sha512
- typed hashes — hkdf_sha256

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 18 |
| Active scenarios | 18 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

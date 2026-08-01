# Ctypes Specification

> <details>

<!-- sdn-diagram:id=ctypes_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=ctypes_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

ctypes_spec -> std
ctypes_spec -> lib
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=ctypes_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 31 | 31 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Ctypes Specification

## Scenarios

### Digest

#### hex() returns deadbeef for [0xde,0xad,0xbe,0xef]

- var d = Digest new
   - Expected: d.hex() equals `deadbeef`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var data: [u8] = [0xdeu8, 0xadu8, 0xbeu8, 0xefu8]
var d = Digest.new(data)
expect(d.hex()).to_equal("deadbeef")
```

</details>

#### len() == 4

- var d = Digest new
   - Expected: d.len() equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var data: [u8] = [0xdeu8, 0xadu8, 0xbeu8, 0xefu8]
var d = Digest.new(data)
expect(d.len()).to_equal(4)
```

</details>

#### bytes() round-trips back to the original span

- var d = Digest new
- var span = d bytes
   - Expected: span.get(0).to_i64() equals `0xde`
   - Expected: span.get(3).to_i64() equals `0xef`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var data: [u8] = [0xdeu8, 0xadu8, 0xbeu8, 0xefu8]
var d = Digest.new(data)
var span = d.bytes()
expect(span.get(0).to_i64()).to_equal(0xde)
expect(span.get(3).to_i64()).to_equal(0xef)
```

</details>

#### ct_eq is true for identical byte contents

- var da = Digest new
- var db = Digest new
   - Expected: da.ct_eq(db) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var a: [u8] = [0xdeu8, 0xadu8, 0xbeu8, 0xefu8]
var b: [u8] = [0xdeu8, 0xadu8, 0xbeu8, 0xefu8]
var da = Digest.new(a)
var db = Digest.new(b)
expect(da.ct_eq(db)).to_equal(true)
```

</details>

#### ct_eq is false for differing bytes

- var da = Digest new
- var db = Digest new
   - Expected: da.ct_eq(db) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var a: [u8] = [0xdeu8, 0xadu8, 0xbeu8, 0xefu8]
var b: [u8] = [0xdeu8, 0xadu8, 0xbeu8, 0x00u8]
var da = Digest.new(a)
var db = Digest.new(b)
expect(da.ct_eq(db)).to_equal(false)
```

</details>

#### ct_eq is false for different lengths

- var da = Digest new
- var db = Digest new
   - Expected: da.ct_eq(db) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var a: [u8] = [0xdeu8, 0xadu8]
var b: [u8] = [0xdeu8, 0xadu8, 0xbeu8, 0xefu8]
var da = Digest.new(a)
var db = Digest.new(b)
expect(da.ct_eq(db)).to_equal(false)
```

</details>

#### from_hex round-trips through hex()

- var d = Digest from hex
   - Expected: d.hex() equals `deadbeef`
   - Expected: d.len() equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var d = Digest.from_hex("deadbeef")
expect(d.hex()).to_equal("deadbeef")
expect(d.len()).to_equal(4)
```

</details>

#### from_span wraps a ByteSpan

- var span = ByteSpan new
- var d = Digest from span
   - Expected: d.len() equals `2`
   - Expected: d.hex() equals `0102`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var data: [u8] = [0x01u8, 0x02u8]
var span = ByteSpan.new(data)
var d = Digest.from_span(span)
expect(d.len()).to_equal(2)
expect(d.hex()).to_equal("0102")
```

</details>

### MacTag

#### hex() and ct_eq work on [0xca,0xfe]

- var ma = MacTag new
- var mb = MacTag new
   - Expected: ma.hex() equals `cafe`
   - Expected: ma.ct_eq(mb) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var a: [u8] = [0xcau8, 0xfeu8]
var b: [u8] = [0xcau8, 0xfeu8]
var ma = MacTag.new(a)
var mb = MacTag.new(b)
expect(ma.hex()).to_equal("cafe")
expect(ma.ct_eq(mb)).to_equal(true)
```

</details>

#### ct_eq is false for differing MacTag

- var ma = MacTag new
- var mb = MacTag new
   - Expected: ma.ct_eq(mb) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var a: [u8] = [0xcau8, 0xfeu8]
var b: [u8] = [0xcau8, 0xffu8]
var ma = MacTag.new(a)
var mb = MacTag.new(b)
expect(ma.ct_eq(mb)).to_equal(false)
```

</details>

#### from_hex produces correct hex

- var m = MacTag from hex
   - Expected: m.hex() equals `cafe`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var m = MacTag.from_hex("cafe")
expect(m.hex()).to_equal("cafe")
```

</details>

### Nonce

#### hex() returns correct lowercase hex

- var n = Nonce new
   - Expected: n.hex() equals `deadbeef`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var data: [u8] = [0xdeu8, 0xadu8, 0xbeu8, 0xefu8]
var n = Nonce.new(data)
expect(n.hex()).to_equal("deadbeef")
```

</details>

#### len() is correct

- var n = Nonce new
   - Expected: n.len() equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var data: [u8] = [0x00u8, 0x01u8, 0x02u8]
var n = Nonce.new(data)
expect(n.len()).to_equal(3)
```

</details>

#### bytes() round-trips

- var n = Nonce new
- var sp = n bytes
   - Expected: sp.get(0).to_i64() equals `255`
   - Expected: sp.get(1).to_i64() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var data: [u8] = [0xffu8, 0x00u8]
var n = Nonce.new(data)
var sp = n.bytes()
expect(sp.get(0).to_i64()).to_equal(255)
expect(sp.get(1).to_i64()).to_equal(0)
```

</details>

### AuthTag

#### ct_eq true for same bytes

- var ta = AuthTag new
- var tb = AuthTag new
   - Expected: ta.ct_eq(tb) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var a: [u8] = [0x11u8, 0x22u8, 0x33u8]
var b: [u8] = [0x11u8, 0x22u8, 0x33u8]
var ta = AuthTag.new(a)
var tb = AuthTag.new(b)
expect(ta.ct_eq(tb)).to_equal(true)
```

</details>

#### ct_eq false for different bytes

- var ta = AuthTag new
- var tb = AuthTag new
   - Expected: ta.ct_eq(tb) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var a: [u8] = [0x11u8, 0x22u8, 0x33u8]
var b: [u8] = [0x11u8, 0x22u8, 0x44u8]
var ta = AuthTag.new(a)
var tb = AuthTag.new(b)
expect(ta.ct_eq(tb)).to_equal(false)
```

</details>

#### hex() for [0xde,0xad,0xbe,0xef]

- var t = AuthTag new
   - Expected: t.hex() equals `deadbeef`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var data: [u8] = [0xdeu8, 0xadu8, 0xbeu8, 0xefu8]
var t = AuthTag.new(data)
expect(t.hex()).to_equal("deadbeef")
```

</details>

### Plaintext

#### hex() and len() work correctly

- var p = Plaintext new
   - Expected: p.hex() equals `deadbeef`
   - Expected: p.len() equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var data: [u8] = [0xdeu8, 0xadu8, 0xbeu8, 0xefu8]
var p = Plaintext.new(data)
expect(p.hex()).to_equal("deadbeef")
expect(p.len()).to_equal(4)
```

</details>

#### bytes() returns accessible span

- var p = Plaintext new
   - Expected: p.bytes().get(0).to_i64() equals `0x42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var data: [u8] = [0x42u8]
var p = Plaintext.new(data)
expect(p.bytes().get(0).to_i64()).to_equal(0x42)
```

</details>

### Ciphertext

#### hex() and len() work correctly

- var c = Ciphertext new
   - Expected: c.hex() equals `deadbeef`
   - Expected: c.len() equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var data: [u8] = [0xdeu8, 0xadu8, 0xbeu8, 0xefu8]
var c = Ciphertext.new(data)
expect(c.hex()).to_equal("deadbeef")
expect(c.len()).to_equal(4)
```

</details>

#### from_hex produces correct span

- var c = Ciphertext from hex
   - Expected: c.len() equals `4`
   - Expected: c.bytes().get(0).to_i64() equals `0xde`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var c = Ciphertext.from_hex("deadbeef")
expect(c.len()).to_equal(4)
expect(c.bytes().get(0).to_i64()).to_equal(0xde)
```

</details>

### SecretKey

#### ct_eq true for equal keys

- var ka = SecretKey new
- var kb = SecretKey new
   - Expected: ka.ct_eq(kb) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var a: [u8] = [0xdeu8, 0xadu8, 0xbeu8, 0xefu8]
var b: [u8] = [0xdeu8, 0xadu8, 0xbeu8, 0xefu8]
var ka = SecretKey.new(a)
var kb = SecretKey.new(b)
expect(ka.ct_eq(kb)).to_equal(true)
```

</details>

#### ct_eq false for different keys

- var ka = SecretKey new
- var kb = SecretKey new
   - Expected: ka.ct_eq(kb) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var a: [u8] = [0xdeu8, 0xadu8, 0xbeu8, 0xefu8]
var b: [u8] = [0xdeu8, 0xadu8, 0xbeu8, 0x00u8]
var ka = SecretKey.new(a)
var kb = SecretKey.new(b)
expect(ka.ct_eq(kb)).to_equal(false)
```

</details>

#### hex() correct

- var k = SecretKey new
   - Expected: k.hex() equals `deadbeef`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var data: [u8] = [0xdeu8, 0xadu8, 0xbeu8, 0xefu8]
var k = SecretKey.new(data)
expect(k.hex()).to_equal("deadbeef")
```

</details>

### PublicKey

#### hex() and len() correct

- var k = PublicKey new
   - Expected: k.hex() equals `deadbeef`
   - Expected: k.len() equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var data: [u8] = [0xdeu8, 0xadu8, 0xbeu8, 0xefu8]
var k = PublicKey.new(data)
expect(k.hex()).to_equal("deadbeef")
expect(k.len()).to_equal(4)
```

</details>

#### bytes() round-trips

- var k = PublicKey new
   - Expected: k.bytes().get(1).to_i64() equals `0x0b`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var data: [u8] = [0x0au8, 0x0bu8]
var k = PublicKey.new(data)
expect(k.bytes().get(1).to_i64()).to_equal(0x0b)
```

</details>

### Signature

#### hex() for [0xde,0xad,0xbe,0xef]

- var s = Signature new
   - Expected: s.hex() equals `deadbeef`
   - Expected: s.len() equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var data: [u8] = [0xdeu8, 0xadu8, 0xbeu8, 0xefu8]
var s = Signature.new(data)
expect(s.hex()).to_equal("deadbeef")
expect(s.len()).to_equal(4)
```

</details>

#### from_span produces correct signature

- var sp = ByteSpan new
- var s = Signature from span
   - Expected: s.len() equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var data: [u8] = [0x01u8, 0x02u8, 0x03u8]
var sp = ByteSpan.new(data)
var s = Signature.from_span(sp)
expect(s.len()).to_equal(3)
```

</details>

### SharedSecret

#### ct_eq true for equal secrets

- var sa = SharedSecret new
- var sb = SharedSecret new
   - Expected: sa.ct_eq(sb) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var a: [u8] = [0xdeu8, 0xadu8, 0xbeu8, 0xefu8]
var b: [u8] = [0xdeu8, 0xadu8, 0xbeu8, 0xefu8]
var sa = SharedSecret.new(a)
var sb = SharedSecret.new(b)
expect(sa.ct_eq(sb)).to_equal(true)
```

</details>

#### ct_eq false for different secrets

- var sa = SharedSecret new
- var sb = SharedSecret new
   - Expected: sa.ct_eq(sb) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var a: [u8] = [0xdeu8, 0xadu8, 0xbeu8, 0xefu8]
var b: [u8] = [0xffu8, 0xadu8, 0xbeu8, 0xefu8]
var sa = SharedSecret.new(a)
var sb = SharedSecret.new(b)
expect(sa.ct_eq(sb)).to_equal(false)
```

</details>

#### hex() for [0xde,0xad,0xbe,0xef]

- var s = SharedSecret new
   - Expected: s.hex() equals `deadbeef`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var data: [u8] = [0xdeu8, 0xadu8, 0xbeu8, 0xefu8]
var s = SharedSecret.new(data)
expect(s.hex()).to_equal("deadbeef")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/crypto/typed/ctypes_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Digest
- MacTag
- Nonce
- AuthTag
- Plaintext
- Ciphertext
- SecretKey
- PublicKey
- Signature
- SharedSecret

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 31 |
| Active scenarios | 31 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

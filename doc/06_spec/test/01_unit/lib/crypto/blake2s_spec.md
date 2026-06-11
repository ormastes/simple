# Blake2s Specification

> <details>

<!-- sdn-diagram:id=blake2s_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=blake2s_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

blake2s_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=blake2s_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Blake2s Specification

## Scenarios

### BLAKE2s RFC 7693 unkeyed test vectors

#### empty input unkeyed 32-byte digest

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# RFC 7693: BLAKE2s("") =
#   69217a3079908094e11121d042354a7c1f55b6482ca1a51e1b250dfd1ed0eef9
val digest = blake2s_hash(_empty_bytes(), 32u32, _empty_bytes())
expect(_bytes_to_hex(digest)).to_equal("69217a3079908094e11121d042354a7c1f55b6482ca1a51e1b250dfd1ed0eef9")
```

</details>

#### Appendix B 'abc' unkeyed 32-byte digest (RFC 7693 §B)

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# RFC 7693 Appendix B:
#   508c5e8c327c14e2e1a72ba34eeb452f37458b209ed63a294d999b4c86675982
val digest = blake2s_hash(_empty_bytes(), 32u32, _abc_bytes())
expect(_bytes_to_hex(digest)).to_equal("508c5e8c327c14e2e1a72ba34eeb452f37458b209ed63a294d999b4c86675982")
```

</details>

#### 64-byte input (one full block boundary) 32-byte digest

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Python: hashlib.blake2s(b'a'*64).hexdigest()
#   651d2f5f20952eacaea2fba2f2af2bcd633e511ea2d2e4c9ae2ac0d9ffb7b252
val msg = _repeat_bytes(0x61u8, 64)
val digest = blake2s_hash(_empty_bytes(), 32u32, msg)
expect(_bytes_to_hex(digest)).to_equal("651d2f5f20952eacaea2fba2f2af2bcd633e511ea2d2e4c9ae2ac0d9ffb7b252")
```

</details>

#### 65-byte input (one full block + 1 residual byte) 32-byte digest

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Python: hashlib.blake2s(b'a'*65).hexdigest()
#   b4ee6ca1ad2ff2a4a8b45b51e01a7a3e5a77a55aae54e9fd0baad0f20c6bb2db
val msg = _repeat_bytes(0x61u8, 65)
val digest = blake2s_hash(_empty_bytes(), 32u32, msg)
expect(_bytes_to_hex(digest)).to_equal("b4ee6ca1ad2ff2a4a8b45b51e01a7a3e5a77a55aae54e9fd0baad0f20c6bb2db")
```

</details>

#### variable output length: 16-byte digest of 'abc'

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Python: hashlib.blake2s(b'abc', digest_size=16).hexdigest()
#   aa4938119b1dc7b87cbad0ffd200d0ae
val digest = blake2s_hash(_empty_bytes(), 16u32, _abc_bytes())
expect(_bytes_to_hex(digest)).to_equal("aa4938119b1dc7b87cbad0ffd200d0ae")
```

</details>

### BLAKE2s keyed-mode test vectors (blake2-kat.json)

#### BLAKE2s key=00..1f in='' out=32 (blake2-kat.json kk=32 in='')

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Python: hashlib.blake2s(b'', key=bytes(range(32))).hexdigest()
#   48a8997da407876b3d79c0d92325ad3b89cbb754d86ab71aee047ad345fd2c49
val key = _range_bytes(32)
val digest = blake2s_hash(key, 32u32, _empty_bytes())
expect(_bytes_to_hex(digest)).to_equal("48a8997da407876b3d79c0d92325ad3b89cbb754d86ab71aee047ad345fd2c49")
```

</details>

#### BLAKE2s key=00..07 in='Hi There' out=32

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Python: hashlib.blake2s(b'Hi There', key=bytes(range(8))).hexdigest()
#   fff44698fee4d219540d95f0f56d41888f344bf0924cef3f6d6a036a4c2aa747
val key = _range_bytes(8)
val digest = blake2s_hash(key, 32u32, _hi_there_bytes())
expect(_bytes_to_hex(digest)).to_equal("fff44698fee4d219540d95f0f56d41888f344bf0924cef3f6d6a036a4c2aa747")
```

</details>

### BLAKE2s streaming update API

#### streaming 3-chunk update matches single-call hash for 'abc'

1. var st = blake2s init
2. chunk a push
3. st = blake2s update
4. chunk b push
5. st = blake2s update
6. chunk c push
7. st = blake2s update
   - Expected: _bytes_to_hex(digest) equals `508c5e8c327c14e2e1a72ba34eeb452f37458b209ed63a294d999b4c86675982`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Feed "a", "b", "c" separately; must equal blake2s_hash([], 32, "abc")
var st = blake2s_init(_empty_bytes(), 32u32)
var chunk_a: [u8] = []
chunk_a.push(0x61u8)
st = blake2s_update(st, chunk_a)
var chunk_b: [u8] = []
chunk_b.push(0x62u8)
st = blake2s_update(st, chunk_b)
var chunk_c: [u8] = []
chunk_c.push(0x63u8)
st = blake2s_update(st, chunk_c)
val digest = blake2s_final(st)
expect(_bytes_to_hex(digest)).to_equal("508c5e8c327c14e2e1a72ba34eeb452f37458b209ed63a294d999b4c86675982")
```

</details>

#### streaming 65-byte message in 1+64 chunks matches single-call hash

1. var st = blake2s init
2. first chunk push
3. st = blake2s update
4. st = blake2s update
   - Expected: _bytes_to_hex(streaming_digest) equals `_bytes_to_hex(onecall_digest)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Chunk 1: 1 byte 'a', Chunk 2: 64 bytes 'a'
# Exercises the buffer-flush boundary during update.
var st = blake2s_init(_empty_bytes(), 32u32)
var first_chunk: [u8] = []
first_chunk.push(0x61u8)
st = blake2s_update(st, first_chunk)
val rest = _repeat_bytes(0x61u8, 64)
st = blake2s_update(st, rest)
val streaming_digest = blake2s_final(st)
val onecall_digest = blake2s_hash(_empty_bytes(), 32u32, _repeat_bytes(0x61u8, 65))
expect(_bytes_to_hex(streaming_digest)).to_equal(_bytes_to_hex(onecall_digest))
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/crypto/blake2s_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- BLAKE2s RFC 7693 unkeyed test vectors
- BLAKE2s keyed-mode test vectors (blake2-kat.json)
- BLAKE2s streaming update API

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

# Blake2b Specification

> <details>

<!-- sdn-diagram:id=blake2b_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=blake2b_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

blake2b_spec -> std
blake2b_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=blake2b_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Blake2b Specification

## Scenarios

### BLAKE2b RFC 7693 unkeyed test vectors

#### empty input unkeyed 64-byte digest

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# RFC 7693: BLAKE2b-512("") =
#   786a02f742015903c6c6fd852552d272912f4740e15847618a86e217f71f5419
#   d25e1031afee585313896444934eb04b903a685b1448b755d56f701afe9be2ce
val digest = blake2b(_empty_bytes(), _empty_bytes(), 64)
expect(_bytes_to_hex(digest)).to_equal("786a02f742015903c6c6fd852552d272912f4740e15847618a86e217f71f5419d25e1031afee585313896444934eb04b903a685b1448b755d56f701afe9be2ce")
```

</details>

#### Appendix B 'abc' unkeyed 64-byte digest

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# RFC 7693 Appendix B:
#   ba80a53f981c4d0d6a2797b69f12f6e94c212f14685ac4b74b12bb6fdbffa2d1
#   7d87c5392aab792dc252d5de4533cc9518d38aa8dbf1925ab92386edd4009923
val digest = blake2b(_empty_bytes(), _abc_bytes(), 64)
expect(_bytes_to_hex(digest)).to_equal("ba80a53f981c4d0d6a2797b69f12f6e94c212f14685ac4b74b12bb6fdbffa2d17d87c5392aab792dc252d5de4533cc9518d38aa8dbf1925ab92386edd4009923")
```

</details>

#### 128-byte input (one full block boundary) 64-byte digest

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# BLAKE2b-512(b'a'*128) — verified byte-exact against an independent
# Node `crypto` blake2b512 reference (the prior Python-comment vector
# was a transcription error: 63-hex first line / digits dropped).
val msg = _repeat_bytes(0x61u8, 128)
val digest = blake2b(_empty_bytes(), msg, 64)
expect(_bytes_to_hex(digest)).to_equal("fc6c71f688f43ea7d60817478808f3cac753e61571865c95adbc2d9122c943a76b92c2cb1047ef3fe7bf6e436ec1d0a99a9e5b216780bf7fed9d7ca91d3a8f3b")
```

</details>

#### 129-byte input (block boundary + 1) 64-byte digest

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# BLAKE2b-512(b'a'*129) — verified byte-exact against an independent
# Node `crypto` blake2b512 reference (prior Python-comment vector wrong).
val msg = _repeat_bytes(0x61u8, 129)
val digest = blake2b(_empty_bytes(), msg, 64)
expect(_bytes_to_hex(digest)).to_equal("55e6e0eb418149a8af92fd9ddc99254781b2f522a131b4f4d984404b71a00e1167b8124d5dcddd4c6977b299392335d6edd303da6d344d74bbef2d38101b232b")
```

</details>

#### variable output length: 32-byte digest of 'abc'

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Python: hashlib.blake2b(b'abc', digest_size=32).hexdigest()
#   bddd813c634239723171ef3fee98579b94964e3bb1cb3e427262c8c068d52319
val digest = blake2b(_empty_bytes(), _abc_bytes(), 32)
expect(_bytes_to_hex(digest)).to_equal("bddd813c634239723171ef3fee98579b94964e3bb1cb3e427262c8c068d52319")
```

</details>

### BLAKE2b keyed-mode test vectors (blake2-kat.json)

#### BLAKE2b key=00..3f in='' out=64 (blake2-kat.json kk=64 in='')

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Python: hashlib.blake2b(b'', key=bytes(range(64))).hexdigest()
#   10ebb67700b1868efb4417987acf4690ae9d972fb7a590c2f02871799aaa4786
#   b5e996e8f0f4eb981fc214b005f42d2ff4233499391653df7aefcbc13fc51568
val key = _range_bytes(64)
val digest = blake2b(key, _empty_bytes(), 64)
expect(_bytes_to_hex(digest)).to_equal("10ebb67700b1868efb4417987acf4690ae9d972fb7a590c2f02871799aaa4786b5e996e8f0f4eb981fc214b005f42d2ff4233499391653df7aefcbc13fc51568")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/crypto/blake2b_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- BLAKE2b RFC 7693 unkeyed test vectors
- BLAKE2b keyed-mode test vectors (blake2-kat.json)

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

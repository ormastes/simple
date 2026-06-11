# Blake2 Rfc7693 Kat Specification

> <details>

<!-- sdn-diagram:id=blake2_rfc7693_kat_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=blake2_rfc7693_kat_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

blake2_rfc7693_kat_spec -> std
blake2_rfc7693_kat_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=blake2_rfc7693_kat_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Blake2 Rfc7693 Kat Specification

## Scenarios

### BLAKE2b RFC 7693 Appendix A test vectors

#### Appendix A 'abc' unkeyed digest (64 bytes)

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Expected: ba80a53f981c4d0d6a2797b69f12f6e94c212f14685ac4b74b12bb6fdbffa2d1
#           7d87c5392aab792dc252d5de4533cc9518d38aa8dbf1925ab92386edd4009923
val msg = _abc_bytes()
val key = _empty_bytes()
val digest = blake2b(key, msg, 64)
expect(_bytes_to_hex(digest)).to_equal("ba80a53f981c4d0d6a2797b69f12f6e94c212f14685ac4b74b12bb6fdbffa2d17d87c5392aab792dc252d5de4533cc9518d38aa8dbf1925ab92386edd4009923")
```

</details>

#### multi-block: 128 bytes of 'a' unkeyed (1 full block, 64-byte digest)

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# 128 bytes = exactly one BLAKE2b block; exercises the all-block-is-final path.
# Reference (Python hashlib.blake2b):
#   fc6c71f688f43ea7d60817478808f3cac753e61571865c95adbc2d9122c943a7
#   6b92c2cb1047ef3fe7bf6e436ec1d0a99a9e5b216780bf7fed9d7ca91d3a8f3b
val msg = _repeat_bytes(0x61, 128)
val key = _empty_bytes()
val digest = blake2b(key, msg, 64)
expect(_bytes_to_hex(digest)).to_equal("fc6c71f688f43ea7d60817478808f3cac753e61571865c95adbc2d9122c943a76b92c2cb1047ef3fe7bf6e436ec1d0a99a9e5b216780bf7fed9d7ca91d3a8f3b")
```

</details>

### BLAKE2s RFC 7693 Appendix B test vectors

#### Appendix B 'abc' unkeyed digest (32 bytes)

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Expected: 508c5e8c327c14e2e1a72ba34eeb452f37458b209ed63a294d999b4c86675982
val msg = _abc_bytes()
val key = _empty_bytes()
val digest = blake2s(key, msg, 32)
expect(_bytes_to_hex(digest)).to_equal("508c5e8c327c14e2e1a72ba34eeb452f37458b209ed63a294d999b4c86675982")
```

</details>

#### multi-block: 64 bytes of 'a' unkeyed (1 full block, 32-byte digest)

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Reference (Python hashlib.blake2s):
#   651d2f5f20952eacaea2fba2f2af2bcd633e511ea2d2e4c9ae2ac0d9ffb7b252
val msg = _repeat_bytes(0x61, 64)
val key = _empty_bytes()
val digest = blake2s(key, msg, 32)
expect(_bytes_to_hex(digest)).to_equal("651d2f5f20952eacaea2fba2f2af2bcd633e511ea2d2e4c9ae2ac0d9ffb7b252")
```

</details>

### BLAKE2 keyed-mode KATs (blake2-kat.json)

#### BLAKE2b key=00..3f in='' out=64 (blake2-kat.json kk=64 in='')

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Expected: 10ebb67700b1868efb4417987acf4690ae9d972fb7a590c2f02871799aaa4786
#           b5e996e8f0f4eb981fc214b005f42d2ff4233499391653df7aefcbc13fc51568
val key = _range_bytes(64)
val msg = _empty_bytes()
val digest = blake2b(key, msg, 64)
expect(_bytes_to_hex(digest)).to_equal("10ebb67700b1868efb4417987acf4690ae9d972fb7a590c2f02871799aaa4786b5e996e8f0f4eb981fc214b005f42d2ff4233499391653df7aefcbc13fc51568")
```

</details>

#### BLAKE2s key=00..1f in='' out=32 (blake2-kat.json kk=32 in='')

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Expected: 48a8997da407876b3d79c0d92325ad3b89cbb754d86ab71aee047ad345fd2c49
val key = _range_bytes(32)
val msg = _empty_bytes()
val digest = blake2s(key, msg, 32)
expect(_bytes_to_hex(digest)).to_equal("48a8997da407876b3d79c0d92325ad3b89cbb754d86ab71aee047ad345fd2c49")
```

</details>

#### BLAKE2b key=00..07 in='Hi There' out=64

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Reference (Python hashlib.blake2b, key=bytes(range(8))):
#   0f3623fb9296d25e4ebf6d11139e105a6265ad20bb38060e393fe43c9643718d
#   565d8c82d089265102171de74ff8dcdff7cd299f06d69d467a9be55c5d26cc95
val key = _range_bytes(8)
val msg = _hi_there_bytes()
val digest = blake2b(key, msg, 64)
expect(_bytes_to_hex(digest)).to_equal("0f3623fb9296d25e4ebf6d11139e105a6265ad20bb38060e393fe43c9643718d565d8c82d089265102171de74ff8dcdff7cd299f06d69d467a9be55c5d26cc95")
```

</details>

#### BLAKE2s key=00..07 in='Hi There' out=32

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Reference (Python hashlib.blake2s, key=bytes(range(8))):
#   fff44698fee4d219540d95f0f56d41888f344bf0924cef3f6d6a036a4c2aa747
val key = _range_bytes(8)
val msg = _hi_there_bytes()
val digest = blake2s(key, msg, 32)
expect(_bytes_to_hex(digest)).to_equal("fff44698fee4d219540d95f0f56d41888f344bf0924cef3f6d6a036a4c2aa747")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/crypto/blake2_rfc7693_kat_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- BLAKE2b RFC 7693 Appendix A test vectors
- BLAKE2s RFC 7693 Appendix B test vectors
- BLAKE2 keyed-mode KATs (blake2-kat.json)

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

# Sha1 Specification

> <details>

<!-- sdn-diagram:id=sha1_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=sha1_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

sha1_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=sha1_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Sha1 Specification

## Scenarios

### SHA-1 — FIPS 180-4 §B.1 canonical vectors

#### empty string

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(sha1_hex("")).to_equal("da39a3ee5e6b4b0d3255bfef95601890afd80709")
```

</details>

#### 'abc' (single-block)

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(sha1_hex("abc")).to_equal("a9993e364706816aba3e25717850c26c9cd0d89d")
```

</details>

#### 56-byte ABCD pattern (two-block, FIPS 180-4 §B.1)

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# "abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq"
# -> 84983e441c3bd26ebaae4aa1f95129e5e54670f1
expect(bytes_to_hex(sha1_bytes(_abcd_pattern_56()))).to_equal(
    "84983e441c3bd26ebaae4aa1f95129e5e54670f1"
)
```

</details>

<details>
<summary>Advanced: 1000 'a' bytes (multi-block stress, attested via Python hashlib)</summary>

#### 1000 'a' bytes (multi-block stress, attested via Python hashlib)

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# hashlib.sha1(b'a'*1000).hexdigest() = 291e9a6c66994949b57ba5e650361e98fc36b1ba
expect(bytes_to_hex(sha1_bytes(_bytes_repeat(0x61, 1000)))).to_equal(
    "291e9a6c66994949b57ba5e650361e98fc36b1ba"
)
```

</details>


</details>

### SHA-1 — output shape

#### digest is exactly 20 bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(sha1_bytes([]).len()).to_equal(20)
```

</details>

#### digest is exactly 20 bytes for non-empty input

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(sha1_bytes([0x61, 0x62, 0x63]).len()).to_equal(20)
```

</details>

#### hex form is exactly 40 lowercase chars

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(sha1_hex("abc").len()).to_equal(40)
```

</details>

### SHA-1 streaming API parity

#### init+update+final equals one-shot for 'abc'

- var ctx = sha1 init
- ctx = sha1 update


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ctx = sha1_init()
ctx = sha1_update(ctx, [0x61, 0x62, 0x63])
expect(bytes_to_hex(sha1_final(ctx))).to_equal(
    "a9993e364706816aba3e25717850c26c9cd0d89d"
)
```

</details>

#### create_sha1_context+update+finalize equals one-shot for ABCD pattern

- var ctx = create sha1 context
- ctx = sha1 update


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ctx = create_sha1_context()
ctx = sha1_update(ctx, _abcd_pattern_56())
expect(bytes_to_hex(sha1_finalize(ctx))).to_equal(
    "84983e441c3bd26ebaae4aa1f95129e5e54670f1"
)
```

</details>

#### two-chunk update equals one-shot (split 'abc' = 'a' || 'bc')

- var ctx = sha1 init
- ctx = sha1 update
- ctx = sha1 update


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ctx = sha1_init()
ctx = sha1_update(ctx, [0x61])
ctx = sha1_update(ctx, [0x62, 0x63])
expect(bytes_to_hex(sha1_finalize(ctx))).to_equal(
    "a9993e364706816aba3e25717850c26c9cd0d89d"
)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/crypto/sha1_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- SHA-1 — FIPS 180-4 §B.1 canonical vectors
- SHA-1 — output shape
- SHA-1 streaming API parity

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 10 |
| Active scenarios | 10 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

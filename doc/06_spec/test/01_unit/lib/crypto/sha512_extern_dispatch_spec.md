# Sha512 Extern Dispatch Specification

> <details>

<!-- sdn-diagram:id=sha512_extern_dispatch_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=sha512_extern_dispatch_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

sha512_extern_dispatch_spec -> std
sha512_extern_dispatch_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=sha512_extern_dispatch_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Sha512 Extern Dispatch Specification

## Scenarios

### SHA-512 rt_sha512_* interpreter dispatch — FIPS 180-4 KAT

#### FIPS 180-4 §C.0 empty string digest

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Expected: cf83e1357eefb8bdf1542850d66d8007d620e4050b5715dc83f4a921d36ce9ce
#           47d0d13c5d85f2b0ff8318d2877eec2f63b931bd47417a81a538327af927da3e
val empty: [u8] = []
val digest = sha512(empty)
expect(bytes_to_hex(digest)).to_equal("cf83e1357eefb8bdf1542850d66d8007d620e4050b5715dc83f4a921d36ce9ce47d0d13c5d85f2b0ff8318d2877eec2f63b931bd47417a81a538327af927da3e")
```

</details>

#### FIPS 180-4 §C.1 'abc' canary digest

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Expected: ddaf35a193617abacc417349ae20413112e6fa4e89a97ea20a9eeee64b55d39a
#           2192992a274fc1a836ba3c23a3feebbd454d4423643ce80e2a9ac94fa54ca49f
val abc: [u8] = [0x61, 0x62, 0x63]
val digest = sha512(abc)
expect(bytes_to_hex(digest)).to_equal("ddaf35a193617abacc417349ae20413112e6fa4e89a97ea20a9eeee64b55d39a2192992a274fc1a836ba3c23a3feebbd454d4423643ce80e2a9ac94fa54ca49f")
```

</details>

#### multi-block boundary: 256 bytes of 0x61 ('a') — 2 SHA-512 blocks

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# DEVIATION from FIPS §C.2/§C.3: 'a' × 256 (= 2 SHA-512 blocks of 128 B
# each, since the padding bumps it past one block) instead of the
# 112-byte FIPS string or 1M-byte vector. This keeps the spec
# interpreter-friendly while still exercising the multi-block branch
# of rt_sha512_hash.
# Reference (computed 2026-05-02):
#   python3 -c "import hashlib; print(hashlib.sha512(b'a'*256).hexdigest())"
val input = _make_256_a()
val digest = sha512(input)
expect(bytes_to_hex(digest)).to_equal("6a9169eb662f136d87374070e8828b3e615a7eca32a89446e9225b02832709be095e635c824a2bb70213ba2ea0ababac0809827843992c851903b7ac0c136699")
```

</details>

#### REQ-SHA512ID-002 byte-by-byte readback contract

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# The extern API is two-step: rt_sha512_hash stashes into a
# static buffer; rt_sha512_byte(i) reads byte i. The wrapper
# `sha512()` exercises i=0..63 — verify length is exactly 64.
val abc: [u8] = [0x61, 0x62, 0x63]
val digest = sha512(abc)
expect(digest.len().to_i64()).to_equal(64i64)
```

</details>

#### REQ-SHA512ID-002 stash-buffer overwrite — second hash overwrites first

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Two consecutive sha512() calls with different inputs must
# yield distinct digests (proves the static buffer is rewritten).
val a: [u8] = [0x61]
val b: [u8] = [0x62]
val da = sha512(a)
val db = sha512(b)
# Re-hash 'a' to confirm we still get the original 'a' digest.
val da_again = sha512(a)
expect(bytes_to_hex(da)).to_equal(bytes_to_hex(da_again))
# And the 'b' digest is different from 'a' digest.
expect(bytes_to_hex(da) == bytes_to_hex(db)).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/crypto/sha512_extern_dispatch_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- SHA-512 rt_sha512_* interpreter dispatch — FIPS 180-4 KAT

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

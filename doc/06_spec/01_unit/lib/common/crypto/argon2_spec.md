# Argon2 Specification

> <details>

<!-- sdn-diagram:id=argon2_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=argon2_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

argon2_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=argon2_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Argon2 Specification

## Scenarios

### Argon2id smoke (small interpreter-tractable parameters)

#### returns 32 bytes for tag_len=32 — native-verified golden

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Minimum valid: m_cost = 8 * parallelism = 8 KiB with p=1.
# Golden verified by running under bin/release/x86_64-unknown-linux-gnu/simple
# (native mode, where i64-add wraps correctly). RFC B.4 vector also passes
# native (see RFC KAT test below).
val pwd = _a2_ascii("password")
val salt = _a2_ascii("somesalt")
val tag = argon2id_bytes(pwd, salt, 1, 8, 1, 32)
expect(tag.len()).to_equal(32)
expect(bytes_to_hex(tag)).to_equal(
    "f137f8e186a403a679ccd0606e5ab5dcdafe43c1640855ac8c6e33e9bd63eeb3"
)
```

</details>

#### returns 16 bytes for tag_len=16 — H' uses correct BLAKE2b-16 digest, native-verified

<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# tag_len=16 exercises the _blake2b_core(data, 16) path in _a2_blake2b_n.
# Prior to fix, this used blake2b_512_bytes then truncated — wrong because
# BLAKE2b mixes digest_length into the IV (parameter block byte 0).
# Now uses _blake2b_core(data, 16) for correct parameterised BLAKE2b.
# Golden verified by native run (same value as interpreter confirms no
# u64-overflow difference between the two paths).
val pwd = _a2_ascii("password")
val salt = _a2_ascii("somesalt")
val tag = argon2id_bytes(pwd, salt, 1, 8, 1, 16)
expect(tag.len()).to_equal(16)
expect(bytes_to_hex(tag)).to_equal(
    "f73a73d271859d21ef45465da12bdf86"
)
```

</details>

#### returns 64 bytes for tag_len=64 — native-verified golden

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# tag_len=64 exercises the blake2b_512_bytes path in _a2_blake2b_n.
# Golden verified by native run.
val pwd = _a2_ascii("password")
val salt = _a2_ascii("somesalt")
val tag = argon2id_bytes(pwd, salt, 1, 8, 1, 64)
expect(tag.len()).to_equal(64)
expect(bytes_to_hex(tag)).to_equal(
    "1437f91898f231ac18bc80cbcd32883b34264c2927195fec7a7773226927033688422945a19069302e7e70233131350f89cb8a96daa78cee92f6b8416a5efd6c"
)
```

</details>

### Argon2id determinism and input sensitivity

#### is deterministic — same inputs produce same tag

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pwd = _a2_ascii("password")
val salt = _a2_ascii("somesalt")
val tag_a = argon2id_bytes(pwd, salt, 1, 8, 1, 32)
val tag_b = argon2id_bytes(pwd, salt, 1, 8, 1, 32)
expect(bytes_to_hex(tag_a)).to_equal(bytes_to_hex(tag_b))
```

</details>

#### salt sensitivity — differing salts produce differing tags

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pwd = _a2_ascii("password")
val salt1 = _a2_ascii("somesalt")
val salt2 = _a2_ascii("othrsalt")
val tag_a = argon2id_bytes(pwd, salt1, 1, 8, 1, 32)
val tag_b = argon2id_bytes(pwd, salt2, 1, 8, 1, 32)
expect(bytes_to_hex(tag_a)).to_not_equal(bytes_to_hex(tag_b))
```

</details>

#### password sensitivity — differing passwords produce differing tags

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pwd1 = _a2_ascii("password")
val pwd2 = _a2_ascii("passw0rd")
val salt = _a2_ascii("somesalt")
val tag_a = argon2id_bytes(pwd1, salt, 1, 8, 1, 32)
val tag_b = argon2id_bytes(pwd2, salt, 1, 8, 1, 32)
expect(bytes_to_hex(tag_a)).to_not_equal(bytes_to_hex(tag_b))
```

</details>

#### argon2id_bytes_ks with non-empty key differs from empty key

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pwd = _a2_ascii("password")
val salt = _a2_ascii("somesalt")
val empty = _a2_empty()
val key = _a2_ascii("secret")
val tag_no_key = argon2id_bytes_ks(pwd, salt, empty, empty, 1, 8, 1, 32)
val tag_with_key = argon2id_bytes_ks(pwd, salt, key, empty, 1, 8, 1, 32)
expect(bytes_to_hex(tag_no_key)).to_not_equal(bytes_to_hex(tag_with_key))
```

</details>

### Argon2id RFC 9106 Appendix B.4 — known-answer test (TIMEOUT in interpreter)

#### RFC B.4: P=0x01×32 S=0x02×16 K=0x03×8 X=0x04×12 t=3 m=32 p=4 T=32

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# KNOWN TIMEOUT IN INTERPRETER MODE.
# Correct expected value per RFC 9106 Appendix B.4.
# This test will timeout under bin/simple test (60s watchdog).
# Run under native: bin/simple build && ./release/simple run <this_file>
val pwd = _a2_repeat(1, 32)
val salt = _a2_repeat(2, 16)
val key = _a2_repeat(3, 8)
val ad = _a2_repeat(4, 12)
val result = argon2id_bytes_ks(pwd, salt, key, ad, 3, 32, 4, 32)
expect(bytes_to_hex(result)).to_equal(
    "0d640df58d78766c08c037a34a8b53c9d01ef0452d75b65eb52520e96b01e659"
)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/crypto/argon2_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Argon2id smoke (small interpreter-tractable parameters)
- Argon2id determinism and input sensitivity
- Argon2id RFC 9106 Appendix B.4 — known-answer test (TIMEOUT in interpreter)

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

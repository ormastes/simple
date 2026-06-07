# Pbkdf2 Industry Vectors Specification

> <details>

<!-- sdn-diagram:id=pbkdf2_industry_vectors_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=pbkdf2_industry_vectors_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

pbkdf2_industry_vectors_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=pbkdf2_industry_vectors_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Pbkdf2 Industry Vectors Specification

## Scenarios

### PBKDF2-HMAC-SHA-256 industry test vectors

#### TC1: password-field=password salt=salt c=1 dkLen=32 → 120fb6cf...

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# draft-josefsson-pbkdf2-test-vectors-00 §2
expect(bytes_to_hex(pbkdf2_sha256_bytes(_password(), _salt(), 1, 32))).to_equal(
    "120fb6cffcf8b32c43e7225256c4f837a86548c92ccc35480805987cb70be17b"
)
```

</details>

#### TC2: password-field=password salt=salt c=2 dkLen=32 → ae4d0c95...

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# draft-josefsson-pbkdf2-test-vectors-00 §2
expect(bytes_to_hex(pbkdf2_sha256_bytes(_password(), _salt(), 2, 32))).to_equal(
    "ae4d0c95af6b46d32d0adff928f06dd02a303f8ef3c251dfd6e2d85a95474c43"
)
```

</details>

#### extra: password-field=password salt=salt c=1000 dkLen=32 (perf-path coverage)

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Not an RFC vector. Exercises the c-iter fast path (cached
# SHA-256 K_ipad/K_opad prefix states + pre-built padding tail
# block). Hash cross-checked 2026-05-01 against the reference
# pre-optimisation implementation: both produce the same 32-byte
# output for these inputs at c=1000.
expect(bytes_to_hex(pbkdf2_sha256_bytes(_password(), _salt(), 1000, 32))).to_equal(
    "632c2812e46d4604102ba7618e9d6d7d2f8128f6266b4a03264d2a0460b7dcb3"
)
```

</details>

### PBKDF2-HMAC-SHA-512 industry test vectors

#### TC1: password-field=password salt=salt c=1 dkLen=64 → 867f70cf...

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# draft-josefsson-pbkdf2-test-vectors-00 §3
expect(bytes_to_hex(pbkdf2_sha512_bytes(_password(), _salt(), 1, 64))).to_equal(
    "867f70cf1ade02cff3752599a3a53dc4af34c7a669815ae5d513554e1c8cf252c02d470a285a0501bad999bfe943c08f050235d7d68b1da55e63f73b60a57fce"
)
```

</details>

#### TC2: password-field=password salt=salt c=2 dkLen=64 → e1d9c16a...

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# draft-josefsson-pbkdf2-test-vectors-00 §3
expect(bytes_to_hex(pbkdf2_sha512_bytes(_password(), _salt(), 2, 64))).to_equal(
    "e1d9c16aa681708a45f5c7c4e215ceb66e011a2e9f0040713f18aefdb866d53cf76cab2868a39b9f7840edce4fef5a82be67335c77a6068e04112754f27ccf4e"
)
```

</details>

#### long-key: password-field=200×'A' salt=salt c=1 dkLen=64 (HMAC key>block_size)

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Not in any RFC, but cross-checked 2026-05-01 against Python
# `hashlib.pbkdf2_hmac("sha512", b"A"*200, b"salt", 1, 64)`.
# Forces the `key > 128B → sha512_bytes(key)` branch in
# `hmac_sha512_bytes`, which the short-key reference spec does
# not cover.
expect(bytes_to_hex(pbkdf2_sha512_bytes(_long_password_sha512(), _salt(), 1, 64))).to_equal(
    "d4d976cd28931aa0d74fe2ea17c14c15b6321b6e69520106468a2812bfc79866058d097bd7c71e1c498512f66248928f162833dce24793d7203dc2d2eabe9429"
)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/crypto/pbkdf2_industry_vectors_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- PBKDF2-HMAC-SHA-256 industry test vectors
- PBKDF2-HMAC-SHA-512 industry test vectors

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

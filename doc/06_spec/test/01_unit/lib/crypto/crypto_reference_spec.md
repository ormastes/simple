# Crypto Reference Specification

> <details>

<!-- sdn-diagram:id=crypto_reference_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=crypto_reference_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

crypto_reference_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=crypto_reference_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Crypto Reference Specification

## Scenarios

### constant_time_compare

#### matches equality semantics for same length values

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(constant_time_compare("abcdef", "abcdef")).to_equal(true)
expect(constant_time_compare("abcdef", "abcdeg")).to_equal(false)
```

</details>

#### rejects different length values

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(constant_time_compare("abcdef", "abc")).to_equal(false)
```

</details>

### legacy hash reference vectors

#### matches SHA-1 known-answer vectors

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(sha1_hex("")).to_equal("da39a3ee5e6b4b0d3255bfef95601890afd80709")
expect(sha1_hex("abc")).to_equal("a9993e364706816aba3e25717850c26c9cd0d89d")
```

</details>

#### matches MD5 known-answer vectors

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(md5_hex("")).to_equal("d41d8cd98f00b204e9800998ecf8427e")
expect(md5_hex("abc")).to_equal("900150983cd24fb0d6963f7d28e17f72")
```

</details>

### PBKDF2 reference vectors

#### matches PBKDF2-HMAC-SHA256 RFC 6070 style vector

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val derived = pbkdf2_sha256("password", "salt", 1)
expect(bytes_to_hex(derived)).to_equal("120fb6cffcf8b32c43e7225256c4f837a86548c92ccc35480805987cb70be17b")
```

</details>

#### matches PBKDF2-HMAC-SHA512 reference vector

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val derived = pbkdf2_sha512("password", "salt", 1)
expect(bytes_to_hex(derived)).to_equal("867f70cf1ade02cff3752599a3a53dc4af34c7a669815ae5d513554e1c8cf252c02d470a285a0501bad999bfe943c08f050235d7d68b1da55e63f73b60a57fce")
```

</details>

#### uses SHA-256 as the default algorithm

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val explicit = pbkdf2_sha256("password", "salt", 1)
val fallback = pbkdf2_with_algorithm("password", "salt", 1, "unknown")
expect(bytes_to_hex(fallback)).to_equal(bytes_to_hex(explicit))
expect(get_recommended_pbkdf2_iterations()).to_be_greater_than(99999)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/crypto/crypto_reference_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- constant_time_compare
- legacy hash reference vectors
- PBKDF2 reference vectors

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

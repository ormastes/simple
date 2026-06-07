# Sha2 Nist Vectors Specification

> <details>

<!-- sdn-diagram:id=sha2_nist_vectors_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=sha2_nist_vectors_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

sha2_nist_vectors_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=sha2_nist_vectors_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Sha2 Nist Vectors Specification

## Scenarios

### SHA-256 NIST FIPS 180-4 test vectors

#### FIPS 180-4 §B.0 empty string digest

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Expected: e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855
expect(sha256_hex("")).to_equal("e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855")
```

</details>

#### FIPS 180-4 §B.1 'abc' (canary) digest

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Expected: ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad
expect(sha256_hex("abc")).to_equal("ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad")
```

</details>

#### FIPS 180-4 §B.2 56-byte string digest

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Input: "abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq"
# Expected: 248d6a61d20638b8e5c026930c3e6039a33ce45964ff2167f6ecedd419db06c1
expect(sha256_hex("abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq")).to_equal("248d6a61d20638b8e5c026930c3e6039a33ce45964ff2167f6ecedd419db06c1")
```

</details>

#### multi-block: 1024 bytes of 0x61 ('a') — 16 SHA-256 blocks

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# DEVIATION: FIPS §B.3 specifies 1M 'a' bytes (cdc76e5c...); replaced with
# 1024 bytes to stay within interpreter timeout. Multi-block boundary covered.
# Reference: python3 => 2edc986847e209b4016e141a6dc8716d3207350f416969382d431539bf292e4a
val input = _make_1024_a()
expect(bytes_to_hex(sha256_bytes(input))).to_equal("2edc986847e209b4016e141a6dc8716d3207350f416969382d431539bf292e4a")
```

</details>

### SHA-512 NIST FIPS 180-4 test vectors

#### FIPS 180-4 §C.0 empty string digest

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Expected: cf83e1357eefb8bdf1542850d66d8007d620e4050b5715dc83f4a921d36ce9ce
#           47d0d13c5d85f2b0ff8318d2877eec2f63b931bd47417a81a538327af927da3e
expect(sha512_hex("")).to_equal("cf83e1357eefb8bdf1542850d66d8007d620e4050b5715dc83f4a921d36ce9ce47d0d13c5d85f2b0ff8318d2877eec2f63b931bd47417a81a538327af927da3e")
```

</details>

#### FIPS 180-4 §C.1 'abc' (canary) digest

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Expected: ddaf35a193617abacc417349ae20413112e6fa4e89a97ea20a9eeee64b55d39a
#           2192992a274fc1a836ba3c23a3feebbd454d4423643ce80e2a9ac94fa54ca49f
expect(sha512_hex("abc")).to_equal("ddaf35a193617abacc417349ae20413112e6fa4e89a97ea20a9eeee64b55d39a2192992a274fc1a836ba3c23a3feebbd454d4423643ce80e2a9ac94fa54ca49f")
```

</details>

#### FIPS 180-4 §C.2 112-byte string digest

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Input: "abcdefghbcdefghicdefghijdefghijkefghijklfghijklmghijklmn
#         hijklmnoijklmnopjklmnopqklmnopqrlmnopqrsmnopqrstnopqrstu"
# Expected: 8e959b75dae313da8cf4f72814fc143f8f7779c6eb9f7fa17299aeadb6889018
#           501d289e4900f7e4331b99dec4b5433ac7d329eeb6dd26545e96e55b874be909
expect(sha512_hex("abcdefghbcdefghicdefghijdefghijkefghijklfghijklmghijklmnhijklmnoijklmnopjklmnopqklmnopqrlmnopqrsmnopqrstnopqrstu")).to_equal("8e959b75dae313da8cf4f72814fc143f8f7779c6eb9f7fa17299aeadb6889018501d289e4900f7e4331b99dec4b5433ac7d329eeb6dd26545e96e55b874be909")
```

</details>

#### multi-block: 1024 bytes of 0x61 ('a') — 8 SHA-512 blocks

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# DEVIATION: FIPS §C.3 specifies 1M 'a' bytes; reduced to 1024.
# Reference: python3 => 74b22492e3b9a86a9c93c23a69f821ebafa429302c1f4054b4bc37356a4bae05
#                        6d9ccbc6f24093a25704faaa72bd21a5f337ca9ec92f32369d24e6b9fae954d8
val input = _make_1024_a()
expect(bytes_to_hex(sha512_bytes(input))).to_equal("74b22492e3b9a86a9c93c23a69f821ebafa429302c1f4054b4bc37356a4bae056d9ccbc6f24093a25704faaa72bd21a5f337ca9ec92f32369d24e6b9fae954d8")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/crypto/sha2_nist_vectors_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- SHA-256 NIST FIPS 180-4 test vectors
- SHA-512 NIST FIPS 180-4 test vectors

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

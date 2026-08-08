# Camellia Rfc3713 Kat Specification

> <details>

<!-- sdn-diagram:id=camellia_rfc3713_kat_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=camellia_rfc3713_kat_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

camellia_rfc3713_kat_spec -> std
camellia_rfc3713_kat_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=camellia_rfc3713_kat_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Camellia Rfc3713 Kat Specification

## Scenarios

### Camellia RFC 3713 Appendix A — 128-bit

#### A.1 Camellia-128 encrypt → 67673138549669730857065648eabe43

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ct = camellia128_encrypt_block(_a1_key(), _a1_pt())
expect(_bytes_hex(ct)).to_equal("67673138549669730857065648eabe43")
```

</details>

#### A.1 Camellia-128 output is 16 bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ct = camellia128_encrypt_block(_a1_key(), _a1_pt())
expect(ct.len()).to_equal(16)
```

</details>

#### A.1 Camellia-128 decrypt roundtrip

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ct = camellia128_encrypt_block(_a1_key(), _a1_pt())
val recovered = camellia128_decrypt_block(_a1_key(), ct)
expect(_bytes_hex(recovered)).to_equal("0123456789abcdeffedcba9876543210")
```

</details>

### Camellia RFC 3713 Appendix A — 192-bit

#### A.2 Camellia-192 encrypt → b4993401b3e996f84ee5cee7d79b09b9

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ct = camellia192_encrypt_block(_a2_key(), _a2_pt())
expect(_bytes_hex(ct)).to_equal("b4993401b3e996f84ee5cee7d79b09b9")
```

</details>

#### A.2 Camellia-192 output is 16 bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ct = camellia192_encrypt_block(_a2_key(), _a2_pt())
expect(ct.len()).to_equal(16)
```

</details>

#### A.2 Camellia-192 decrypt roundtrip

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ct = camellia192_encrypt_block(_a2_key(), _a2_pt())
val recovered = camellia192_decrypt_block(_a2_key(), ct)
expect(_bytes_hex(recovered)).to_equal("0123456789abcdeffedcba9876543210")
```

</details>

### Camellia RFC 3713 Appendix A — 256-bit

#### A.3 Camellia-256 encrypt → 9acc237dff16d76c20ef7c919e3a7509

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ct = camellia256_encrypt_block(_a3_key(), _a3_pt())
expect(_bytes_hex(ct)).to_equal("9acc237dff16d76c20ef7c919e3a7509")
```

</details>

#### A.3 Camellia-256 output is 16 bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ct = camellia256_encrypt_block(_a3_key(), _a3_pt())
expect(ct.len()).to_equal(16)
```

</details>

#### A.3 Camellia-256 decrypt roundtrip

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ct = camellia256_encrypt_block(_a3_key(), _a3_pt())
val recovered = camellia256_decrypt_block(_a3_key(), ct)
expect(_bytes_hex(recovered)).to_equal("0123456789abcdeffedcba9876543210")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/crypto/camellia_rfc3713_kat_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Camellia RFC 3713 Appendix A — 128-bit
- Camellia RFC 3713 Appendix A — 192-bit
- Camellia RFC 3713 Appendix A — 256-bit

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

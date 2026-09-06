# Sha3 Kat Specification

> <details>

<!-- sdn-diagram:id=sha3_kat_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=sha3_kat_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

sha3_kat_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=sha3_kat_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Sha3 Kat Specification

## Scenarios

### SHA3-256 — FIPS 202 known-answer vectors

#### SHA3-256(\

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(bytes_to_hex(sha3_256_bytes(_empty()))).to_equal(
    "a7ffc6f8bf1ed76651c14756a061d662f580ff4de43b49fa82d80a4b80f8434a"
)
```

</details>

#### SHA3-256(\

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(bytes_to_hex(sha3_256_bytes(_abc()))).to_equal(
    "3a985da74fe225b2045c172d6bd390bd855f086e3e9d525b46bfe24511431532"
)
```

</details>

#### Streaming SHA3-256(\

- var ctx = create sha3 256 context
- ctx = sha3 update
- ctx = sha3 update


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ctx = create_sha3_256_context()
ctx = sha3_update(ctx, [0x61])
ctx = sha3_update(ctx, [0x62, 0x63])
expect(bytes_to_hex(sha3_finalize(ctx, 32))).to_equal(
    "3a985da74fe225b2045c172d6bd390bd855f086e3e9d525b46bfe24511431532"
)
```

</details>

### SHA3-384 — FIPS 202 known-answer vectors

#### SHA3-384(\

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(bytes_to_hex(sha3_384_bytes(_empty()))).to_equal(
    "0c63a75b845e4f7d01107d852e4c2485c51a50aaaa94fc61995e71bbee983a2ac3713831264adb47fb6bd1e058d5f004"
)
```

</details>

#### SHA3-384(\

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(bytes_to_hex(sha3_384_bytes(_abc()))).to_equal(
    "ec01498288516fc926459f58e2c6ad8df9b473cb0fc08c2596da7cf0e49be4b298d88cea927ac7f539f1edf228376d25"
)
```

</details>

### SHA3-512 — FIPS 202 known-answer vectors

#### SHA3-512(\

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(bytes_to_hex(sha3_512_bytes(_empty()))).to_equal(
    "a69f73cca23a9ac5c8b567dc185a756e97c982164fe25859e0d1dcc1475c80a615b2123af1f5f94c11e3e9402c3ac558f500199d95b6d3e301758586281dcd26"
)
```

</details>

#### SHA3-512(\

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(bytes_to_hex(sha3_512_bytes(_abc()))).to_equal(
    "b751850b1a57168a5693cd924b6b096e08f621827444f70d884f5d0240d2712e10e116e9192af3c91a7ec57647e3934057340b4cf408d5a56592f8274eec53f0"
)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/crypto/sha3_kat_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- SHA3-256 — FIPS 202 known-answer vectors
- SHA3-384 — FIPS 202 known-answer vectors
- SHA3-512 — FIPS 202 known-answer vectors

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

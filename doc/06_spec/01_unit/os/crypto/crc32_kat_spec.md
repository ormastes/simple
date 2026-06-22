# Crc32 Kat Specification

> <details>

<!-- sdn-diagram:id=crc32_kat_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=crc32_kat_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

crc32_kat_spec -> std
crc32_kat_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=crc32_kat_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Crc32 Kat Specification

## Scenarios

### CRC-32 IEEE 802.3 one-shot KATs

#### empty input → 0x00000000

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(crc32(_empty())).to_equal(0x00000000)
```

</details>

#### \

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(crc32(_abc())).to_equal(0x352441C2)
```

</details>

#### \

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(crc32(_check_sequence())).to_equal(0xCBF43926)
```

</details>

### CRC-32C Castagnoli one-shot KATs

#### empty input → 0x00000000

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(crc32c(_empty())).to_equal(0x00000000)
```

</details>

#### \

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(crc32c(_abc())).to_equal(0x364B3FB7)
```

</details>

#### \

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(crc32c(_check_sequence())).to_equal(0xE3069283)
```

</details>

### CRC-32 IEEE 802.3 streaming API

#### streaming \

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s1 = crc32_update(crc32_init(), _abc_part1())
val s2 = crc32_update(s1, _abc_part2())
val result = crc32_finalize(s2)
expect(result).to_equal(0x352441C2)
```

</details>

#### streaming empty matches one-shot

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = crc32_finalize(crc32_update(crc32_init(), _empty()))
expect(result).to_equal(0x00000000)
```

</details>

### CRC-32C Castagnoli streaming API

#### streaming \

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s1 = crc32c_update(crc32c_init(), _abc_part1())
val s2 = crc32c_update(s1, _abc_part2())
val result = crc32c_finalize(s2)
expect(result).to_equal(0x364B3FB7)
```

</details>

#### streaming empty matches one-shot

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = crc32c_finalize(crc32c_update(crc32c_init(), _empty()))
expect(result).to_equal(0x00000000)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/crypto/crc32_kat_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- CRC-32 IEEE 802.3 one-shot KATs
- CRC-32C Castagnoli one-shot KATs
- CRC-32 IEEE 802.3 streaming API
- CRC-32C Castagnoli streaming API

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 10 |
| Active scenarios | 10 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

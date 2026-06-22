# Sm3 Kat Specification

> <details>

<!-- sdn-diagram:id=sm3_kat_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=sm3_kat_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

sm3_kat_spec -> std
sm3_kat_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=sm3_kat_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Sm3 Kat Specification

## Scenarios

### SM3 — GB/T 32905-2012 known-answer vectors

#### SM3(\

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_bytes_hex(sm3_hash(_abc_bytes()))).to_equal(
    "66c7f0f462eeedd9d1f2d46bdc10e4e24167c4875cf2f7a2297da02b8f4ba8e0"
)
```

</details>

#### SM3(\

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_bytes_hex(sm3_hash(_abcd16_bytes()))).to_equal(
    "debe9ff92275b8a138604889c18e5a4d6fdb70e5387e5765293dcba39c0c5732"
)
```

</details>

#### SM3(\

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_bytes_hex(sm3_hash(_empty_bytes()))).to_equal(
    "1ab21d8355cfa17f8e61194831e81a8f22bec8c728fefb747ed035eb5082aa2b"
)
```

</details>

#### SM3 digest length is 32 bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(sm3_hash(_empty_bytes()).len()).to_equal(32)
```

</details>

#### SM3 padding produces multiple-of-64 length

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(sm3_pad(_abc_bytes()).len() % 64).to_equal(0)
```

</details>

#### sm3_compress accepts IV state and 64-byte block and returns 8 words

1. block push
2. state iv push
3. state iv push
4. state iv push
5. state iv push
6. state iv push
7. state iv push
8. state iv push
9. state iv push
   - Expected: result.len() equals `8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var block: [u8] = []
var bi = 0
while bi < 64:
    block.push(0x00)
    bi = bi + 1
var state_iv = []
state_iv.push(0x7380166F)
state_iv.push(0x4914B2B9)
state_iv.push(0x172442D7)
state_iv.push(0xDA8A0600)
state_iv.push(0xA96F30BC)
state_iv.push(0x163138AA)
state_iv.push(0xE38DEE4D)
state_iv.push(0xB0FB0E4E)
val result = sm3_compress(state_iv, block)
expect(result.len()).to_equal(8)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/crypto/sm3_kat_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- SM3 — GB/T 32905-2012 known-answer vectors

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

# Ripemd160 Specification

> <details>

<!-- sdn-diagram:id=ripemd160_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=ripemd160_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

ripemd160_spec -> std
ripemd160_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=ripemd160_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Ripemd160 Specification

## Scenarios

### RIPEMD-160 — official ISO/IEC 10118-3 known-answer vectors

#### empty string

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# RIPEMD-160("") = 9c1185a5c5e9fc54612808977ee8f548b2258d31
expect(ripemd160_hex("")).to_equal("9c1185a5c5e9fc54612808977ee8f548b2258d31")
```

</details>

#### single character 'a'

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# RIPEMD-160("a") = 0bdc9d2d256b3ee9daae347be6f4dc835a467ffe
expect(ripemd160_hex("a")).to_equal("0bdc9d2d256b3ee9daae347be6f4dc835a467ffe")
```

</details>

#### 'abc'

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# RIPEMD-160("abc") = 8eb208f7e05d987a9b044a8e98c6b087f15a0bfc
expect(ripemd160_hex("abc")).to_equal("8eb208f7e05d987a9b044a8e98c6b087f15a0bfc")
```

</details>

#### 'message digest'

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# RIPEMD-160("message digest") = 5d0689ef49d2fae572b881b123a85ffa21595f36
expect(ripemd160_hex("message digest")).to_equal("5d0689ef49d2fae572b881b123a85ffa21595f36")
```

</details>

#### lowercase alphabet a-z

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# RIPEMD-160("abcdefghijklmnopqrstuvwxyz") = f71c27109c692c1b56bbdceb5b9d2865b3708dbc
expect(ripemd160_hex("abcdefghijklmnopqrstuvwxyz")).to_equal("f71c27109c692c1b56bbdceb5b9d2865b3708dbc")
```

</details>

#### alphanumeric A-Z + a-z + 0-9

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# RIPEMD-160("ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789")
#   = b0e20b6e3116640286ed3a87a5713079b21f5189
val msg = "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789"
expect(ripemd160_hex(msg)).to_equal("b0e20b6e3116640286ed3a87a5713079b21f5189")
```

</details>

#### '1234567890' repeated 8 times (80-byte input)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# RIPEMD-160("12345678901234567890...") = 9b752e45573d4b39f4dbd3323cab82bf63326bfb
expect(ripemd160_hex(_ten_digits_x8())).to_equal("9b752e45573d4b39f4dbd3323cab82bf63326bfb")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/crypto/ripemd160_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- RIPEMD-160 — official ISO/IEC 10118-3 known-answer vectors

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

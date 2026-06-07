# Reed Solomon Specification

> <details>

<!-- sdn-diagram:id=reed_solomon_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=reed_solomon_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

reed_solomon_spec -> std
reed_solomon_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=reed_solomon_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 24 | 24 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Reed Solomon Specification

## Scenarios

### Reed-Solomon GF(2^8) encoder KAT (n=10, k=4)

#### produces correct parity byte 0 (0xfa)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = rs_gf256_encode(_data(), 10, 4)
expect(p[0].to_u64()).to_equal(0xfau64)
```

</details>

#### produces correct parity byte 1 (0x22)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = rs_gf256_encode(_data(), 10, 4)
expect(p[1].to_u64()).to_equal(0x22u64)
```

</details>

#### produces correct parity byte 2 (0x1d)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = rs_gf256_encode(_data(), 10, 4)
expect(p[2].to_u64()).to_equal(0x1du64)
```

</details>

#### produces correct parity byte 3 (0xc7)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = rs_gf256_encode(_data(), 10, 4)
expect(p[3].to_u64()).to_equal(0xc7u64)
```

</details>

#### produces correct parity byte 4 (0x40)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = rs_gf256_encode(_data(), 10, 4)
expect(p[4].to_u64()).to_equal(0x40u64)
```

</details>

#### produces correct parity byte 5 (0x6f)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = rs_gf256_encode(_data(), 10, 4)
expect(p[5].to_u64()).to_equal(0x6fu64)
```

</details>

#### returns exactly (n-k)=6 parity bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = rs_gf256_encode(_data(), 10, 4)
expect(p.len()).to_equal(6u64)
```

</details>

### Reed-Solomon GF(2^8) decoder — clean codeword

#### clean codeword returns Ok

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = rs_gf256_decode(_codeword(), 10, 4)
expect(_decode_ok(result)).to_equal(true)
```

</details>

#### clean codeword recovers data byte 0 (0x48)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val d = _decode_data(rs_gf256_decode(_codeword(), 10, 4))
expect(d[0].to_u64()).to_equal(0x48u64)
```

</details>

#### clean codeword recovers data byte 1 (0x65)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val d = _decode_data(rs_gf256_decode(_codeword(), 10, 4))
expect(d[1].to_u64()).to_equal(0x65u64)
```

</details>

#### clean codeword recovers data byte 2 (0x6c)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val d = _decode_data(rs_gf256_decode(_codeword(), 10, 4))
expect(d[2].to_u64()).to_equal(0x6cu64)
```

</details>

#### clean codeword recovers data byte 3 (0x6c)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val d = _decode_data(rs_gf256_decode(_codeword(), 10, 4))
expect(d[3].to_u64()).to_equal(0x6cu64)
```

</details>

### Reed-Solomon GF(2^8) decoder — 1-error correction

#### 1-error: returns Ok

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = rs_gf256_decode(_corrupt1(), 10, 4)
expect(_decode_ok(result)).to_equal(true)
```

</details>

#### 1-error: recovers data byte 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val d = _decode_data(rs_gf256_decode(_corrupt1(), 10, 4))
expect(d[0].to_u64()).to_equal(0x48u64)
```

</details>

#### 1-error: recovers data byte 3 (the corrupted one)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val d = _decode_data(rs_gf256_decode(_corrupt1(), 10, 4))
expect(d[3].to_u64()).to_equal(0x6cu64)
```

</details>

### Reed-Solomon GF(2^8) decoder — 2-error correction

#### 2-error: returns Ok

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = rs_gf256_decode(_corrupt2(), 10, 4)
expect(_decode_ok(result)).to_equal(true)
```

</details>

#### 2-error: recovers data byte 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val d = _decode_data(rs_gf256_decode(_corrupt2(), 10, 4))
expect(d[0].to_u64()).to_equal(0x48u64)
```

</details>

#### 2-error: recovers data byte 1 (corrupted)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val d = _decode_data(rs_gf256_decode(_corrupt2(), 10, 4))
expect(d[1].to_u64()).to_equal(0x65u64)
```

</details>

### Reed-Solomon GF(2^8) decoder — 3-error correction (t=3)

#### 3-error: returns Ok

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = rs_gf256_decode(_corrupt3(), 10, 4)
expect(_decode_ok(result)).to_equal(true)
```

</details>

#### 3-error: recovers data byte 0 (corrupted)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val d = _decode_data(rs_gf256_decode(_corrupt3(), 10, 4))
expect(d[0].to_u64()).to_equal(0x48u64)
```

</details>

#### 3-error: recovers data byte 1

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val d = _decode_data(rs_gf256_decode(_corrupt3(), 10, 4))
expect(d[1].to_u64()).to_equal(0x65u64)
```

</details>

#### 3-error: recovers data byte 2

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val d = _decode_data(rs_gf256_decode(_corrupt3(), 10, 4))
expect(d[2].to_u64()).to_equal(0x6cu64)
```

</details>

#### 3-error: recovers data byte 3

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val d = _decode_data(rs_gf256_decode(_corrupt3(), 10, 4))
expect(d[3].to_u64()).to_equal(0x6cu64)
```

</details>

### Reed-Solomon GF(2^8) decoder — over-capacity (4 errors > t=3)

#### 4-error: returns Err (not Ok)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = rs_gf256_decode(_corrupt4(), 10, 4)
expect(_decode_err(result)).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/codec/reed_solomon_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Reed-Solomon GF(2^8) encoder KAT (n=10, k=4)
- Reed-Solomon GF(2^8) decoder — clean codeword
- Reed-Solomon GF(2^8) decoder — 1-error correction
- Reed-Solomon GF(2^8) decoder — 2-error correction
- Reed-Solomon GF(2^8) decoder — 3-error correction (t=3)
- Reed-Solomon GF(2^8) decoder — over-capacity (4 errors > t=3)

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 24 |
| Active scenarios | 24 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

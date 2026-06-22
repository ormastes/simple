# Sha384 Kat Specification

> <details>

<!-- sdn-diagram:id=sha384_kat_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=sha384_kat_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

sha384_kat_spec -> std
sha384_kat_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=sha384_kat_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Sha384 Kat Specification

## Scenarios

### SHA-384 — FIPS 180-4 known-answer vectors

#### padding empty: byte[0]=0x80, length=128

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val padded = _sha384_pad(_empty_bytes())
expect(padded.len()).to_equal(128)
expect(padded[0]).to_equal(0x80)
expect(padded[1]).to_equal(0x00)
expect(padded[127]).to_equal(0x00)
```

</details>

#### diag: w[0] for empty input = 0x8000000000000000

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_sha384_diag_w0(_empty_bytes())).to_equal(0x8000000000000000)
```

</details>

#### diag: h[0] = 0xcbbb9d5dc1059ed8

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_sha384_diag_h0()).to_equal(0xCBBB9D5DC1059ED8)
```

</details>

#### diag: big_sigma0(SHA-384 h[0]) == canonical 0xdb9a810738c045b1

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Regression guard for the u64-fn-param right-shift sign-extension bug
# fixed via _logical_shr64 in sha384.spl. Before fix, this returned
# 0xfffffffcb6c045b1 because (x >> 28/34/39) on a u64 fn param
# arg with bit 63 set sign-extended into the high bits. See
# doc/08_tracking/bug/u64_right_shift_fn_param_arithmetic_2026-05-02.md.
expect(_sha384_diag_big_sigma0_h0()).to_equal(0xdb9a810738c045b1)
```

</details>

#### SHA-384(\

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_bytes_hex(sha384(_empty_bytes()))).to_equal(
    "38b060a751ac96384cd9327eb1b1e36a21fdb71114be07434c0cc7bf63f6e1da274edebfe76f65fbd51ad2f14898b95b"
)
```

</details>

#### SHA-384(\

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_bytes_hex(sha384(_abc_bytes()))).to_equal(
    "cb00753f45a35e8bb5a03d699ac65007272c32ab0eded1631a8b605a43ff5bed8086072ba1e7cc2358baeca134c825a7"
)
```

</details>

#### SHA-384 output length is 48 bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(sha384(_abc_bytes()).len()).to_equal(48)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/crypto/sha384_kat_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- SHA-384 — FIPS 180-4 known-answer vectors

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

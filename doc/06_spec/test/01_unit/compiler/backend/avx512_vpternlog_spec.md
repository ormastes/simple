# Avx512 Vpternlog Specification

> <details>

<!-- sdn-diagram:id=avx512_vpternlog_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=avx512_vpternlog_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

avx512_vpternlog_spec -> std
avx512_vpternlog_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=avx512_vpternlog_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Avx512 Vpternlog Specification

## Scenarios

### AVX-512 VPTERNLOGD byte-level emit

#### VPTERNLOGD zmm0,zmm0,zmm0,0xFF (all-ones)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bytes = emit_avx512_vpternlogd(X86_ZMM0, X86_ZMM0, X86_ZMM0, 0xFF)
expect(_list_hex(bytes)).to_equal("62f37d4825c0ff")
```

</details>

#### VPTERNLOGD zmm1,zmm2,zmm3,0xAC (blend)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bytes = emit_avx512_vpternlogd(X86_ZMM1, X86_ZMM2, X86_ZMM3, 0xAC)
expect(_list_hex(bytes)).to_equal("62f36d4825cbac")
```

</details>

#### VPTERNLOGD zmm0,zmm1,zmm0,0x00 (zero)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bytes = emit_avx512_vpternlogd(X86_ZMM0, X86_ZMM1, X86_ZMM0, 0x00)
expect(_list_hex(bytes)).to_equal("62f3754825c000")
```

</details>

#### VPTERNLOGD zmm0,zmm0,zmm0,0x96 (XOR3)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bytes = emit_avx512_vpternlogd(X86_ZMM0, X86_ZMM0, X86_ZMM0, 0x96)
expect(_list_hex(bytes)).to_equal("62f37d4825c096")
```

</details>

#### output length is 7 bytes (EVEX 4 + opcode 1 + ModRM 1 + imm8 1)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bytes = emit_avx512_vpternlogd(X86_ZMM0, X86_ZMM0, X86_ZMM0, 0xFF)
expect(bytes.len()).to_equal(7)
```

</details>

### AVX-512 VPTERNLOGQ byte-level emit

#### VPTERNLOGQ zmm0,zmm0,zmm0,0x96 (XOR3, 64-bit)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bytes = emit_avx512_vpternlogq(X86_ZMM0, X86_ZMM0, X86_ZMM0, 0x96)
expect(_list_hex(bytes)).to_equal("62f3fd4825c096")
```

</details>

#### VPTERNLOGQ output length is 7 bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bytes = emit_avx512_vpternlogq(X86_ZMM0, X86_ZMM0, X86_ZMM0, 0x96)
expect(bytes.len()).to_equal(7)
```

</details>

#### VPTERNLOGQ W-bit differs from VPTERNLOGD (byte index 2)

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val d_bytes = emit_avx512_vpternlogd(X86_ZMM0, X86_ZMM0, X86_ZMM0, 0x96)
val q_bytes = emit_avx512_vpternlogq(X86_ZMM0, X86_ZMM0, X86_ZMM0, 0x96)
expect(d_bytes[2] == q_bytes[2]).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/backend/avx512_vpternlog_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- AVX-512 VPTERNLOGD byte-level emit
- AVX-512 VPTERNLOGQ byte-level emit

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

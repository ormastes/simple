# X86 Vex Crypto Specification

> <details>

<!-- sdn-diagram:id=x86_vex_crypto_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=x86_vex_crypto_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

x86_vex_crypto_spec -> std
x86_vex_crypto_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=x86_vex_crypto_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 26 | 26 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# X86 Vex Crypto Specification

## Scenarios

### emit_vaesenc golden bytes

#### vaesenc(0,0,0) — all-zero regs, simplest case

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# b1=226=0xE2, b2=121=0x79, modrm=192=0xC0
val bytes = emit_vaesenc(0, 0, 0)
expect(_list_hex(bytes)).to_equal("c4e279dcc0")
```

</details>

#### vaesenc(0,1,2) — typical non-zero regs

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# b1=226=0xE2, b2=113=0x71, modrm=194=0xC2
val bytes = emit_vaesenc(0, 1, 2)
expect(_list_hex(bytes)).to_equal("c4e271dcc2")
```

</details>

#### vaesenc(1,2,3) — matches docstring example

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# b1=226=0xE2, b2=105=0x69, modrm=203=0xCB
val bytes = emit_vaesenc(1, 2, 3)
expect(_list_hex(bytes)).to_equal("c4e269dccb")
```

</details>

#### vaesenc(8,0,0) — dst>=8 clears ~R bit in byte1

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# b1=226-128=98=0x62, b2=0x79, modrm=0xC0
val bytes = emit_vaesenc(8, 0, 0)
expect(_list_hex(bytes)).to_equal("c46279dcc0")
```

</details>

#### vaesenc(0,0,9) — src2>=8 clears ~B bit in byte1, modrm rm=1

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# b1=226-32=194=0xC2, b2=0x79, modrm=192+1=193=0xC1
val bytes = emit_vaesenc(0, 0, 9)
expect(_list_hex(bytes)).to_equal("c4c279dcc1")
```

</details>

#### output length is 5 bytes (C4 + byte1 + byte2 + opcode + ModRM)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bytes = emit_vaesenc(0, 0, 0)
expect(bytes.len()).to_equal(5)
```

</details>

#### byte 0 is 0xC4 (VEX 3-byte prefix marker)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bytes = emit_vaesenc(0, 1, 2)
expect(bytes[0]).to_equal(0xC4)
```

</details>

#### opcode byte is 0xDC

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bytes = emit_vaesenc(0, 1, 2)
expect(bytes[3]).to_equal(0xDC)
```

</details>

### emit_vaesenclast golden bytes

#### vaesenclast(0,1,2) — same VEX prefix as vaesenc, opcode DD

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# b1=0xE2, b2=0x71, modrm=0xC2, opcode=0xDD
val bytes = emit_vaesenclast(0, 1, 2)
expect(_list_hex(bytes)).to_equal("c4e271ddc2")
```

</details>

#### opcode byte is 0xDD

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bytes = emit_vaesenclast(0, 1, 2)
expect(bytes[3]).to_equal(0xDD)
```

</details>

#### output length is 5 bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bytes = emit_vaesenclast(0, 0, 0)
expect(bytes.len()).to_equal(5)
```

</details>

### emit_vaesdec golden bytes

#### vaesdec(0,1,2) — same VEX prefix, opcode DE

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# b1=0xE2, b2=0x71, modrm=0xC2, opcode=0xDE
val bytes = emit_vaesdec(0, 1, 2)
expect(_list_hex(bytes)).to_equal("c4e271dec2")
```

</details>

#### opcode byte is 0xDE

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bytes = emit_vaesdec(0, 1, 2)
expect(bytes[3]).to_equal(0xDE)
```

</details>

#### output length is 5 bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bytes = emit_vaesdec(0, 0, 0)
expect(bytes.len()).to_equal(5)
```

</details>

### emit_vaesdeclast golden bytes

#### vaesdeclast(0,1,2) — same VEX prefix, opcode DF

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# b1=0xE2, b2=0x71, modrm=0xC2, opcode=0xDF
val bytes = emit_vaesdeclast(0, 1, 2)
expect(_list_hex(bytes)).to_equal("c4e271dfc2")
```

</details>

#### opcode byte is 0xDF

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bytes = emit_vaesdeclast(0, 1, 2)
expect(bytes[3]).to_equal(0xDF)
```

</details>

#### output length is 5 bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bytes = emit_vaesdeclast(0, 0, 0)
expect(bytes.len()).to_equal(5)
```

</details>

### emit_vpclmulqdq golden bytes

#### vpclmulqdq(0,1,2,0x00) — LowxLow

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# b1_0f3a(0,2)=227=0xE3, b2(1)=113=0x71, modrm=194=0xC2, imm8=0x00
val bytes = emit_vpclmulqdq(0, 1, 2, 0x00)
expect(_list_hex(bytes)).to_equal("c4e37144c200")
```

</details>

#### vpclmulqdq(0,1,2,0x11) — HighxHigh

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# same prefix, imm8=0x11
val bytes = emit_vpclmulqdq(0, 1, 2, 0x11)
expect(_list_hex(bytes)).to_equal("c4e37144c211")
```

</details>

#### output length is 6 bytes (C4 + byte1 + byte2 + opcode + ModRM + imm8)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bytes = emit_vpclmulqdq(0, 1, 2, 0x00)
expect(bytes.len()).to_equal(6)
```

</details>

#### byte 0 is 0xC4 (VEX 3-byte prefix)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bytes = emit_vpclmulqdq(0, 1, 2, 0x00)
expect(bytes[0]).to_equal(0xC4)
```

</details>

#### opcode byte is 0x44

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bytes = emit_vpclmulqdq(0, 1, 2, 0x00)
expect(bytes[3]).to_equal(0x44)
```

</details>

#### imm8 is the last byte

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bytes = emit_vpclmulqdq(0, 1, 2, 0x11)
expect(bytes[5]).to_equal(0x11)
```

</details>

#### byte1 uses 0F3A map (mmmmm=3) — differs from AES byte1 by 1

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# AES vaesenc(0,1,2): byte1=0xE2; VPCLMULQDQ(0,1,2,...): byte1=0xE3
val aes_bytes = emit_vaesenc(0, 1, 2)
val pclmul_bytes = emit_vpclmulqdq(0, 1, 2, 0x00)
expect(pclmul_bytes[1]).to_equal(aes_bytes[1] + 1)
```

</details>

### VEX vs legacy AES encoding

#### VEX form (emit_vaesenc) starts with 0xC4, legacy (emit_aesenc) starts with 0x66

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val vex_bytes = emit_vaesenc(0, 0, 0)
val leg_bytes = emit_aesenc(0, 0)
expect(vex_bytes[0]).to_equal(0xC4)
expect(leg_bytes[0]).to_equal(0x66)
```

</details>

#### VEX byte1 is 0xE2 (map+extension); legacy byte1 is 0x0F (escape)

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val vex_bytes = emit_vaesenc(0, 0, 0)
val leg_bytes = emit_aesenc(0, 0)
expect(vex_bytes[1]).to_equal(0xE2)
expect(leg_bytes[1]).to_equal(0x0F)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/backend/x86_vex_crypto_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- emit_vaesenc golden bytes
- emit_vaesenclast golden bytes
- emit_vaesdec golden bytes
- emit_vaesdeclast golden bytes
- emit_vpclmulqdq golden bytes
- VEX vs legacy AES encoding

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 26 |
| Active scenarios | 26 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

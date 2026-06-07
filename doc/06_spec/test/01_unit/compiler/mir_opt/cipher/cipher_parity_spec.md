# Cipher Parity Specification

> <details>

<!-- sdn-diagram:id=cipher_parity_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=cipher_parity_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

cipher_parity_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=cipher_parity_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 12 | 12 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Cipher Parity Specification

## Scenarios

### Cipher parity — function count preserved

#### AES round software path (no caps) preserves function count

<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m    = make_call_module(SYM_AES_ROUND)
val caps = make_x86_caps_none()
val out  = run_pattern_idiom_pass_x86(m, caps, false)
expect(out.functions.keys().len()).to_equal(m.functions.keys().len())
```

</details>

#### AES round hardware path (full caps) preserves function count

<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m    = make_call_module(SYM_AES_ROUND)
val caps = make_x86_caps_full()
val out  = run_pattern_idiom_pass_x86(m, caps, false)
expect(out.functions.keys().len()).to_equal(m.functions.keys().len())
```

</details>

#### SHA256 software path preserves function count

<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m    = make_call_module(SYM_SHA256_COMPRESS)
val caps = make_x86_caps_none()
val out  = run_pattern_idiom_pass_x86(m, caps, false)
expect(out.functions.keys().len()).to_equal(m.functions.keys().len())
```

</details>

#### SHA256 hardware path preserves function count

<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m    = make_call_module(SYM_SHA256_COMPRESS)
val caps = make_x86_caps_full()
val out  = run_pattern_idiom_pass_x86(m, caps, false)
expect(out.functions.keys().len()).to_equal(m.functions.keys().len())
```

</details>

### Cipher parity — instruction count preserved

#### AES rewrite keeps same number of instructions per block

<details>
<summary>Executable SPipe</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m    = make_call_module(SYM_AES_ROUND)
val caps = make_x86_caps_full()
val out  = run_pattern_idiom_pass_x86(m, caps, false)
val sym  = out.functions.keys()[0]
val func = out.functions[sym]
expect(func.blocks[0].instructions.len()).to_equal(1)
```

</details>

#### SHA256 rewrite keeps same number of instructions per block

<details>
<summary>Executable SPipe</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m    = make_call_module(SYM_SHA256_COMPRESS)
val caps = make_x86_caps_full()
val out  = run_pattern_idiom_pass_x86(m, caps, false)
val sym  = out.functions.keys()[0]
val func = out.functions[sym]
expect(func.blocks[0].instructions.len()).to_equal(1)
```

</details>

#### CRC32 rewrite keeps same number of instructions per block

<details>
<summary>Executable SPipe</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m    = make_call_module(SYM_CRC32_UPDATE_BYTE)
val caps = make_x86_caps_full()
val out  = run_pattern_idiom_pass_x86(m, caps, false)
val sym  = out.functions.keys()[0]
val func = out.functions[sym]
expect(func.blocks[0].instructions.len()).to_equal(1)
```

</details>

### Cipher parity — multi-call blocks

#### block with 4 AES callees: all 4 rewritten to Intrinsic when has_aes=true

<details>
<summary>Executable SPipe</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val callees = [SYM_AES_ROUND, SYM_AES_ROUND_LAST, SYM_AES_INV_ROUND, SYM_AES_INV_ROUND_LAST]
val m    = make_multi_call_module(callees)
val caps = make_x86_caps_full()
val out  = run_pattern_idiom_pass_x86(m, caps, false)
val sym  = out.functions.keys()[0]
val func = out.functions[sym]
val block = func.blocks[0]
var intrinsic_count = 0
for inst in block.instructions:
    val is_intrinsic = match inst.kind:
        case Intrinsic(dest, name, args): true
        case _: false
    if is_intrinsic:
        intrinsic_count = intrinsic_count + 1
expect(intrinsic_count).to_equal(4)
```

</details>

#### block with 4 AES callees: all 4 remain Call when has_aes=false

<details>
<summary>Executable SPipe</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val callees = [SYM_AES_ROUND, SYM_AES_ROUND_LAST, SYM_AES_INV_ROUND, SYM_AES_INV_ROUND_LAST]
val m    = make_multi_call_module(callees)
val caps = make_x86_caps_none()
val out  = run_pattern_idiom_pass_x86(m, caps, false)
val sym  = out.functions.keys()[0]
val func = out.functions[sym]
val block = func.blocks[0]
var call_count = 0
for inst in block.instructions:
    val is_call = match inst.kind:
        case Call(dest, func_op, args): true
        case _: false
    if is_call:
        call_count = call_count + 1
expect(call_count).to_equal(4)
```

</details>

#### mixed block (AES + SHA256 + CRC32 + CLMUL): correct selective rewrite with full caps

<details>
<summary>Executable SPipe</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val callees = [SYM_AES_ROUND, SYM_SHA256_COMPRESS, SYM_CRC32_UPDATE_BYTE, SYM_CLMUL_LO]
val m    = make_multi_call_module(callees)
val caps = make_x86_caps_full()
val out  = run_pattern_idiom_pass_x86(m, caps, false)
val sym  = out.functions.keys()[0]
val func = out.functions[sym]
val block = func.blocks[0]
expect(block.instructions.len()).to_equal(4)
```

</details>

### Cipher parity — all cipher symbols

#### each SYM_* constant with full caps produces Intrinsic

<details>
<summary>Executable SPipe</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val all_syms = [
    SYM_AES_ROUND, SYM_AES_ROUND_LAST,
    SYM_AES_INV_ROUND, SYM_AES_INV_ROUND_LAST,
    SYM_SHA256_COMPRESS,
    SYM_CRC32_UPDATE_BYTE, SYM_CRC32_UPDATE_U32, SYM_CRC32_UPDATE_U64,
    SYM_OS_CRC32_UPDATE_BYTE, SYM_OS_CRC32_UPDATE_U32, SYM_OS_CRC32_UPDATE_U64,
    SYM_CLMUL_LO, SYM_CLMUL_HI
]
val caps = make_x86_caps_full()
var all_intrinsic = true
for sym in all_syms:
    val m   = make_call_module(sym)
    val out = run_pattern_idiom_pass_x86(m, caps, false)
    val fsym = out.functions.keys()[0]
    val func = out.functions[fsym]
    val inst = func.blocks[0].instructions[0]
    val is_intrinsic = match inst.kind:
        case Intrinsic(dest, name, args): true
        case _: false
    if !is_intrinsic:
        all_intrinsic = false
expect(all_intrinsic).to_equal(true)
```

</details>

#### each SYM_* constant with no caps stays Call

<details>
<summary>Executable SPipe</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val all_syms = [
    SYM_AES_ROUND, SYM_AES_ROUND_LAST,
    SYM_AES_INV_ROUND, SYM_AES_INV_ROUND_LAST,
    SYM_SHA256_COMPRESS,
    SYM_CRC32_UPDATE_BYTE, SYM_CRC32_UPDATE_U32, SYM_CRC32_UPDATE_U64,
    SYM_OS_CRC32_UPDATE_BYTE, SYM_OS_CRC32_UPDATE_U32, SYM_OS_CRC32_UPDATE_U64,
    SYM_CLMUL_LO, SYM_CLMUL_HI
]
val caps = make_x86_caps_none()
var all_call = true
for sym in all_syms:
    val m   = make_call_module(sym)
    val out = run_pattern_idiom_pass_x86(m, caps, false)
    val fsym = out.functions.keys()[0]
    val func = out.functions[fsym]
    val inst = func.blocks[0].instructions[0]
    val is_call = match inst.kind:
        case Call(dest, func_op, args): true
        case _: false
    if !is_call:
        all_call = false
expect(all_call).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/mir_opt/cipher/cipher_parity_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Cipher parity — function count preserved
- Cipher parity — instruction count preserved
- Cipher parity — multi-call blocks
- Cipher parity — all cipher symbols

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 12 |
| Active scenarios | 12 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

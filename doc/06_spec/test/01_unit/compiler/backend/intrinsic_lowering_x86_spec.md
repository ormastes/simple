# Intrinsic Lowering X86 Specification

> 1. var r = lower cipher intrinsic x86

<!-- sdn-diagram:id=intrinsic_lowering_x86_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=intrinsic_lowering_x86_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

intrinsic_lowering_x86_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=intrinsic_lowering_x86_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 29 | 29 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Intrinsic Lowering X86 Specification

## Scenarios

### lower_cipher_intrinsic_x86 — AES-NI lowering when has_aes

#### crypto_aes_round emits a non-empty byte sequence

1. var r = lower cipher intrinsic x86
   - Expected: r.lowered is true
   - Expected: r.bytes.len() > 0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var r = lower_cipher_intrinsic_x86("crypto_aes_round", [0, 0], caps_aes_only())
expect(r.lowered).to_equal(true)
expect(r.bytes.len() > 0).to_equal(true)
```

</details>

#### crypto_aes_round_last lowers to non-empty bytes

1. var r = lower cipher intrinsic x86
   - Expected: r.lowered is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var r = lower_cipher_intrinsic_x86("crypto_aes_round_last", [0, 0], caps_aes_only())
expect(r.lowered).to_equal(true)
```

</details>

#### crypto_aes_inv_round lowers

1. var r = lower cipher intrinsic x86
   - Expected: r.lowered is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var r = lower_cipher_intrinsic_x86("crypto_aes_inv_round", [0, 0], caps_aes_only())
expect(r.lowered).to_equal(true)
```

</details>

#### crypto_aes_imc lowers

1. var r = lower cipher intrinsic x86
   - Expected: r.lowered is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var r = lower_cipher_intrinsic_x86("crypto_aes_imc", [0, 0], caps_aes_only())
expect(r.lowered).to_equal(true)
```

</details>

#### crypto_aes_keygen_assist lowers with rcon arg

1. var r = lower cipher intrinsic x86
   - Expected: r.lowered is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var r = lower_cipher_intrinsic_x86("crypto_aes_keygen_assist", [0, 0, 16], caps_aes_only())
expect(r.lowered).to_equal(true)
```

</details>

### lower_cipher_intrinsic_x86 — bare X86Caps refuses cipher idioms

#### AES round on bare caps returns lowered=false, reason='no-cap'

1. var r = lower cipher intrinsic x86
   - Expected: r.lowered is false
   - Expected: r.reason equals `no-cap`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var r = lower_cipher_intrinsic_x86("crypto_aes_round", [0, 0], caps_bare())
expect(r.lowered).to_equal(false)
expect(r.reason).to_equal("no-cap")
```

</details>

#### SHA256 rounds2 on bare caps refuses

1. var r = lower cipher intrinsic x86
   - Expected: r.lowered is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var r = lower_cipher_intrinsic_x86("crypto_sha256_rounds2", [0, 0], caps_bare())
expect(r.lowered).to_equal(false)
```

</details>

#### CRC32_U8 on bare caps refuses

1. var r = lower cipher intrinsic x86
   - Expected: r.lowered is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var r = lower_cipher_intrinsic_x86("crc32_u8", [0, 0], caps_bare())
expect(r.lowered).to_equal(false)
```

</details>

#### CLMUL_LO on bare caps refuses

1. var r = lower cipher intrinsic x86
   - Expected: r.lowered is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var r = lower_cipher_intrinsic_x86("clmul_lo", [0, 0], caps_bare())
expect(r.lowered).to_equal(false)
```

</details>

### lower_cipher_intrinsic_x86 — unknown name handling

#### unrecognised intrinsic returns lowered=false, reason='unknown'

1. var r = lower cipher intrinsic x86
   - Expected: r.lowered is false
   - Expected: r.reason equals `unknown`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var r = lower_cipher_intrinsic_x86("not_a_real_intrinsic", [0, 0], caps_full_v3())
expect(r.lowered).to_equal(false)
expect(r.reason).to_equal("unknown")
```

</details>

#### empty name returns unknown

1. var r = lower cipher intrinsic x86
   - Expected: r.lowered is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var r = lower_cipher_intrinsic_x86("", [], caps_full_v3())
expect(r.lowered).to_equal(false)
```

</details>

### lower_cipher_intrinsic_x86 — SHA / CRC32 / CLMUL on full caps

#### crypto_sha256_rounds2 lowers when has_sha_ni

1. var r = lower cipher intrinsic x86
   - Expected: r.lowered is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Arity is 3 per intrinsics.spl: [a_state, b_state, w_k] (third operand
# is the implicit XMM0 hardware operand on x86, not encoded in bytes).
var r = lower_cipher_intrinsic_x86("crypto_sha256_rounds2", [0, 0, 0], caps_full_v3())
expect(r.lowered).to_equal(true)
```

</details>

#### crc32_u8 lowers when has_sse42

1. var r = lower cipher intrinsic x86
   - Expected: r.lowered is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var r = lower_cipher_intrinsic_x86("crc32_u8", [0, 0], caps_full_v3())
expect(r.lowered).to_equal(true)
```

</details>

#### crc32_u64 lowers when has_sse42

1. var r = lower cipher intrinsic x86
   - Expected: r.lowered is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var r = lower_cipher_intrinsic_x86("crc32_u64", [0, 0], caps_full_v3())
expect(r.lowered).to_equal(true)
```

</details>

#### clmul_lo lowers when has_pclmul

1. var r = lower cipher intrinsic x86
   - Expected: r.lowered is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var r = lower_cipher_intrinsic_x86("clmul_lo", [0, 0], caps_full_v3())
expect(r.lowered).to_equal(true)
```

</details>

#### clmul_hi lowers when has_pclmul

1. var r = lower cipher intrinsic x86
   - Expected: r.lowered is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var r = lower_cipher_intrinsic_x86("clmul_hi", [0, 0], caps_full_v3())
expect(r.lowered).to_equal(true)
```

</details>

### lower_cipher_intrinsic_x86 — portable bit/matrix scaffolding

#### bit_rotate_left lowers with explicit dst/src/count contract

1. var r = lower cipher intrinsic x86
   - Expected: r.lowered is true
   - Expected: r.reason equals ``
   - Expected: r.bytes equals `[0x48, 0x89, 0xD1, 0x48, 0xC1, 0xC1, 0x08]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var r = lower_cipher_intrinsic_x86("bit_rotate_left", [1, 2, 8], caps_full_v3())
expect(r.lowered).to_equal(true)
expect(r.reason).to_equal("")
expect(r.bytes).to_equal([0x48, 0x89, 0xD1, 0x48, 0xC1, 0xC1, 0x08])
```

</details>

#### bit_rotate_right lowers with explicit dst/src/count contract

1. var r = lower cipher intrinsic x86
   - Expected: r.lowered is true
   - Expected: r.reason equals ``
   - Expected: r.bytes equals `[0x48, 0x89, 0xD1, 0x48, 0xC1, 0xC9, 0x08]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var r = lower_cipher_intrinsic_x86("bit_rotate_right", [1, 2, 8], caps_full_v3())
expect(r.lowered).to_equal(true)
expect(r.reason).to_equal("")
expect(r.bytes).to_equal([0x48, 0x89, 0xD1, 0x48, 0xC1, 0xC9, 0x08])
```

</details>

#### bit_rotate_left with 2 args returns bad-arity

1. var r = lower cipher intrinsic x86
   - Expected: r.lowered is false
   - Expected: r.reason equals `bad-arity`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var r = lower_cipher_intrinsic_x86("bit_rotate_left", [1, 2], caps_full_v3())
expect(r.lowered).to_equal(false)
expect(r.reason).to_equal("bad-arity")
```

</details>

#### bit_rotate_right on bare caps returns no-cap

1. var r = lower cipher intrinsic x86
   - Expected: r.lowered is false
   - Expected: r.reason equals `no-cap`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var r = lower_cipher_intrinsic_x86("bit_rotate_right", [1, 2, 8], caps_bare())
expect(r.lowered).to_equal(false)
expect(r.reason).to_equal("no-cap")
```

</details>

#### bit_bswap lowers even on bare caps because x86_64 baseline supports bswap

1. var r = lower cipher intrinsic x86
   - Expected: r.lowered is true
   - Expected: r.bytes equals `[0x48, 0x0f, 0xc8]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var r = lower_cipher_intrinsic_x86("bit_bswap", [0], caps_bare())
expect(r.lowered).to_equal(true)
expect(r.bytes).to_equal([0x48, 0x0f, 0xc8])
```

</details>

#### bit_popcount lowers on capable caps

1. var r = lower cipher intrinsic x86
   - Expected: r.lowered is true
   - Expected: r.reason equals ``
   - Expected: r.bytes equals `[0xf3, 0x48, 0x0f, 0xb8, 0xc1]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var r = lower_cipher_intrinsic_x86("bit_popcount", [0, 1], caps_full_v3())
expect(r.lowered).to_equal(true)
expect(r.reason).to_equal("")
expect(r.bytes).to_equal([0xf3, 0x48, 0x0f, 0xb8, 0xc1])
```

</details>

#### bit_clz lowers to LZCNT on caps with bmi1

1. var r = lower cipher intrinsic x86
   - Expected: r.lowered is true
   - Expected: r.reason equals ``
   - Expected: r.bytes equals `[0xf3, 0x48, 0x0f, 0xbd, 0xc1]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var r = lower_cipher_intrinsic_x86("bit_clz", [0, 1], caps_full_v3())
expect(r.lowered).to_equal(true)
expect(r.reason).to_equal("")
expect(r.bytes).to_equal([0xf3, 0x48, 0x0f, 0xbd, 0xc1])
```

</details>

#### bit_clz returns no-cap on bare caps without bmi1

1. var r = lower cipher intrinsic x86
   - Expected: r.lowered is false
   - Expected: r.reason equals `no-cap`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var r = lower_cipher_intrinsic_x86("bit_clz", [0, 1], caps_bare())
expect(r.lowered).to_equal(false)
expect(r.reason).to_equal("no-cap")
```

</details>

#### bit_ctz lowers to TZCNT on caps with bmi1

1. var r = lower cipher intrinsic x86
   - Expected: r.lowered is true
   - Expected: r.reason equals ``
   - Expected: r.bytes equals `[0xf3, 0x48, 0x0f, 0xbc, 0xc1]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var r = lower_cipher_intrinsic_x86("bit_ctz", [0, 1], caps_full_v3())
expect(r.lowered).to_equal(true)
expect(r.reason).to_equal("")
expect(r.bytes).to_equal([0xf3, 0x48, 0x0f, 0xbc, 0xc1])
```

</details>

#### bit_ctz returns no-cap on bare caps without bmi1

1. var r = lower cipher intrinsic x86
   - Expected: r.lowered is false
   - Expected: r.reason equals `no-cap`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var r = lower_cipher_intrinsic_x86("bit_ctz", [0, 1], caps_bare())
expect(r.lowered).to_equal(false)
expect(r.reason).to_equal("no-cap")
```

</details>

#### bit_parity lowers to POPCNT+AND on capable caps

1. var r = lower cipher intrinsic x86
   - Expected: r.lowered is true
   - Expected: r.reason equals ``
   - Expected: r.bytes equals `[0xf3, 0x48, 0x0f, 0xb8, 0xc1, 0x48, 0x83, 0xe0, 0x01]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var r = lower_cipher_intrinsic_x86("bit_parity", [0, 1], caps_full_v3())
expect(r.lowered).to_equal(true)
expect(r.reason).to_equal("")
expect(r.bytes).to_equal([0xf3, 0x48, 0x0f, 0xb8, 0xc1, 0x48, 0x83, 0xe0, 0x01])
```

</details>

#### bit_parity returns no-cap on bare caps without popcnt

1. var r = lower cipher intrinsic x86
   - Expected: r.lowered is false
   - Expected: r.reason equals `no-cap`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var r = lower_cipher_intrinsic_x86("bit_parity", [0, 1], caps_bare())
expect(r.lowered).to_equal(false)
expect(r.reason).to_equal("no-cap")
```

</details>

<details>
<summary>Advanced: matrix_dot is recognised and returns unimplemented on capable caps</summary>

#### matrix_dot is recognised and returns unimplemented on capable caps

1. var r = lower cipher intrinsic x86
   - Expected: r.lowered is false
   - Expected: r.reason equals `unimplemented`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var r = lower_cipher_intrinsic_x86("matrix_dot", [0, 0, 0], caps_full_v3())
expect(r.lowered).to_equal(false)
expect(r.reason).to_equal("unimplemented")
```

</details>


</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/backend/intrinsic_lowering_x86_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- lower_cipher_intrinsic_x86 — AES-NI lowering when has_aes
- lower_cipher_intrinsic_x86 — bare X86Caps refuses cipher idioms
- lower_cipher_intrinsic_x86 — unknown name handling
- lower_cipher_intrinsic_x86 — SHA / CRC32 / CLMUL on full caps
- lower_cipher_intrinsic_x86 — portable bit/matrix scaffolding

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 29 |
| Active scenarios | 29 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

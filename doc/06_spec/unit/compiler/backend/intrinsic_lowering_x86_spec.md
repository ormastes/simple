# Intrinsic Lowering X86 Specification

> Tests covering lower_cipher_intrinsic_x86 — AES-NI lowering when has_aes, lower_cipher_intrinsic_x86 — bare X86Caps refuses cipher idioms, lower_cipher_intrinsic_x86 — unknown name handling, lower_cipher_intrinsic_x86 — SHA / CRC32 / CLMUL on full caps, lower_cipher_intrinsic_x86 — portable bit/matrix scaffolding.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 29 | 29 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Intrinsic Lowering X86 Specification

## Scenarios

### lower_cipher_intrinsic_x86 — AES-NI lowering when has_aes

#### crypto_aes_round emits a non-empty byte sequence

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- crypto_aes_round emits a non-empty byte sequence
   - Expected: r.lowered is true
   - Expected: r.bytes.len() > 0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("crypto_aes_round emits a non-empty byte sequence")
var r = lower_cipher_intrinsic_x86("crypto_aes_round", [0, 0], caps_aes_only())
expect(r.lowered).to_equal(true)
expect(r.bytes.len() > 0).to_equal(true)
```

</details>

#### crypto_aes_round_last lowers to non-empty bytes

- crypto_aes_round_last lowers to non-empty bytes
   - Expected: r.lowered is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("crypto_aes_round_last lowers to non-empty bytes")
var r = lower_cipher_intrinsic_x86("crypto_aes_round_last", [0, 0], caps_aes_only())
expect(r.lowered).to_equal(true)
```

</details>

#### crypto_aes_inv_round lowers

- crypto_aes_inv_round lowers
   - Expected: r.lowered is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("crypto_aes_inv_round lowers")
var r = lower_cipher_intrinsic_x86("crypto_aes_inv_round", [0, 0], caps_aes_only())
expect(r.lowered).to_equal(true)
```

</details>

#### crypto_aes_imc lowers

- crypto_aes_imc lowers
   - Expected: r.lowered is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("crypto_aes_imc lowers")
var r = lower_cipher_intrinsic_x86("crypto_aes_imc", [0, 0], caps_aes_only())
expect(r.lowered).to_equal(true)
```

</details>

#### crypto_aes_keygen_assist lowers with rcon arg

- crypto_aes_keygen_assist lowers with rcon arg
   - Expected: r.lowered is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("crypto_aes_keygen_assist lowers with rcon arg")
var r = lower_cipher_intrinsic_x86("crypto_aes_keygen_assist", [0, 0, 16], caps_aes_only())
expect(r.lowered).to_equal(true)
```

</details>

### lower_cipher_intrinsic_x86 — bare X86Caps refuses cipher idioms

#### AES round on bare caps returns lowered=false, reason='no-cap'

- AES round on bare caps returns lowered=false, reason='no-cap'
   - Expected: r.lowered is false
   - Expected: r.reason equals `no-cap`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AES round on bare caps returns lowered=false, reason='no-cap'")
var r = lower_cipher_intrinsic_x86("crypto_aes_round", [0, 0], caps_bare())
expect(r.lowered).to_equal(false)
expect(r.reason).to_equal("no-cap")
```

</details>

#### SHA256 rounds2 on bare caps refuses

- SHA256 rounds2 on bare caps refuses
   - Expected: r.lowered is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("SHA256 rounds2 on bare caps refuses")
var r = lower_cipher_intrinsic_x86("crypto_sha256_rounds2", [0, 0], caps_bare())
expect(r.lowered).to_equal(false)
```

</details>

#### CRC32_U8 on bare caps refuses

- CRC32_U8 on bare caps refuses
   - Expected: r.lowered is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("CRC32_U8 on bare caps refuses")
var r = lower_cipher_intrinsic_x86("crc32_u8", [0, 0], caps_bare())
expect(r.lowered).to_equal(false)
```

</details>

#### CLMUL_LO on bare caps refuses

- CLMUL_LO on bare caps refuses
   - Expected: r.lowered is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("CLMUL_LO on bare caps refuses")
var r = lower_cipher_intrinsic_x86("clmul_lo", [0, 0], caps_bare())
expect(r.lowered).to_equal(false)
```

</details>

### lower_cipher_intrinsic_x86 — unknown name handling

#### unrecognised intrinsic returns lowered=false, reason='unknown'

- unrecognised intrinsic returns lowered=false, reason='unknown'
   - Expected: r.lowered is false
   - Expected: r.reason equals `unknown`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("unrecognised intrinsic returns lowered=false, reason='unknown'")
var r = lower_cipher_intrinsic_x86("not_a_real_intrinsic", [0, 0], caps_full_v3())
expect(r.lowered).to_equal(false)
expect(r.reason).to_equal("unknown")
```

</details>

#### empty name returns unknown

- empty name returns unknown
   - Expected: r.lowered is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("empty name returns unknown")
var r = lower_cipher_intrinsic_x86("", [], caps_full_v3())
expect(r.lowered).to_equal(false)
```

</details>

### lower_cipher_intrinsic_x86 — SHA / CRC32 / CLMUL on full caps

#### crypto_sha256_rounds2 lowers when has_sha_ni

- crypto_sha256_rounds2 lowers when has_sha_ni
   - Expected: r.lowered is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("crypto_sha256_rounds2 lowers when has_sha_ni")
# Arity is 3 per intrinsics.spl: [a_state, b_state, w_k] (third operand
# is the implicit XMM0 hardware operand on x86, not encoded in bytes).
var r = lower_cipher_intrinsic_x86("crypto_sha256_rounds2", [0, 0, 0], caps_full_v3())
expect(r.lowered).to_equal(true)
```

</details>

#### crc32_u8 lowers when has_sse42

- crc32_u8 lowers when has_sse42
   - Expected: r.lowered is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("crc32_u8 lowers when has_sse42")
var r = lower_cipher_intrinsic_x86("crc32_u8", [0, 0], caps_full_v3())
expect(r.lowered).to_equal(true)
```

</details>

#### crc32_u64 lowers when has_sse42

- crc32_u64 lowers when has_sse42
   - Expected: r.lowered is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("crc32_u64 lowers when has_sse42")
var r = lower_cipher_intrinsic_x86("crc32_u64", [0, 0], caps_full_v3())
expect(r.lowered).to_equal(true)
```

</details>

#### clmul_lo lowers when has_pclmul

- clmul_lo lowers when has_pclmul
   - Expected: r.lowered is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("clmul_lo lowers when has_pclmul")
var r = lower_cipher_intrinsic_x86("clmul_lo", [0, 0], caps_full_v3())
expect(r.lowered).to_equal(true)
```

</details>

#### clmul_hi lowers when has_pclmul

- clmul_hi lowers when has_pclmul
   - Expected: r.lowered is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("clmul_hi lowers when has_pclmul")
var r = lower_cipher_intrinsic_x86("clmul_hi", [0, 0], caps_full_v3())
expect(r.lowered).to_equal(true)
```

</details>

### lower_cipher_intrinsic_x86 — portable bit/matrix scaffolding

#### bit_rotate_left lowers with explicit dst/src/count contract

- bit_rotate_left lowers with explicit dst/src/count contract
   - Expected: r.lowered is true
   - Expected: r.reason equals ``
   - Expected: r.bytes equals `[0x48, 0x89, 0xD1, 0x48, 0xC1, 0xC1, 0x08]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("bit_rotate_left lowers with explicit dst/src/count contract")
var r = lower_cipher_intrinsic_x86("bit_rotate_left", [1, 2, 8], caps_full_v3())
expect(r.lowered).to_equal(true)
expect(r.reason).to_equal("")
expect(r.bytes).to_equal([0x48, 0x89, 0xD1, 0x48, 0xC1, 0xC1, 0x08])
```

</details>

#### bit_rotate_right lowers with explicit dst/src/count contract

- bit_rotate_right lowers with explicit dst/src/count contract
   - Expected: r.lowered is true
   - Expected: r.reason equals ``
   - Expected: r.bytes equals `[0x48, 0x89, 0xD1, 0x48, 0xC1, 0xC9, 0x08]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("bit_rotate_right lowers with explicit dst/src/count contract")
var r = lower_cipher_intrinsic_x86("bit_rotate_right", [1, 2, 8], caps_full_v3())
expect(r.lowered).to_equal(true)
expect(r.reason).to_equal("")
expect(r.bytes).to_equal([0x48, 0x89, 0xD1, 0x48, 0xC1, 0xC9, 0x08])
```

</details>

#### bit_rotate_left with 2 args returns bad-arity

- bit_rotate_left with 2 args returns bad-arity
   - Expected: r.lowered is false
   - Expected: r.reason equals `bad-arity`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("bit_rotate_left with 2 args returns bad-arity")
var r = lower_cipher_intrinsic_x86("bit_rotate_left", [1, 2], caps_full_v3())
expect(r.lowered).to_equal(false)
expect(r.reason).to_equal("bad-arity")
```

</details>

#### bit_rotate_right on bare caps returns no-cap

- bit_rotate_right on bare caps returns no-cap
   - Expected: r.lowered is false
   - Expected: r.reason equals `no-cap`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("bit_rotate_right on bare caps returns no-cap")
var r = lower_cipher_intrinsic_x86("bit_rotate_right", [1, 2, 8], caps_bare())
expect(r.lowered).to_equal(false)
expect(r.reason).to_equal("no-cap")
```

</details>

#### bit_bswap lowers even on bare caps because x86_64 baseline supports bswap

- bit_bswap lowers even on bare caps because x86_64 baseline supports bswap
   - Expected: r.lowered is true
   - Expected: r.bytes equals `[0x48, 0x0f, 0xc8]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("bit_bswap lowers even on bare caps because x86_64 baseline supports bswap")
var r = lower_cipher_intrinsic_x86("bit_bswap", [0], caps_bare())
expect(r.lowered).to_equal(true)
expect(r.bytes).to_equal([0x48, 0x0f, 0xc8])
```

</details>

#### bit_popcount lowers on capable caps

- bit_popcount lowers on capable caps
   - Expected: r.lowered is true
   - Expected: r.reason equals ``
   - Expected: r.bytes equals `[0xf3, 0x48, 0x0f, 0xb8, 0xc1]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("bit_popcount lowers on capable caps")
var r = lower_cipher_intrinsic_x86("bit_popcount", [0, 1], caps_full_v3())
expect(r.lowered).to_equal(true)
expect(r.reason).to_equal("")
expect(r.bytes).to_equal([0xf3, 0x48, 0x0f, 0xb8, 0xc1])
```

</details>

#### bit_clz lowers to LZCNT on caps with bmi1

- bit_clz lowers to LZCNT on caps with bmi1
   - Expected: r.lowered is true
   - Expected: r.reason equals ``
   - Expected: r.bytes equals `[0xf3, 0x48, 0x0f, 0xbd, 0xc1]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("bit_clz lowers to LZCNT on caps with bmi1")
var r = lower_cipher_intrinsic_x86("bit_clz", [0, 1], caps_full_v3())
expect(r.lowered).to_equal(true)
expect(r.reason).to_equal("")
expect(r.bytes).to_equal([0xf3, 0x48, 0x0f, 0xbd, 0xc1])
```

</details>

#### bit_clz returns no-cap on bare caps without bmi1

- bit_clz returns no-cap on bare caps without bmi1
   - Expected: r.lowered is false
   - Expected: r.reason equals `no-cap`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("bit_clz returns no-cap on bare caps without bmi1")
var r = lower_cipher_intrinsic_x86("bit_clz", [0, 1], caps_bare())
expect(r.lowered).to_equal(false)
expect(r.reason).to_equal("no-cap")
```

</details>

#### bit_ctz lowers to TZCNT on caps with bmi1

- bit_ctz lowers to TZCNT on caps with bmi1
   - Expected: r.lowered is true
   - Expected: r.reason equals ``
   - Expected: r.bytes equals `[0xf3, 0x48, 0x0f, 0xbc, 0xc1]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("bit_ctz lowers to TZCNT on caps with bmi1")
var r = lower_cipher_intrinsic_x86("bit_ctz", [0, 1], caps_full_v3())
expect(r.lowered).to_equal(true)
expect(r.reason).to_equal("")
expect(r.bytes).to_equal([0xf3, 0x48, 0x0f, 0xbc, 0xc1])
```

</details>

#### bit_ctz returns no-cap on bare caps without bmi1

- bit_ctz returns no-cap on bare caps without bmi1
   - Expected: r.lowered is false
   - Expected: r.reason equals `no-cap`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("bit_ctz returns no-cap on bare caps without bmi1")
var r = lower_cipher_intrinsic_x86("bit_ctz", [0, 1], caps_bare())
expect(r.lowered).to_equal(false)
expect(r.reason).to_equal("no-cap")
```

</details>

#### bit_parity lowers to POPCNT+AND on capable caps

- bit_parity lowers to POPCNT+AND on capable caps
   - Expected: r.lowered is true
   - Expected: r.reason equals ``
   - Expected: r.bytes equals `[0xf3, 0x48, 0x0f, 0xb8, 0xc1, 0x48, 0x83, 0xe0, 0x01]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("bit_parity lowers to POPCNT+AND on capable caps")
var r = lower_cipher_intrinsic_x86("bit_parity", [0, 1], caps_full_v3())
expect(r.lowered).to_equal(true)
expect(r.reason).to_equal("")
expect(r.bytes).to_equal([0xf3, 0x48, 0x0f, 0xb8, 0xc1, 0x48, 0x83, 0xe0, 0x01])
```

</details>

#### bit_parity returns no-cap on bare caps without popcnt

- bit_parity returns no-cap on bare caps without popcnt
   - Expected: r.lowered is false
   - Expected: r.reason equals `no-cap`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("bit_parity returns no-cap on bare caps without popcnt")
var r = lower_cipher_intrinsic_x86("bit_parity", [0, 1], caps_bare())
expect(r.lowered).to_equal(false)
expect(r.reason).to_equal("no-cap")
```

</details>

<details>
<summary>Advanced: matrix_dot is recognised and returns unimplemented on capable caps</summary>

#### matrix_dot is recognised and returns unimplemented on capable caps

- matrix_dot is recognised and returns unimplemented on capable caps
   - Expected: r.lowered is false
   - Expected: r.reason equals `unimplemented`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("matrix_dot is recognised and returns unimplemented on capable caps")
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
| Source | `test/unit/compiler/backend/intrinsic_lowering_x86_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering lower_cipher_intrinsic_x86 — AES-NI lowering when has_aes, lower_cipher_intrinsic_x86 — bare X86Caps refuses cipher idioms, lower_cipher_intrinsic_x86 — unknown name handling, lower_cipher_intrinsic_x86 — SHA / CRC32 / CLMUL on full caps, lower_cipher_intrinsic_x86 — portable bit/matrix scaffolding.
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `c76f74d1c9818ae68e54eafdfc5e1d452877e801f7445a907c9a8013062808c8`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `c76f74d1c9818ae68e54eafdfc5e1d452877e801f7445a907c9a8013062808c8`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `c76f74d1c9818ae68e54eafdfc5e1d452877e801f7445a907c9a8013062808c8`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/compiler/backend/intrinsic_lowering_x86_spec.spl
mirror: doc/06_spec/unit/compiler/backend/intrinsic_lowering_x86_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/compiler/backend/intrinsic_lowering_x86_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/compiler/backend/intrinsic_lowering_x86_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/compiler/backend/intrinsic_lowering_x86_spec.spl:48:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'crypto_aes_round emits a non-empty byte sequence' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/backend/intrinsic_lowering_x86_spec.spl:55:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'crypto_aes_round_last lowers to non-empty bytes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/backend/intrinsic_lowering_x86_spec.spl:61:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'crypto_aes_inv_round lowers' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

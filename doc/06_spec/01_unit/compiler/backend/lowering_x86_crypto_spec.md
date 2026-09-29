# lowering_x86_crypto_spec

> Purpose: Prove that x86 cipher intrinsic lowering — AES-NI.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 16 | 16 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# lowering_x86_crypto_spec

Purpose: Prove that x86 cipher intrinsic lowering — AES-NI.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/backend/lowering_x86_crypto_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Prove that x86 cipher intrinsic lowering — AES-NI.
Audience: COMP maintainers who read this spec to confirm the behavior still holds.

## Scenarios

### x86 cipher intrinsic lowering — AES-NI

#### AESENC xmm0,xmm1 (crypto_aes_round [0,1])

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- AESENC xmm0,xmm1 (crypto_aes_round [0,1])
- Verify: AESENC xmm0,xmm1 (crypto_aes_round [0,1])
   - Expected: result.lowered is true
   - Expected: result.reason equals ``
   - Expected: _list_hex(result.bytes) equals `660f38dcc1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("AESENC xmm0,xmm1 (crypto_aes_round [0,1])")
step("Verify: AESENC xmm0,xmm1 (crypto_aes_round [0,1])")
# @req: REQ-COMP-X86-CIPHER-INTRINSIC-LOWERING-AES-NI-001
val result = lower_cipher_intrinsic_x86("crypto_aes_round", [0, 1], TEST_X86_CAPS)
expect(result.lowered).to_equal(true)
expect(result.reason).to_equal("")
expect(_list_hex(result.bytes)).to_equal("660f38dcc1")
```

</details>

#### AESENC output length is 5 bytes

- AESENC output length is 5 bytes
- Verify: AESENC output length is 5 bytes
   - Expected: result.bytes.len() equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("AESENC output length is 5 bytes")
step("Verify: AESENC output length is 5 bytes")
val result = lower_cipher_intrinsic_x86("crypto_aes_round", [0, 1], TEST_X86_CAPS)
expect(result.bytes.len()).to_equal(5)
```

</details>

#### AESENCLAST xmm0,xmm1 (crypto_aes_round_last [0,1])

- AESENCLAST xmm0,xmm1 (crypto_aes_round_last [0,1])
- Verify: AESENCLAST xmm0,xmm1 (crypto_aes_round_last [0,1])
   - Expected: result.lowered is true
   - Expected: result.reason equals ``
   - Expected: _list_hex(result.bytes) equals `660f38ddc1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("AESENCLAST xmm0,xmm1 (crypto_aes_round_last [0,1])")
step("Verify: AESENCLAST xmm0,xmm1 (crypto_aes_round_last [0,1])")
val result = lower_cipher_intrinsic_x86("crypto_aes_round_last", [0, 1], TEST_X86_CAPS)
expect(result.lowered).to_equal(true)
expect(result.reason).to_equal("")
expect(_list_hex(result.bytes)).to_equal("660f38ddc1")
```

</details>

#### AESENCLAST output length is 5 bytes

- AESENCLAST output length is 5 bytes
- Verify: AESENCLAST output length is 5 bytes
   - Expected: result.bytes.len() equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("AESENCLAST output length is 5 bytes")
step("Verify: AESENCLAST output length is 5 bytes")
val result = lower_cipher_intrinsic_x86("crypto_aes_round_last", [0, 1], TEST_X86_CAPS)
expect(result.bytes.len()).to_equal(5)
```

</details>

#### AESDEC xmm2,xmm3 (crypto_aes_inv_round [2,3])

- AESDEC xmm2,xmm3 (crypto_aes_inv_round [2,3])
- Verify: AESDEC xmm2,xmm3 (crypto_aes_inv_round [2,3])
   - Expected: result.lowered is true
   - Expected: result.reason equals ``
   - Expected: _list_hex(result.bytes) equals `660f38ded3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("AESDEC xmm2,xmm3 (crypto_aes_inv_round [2,3])")
step("Verify: AESDEC xmm2,xmm3 (crypto_aes_inv_round [2,3])")
val result = lower_cipher_intrinsic_x86("crypto_aes_inv_round", [2, 3], TEST_X86_CAPS)
expect(result.lowered).to_equal(true)
expect(result.reason).to_equal("")
expect(_list_hex(result.bytes)).to_equal("660f38ded3")
```

</details>

#### AESDEC output length is 5 bytes

- AESDEC output length is 5 bytes
- Verify: AESDEC output length is 5 bytes
   - Expected: result.bytes.len() equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("AESDEC output length is 5 bytes")
step("Verify: AESDEC output length is 5 bytes")
val result = lower_cipher_intrinsic_x86("crypto_aes_inv_round", [2, 3], TEST_X86_CAPS)
expect(result.bytes.len()).to_equal(5)
```

</details>

### x86 cipher intrinsic lowering — CRC32

#### CRC32 r32,r8 (crc32_u8 [0,1])

- CRC32 r32,r8 (crc32_u8 [0,1])
- Verify: CRC32 r32,r8 (crc32_u8 [0,1])
   - Expected: result.lowered is true
   - Expected: result.reason equals ``
   - Expected: _list_hex(result.bytes) equals `f20f38f0c1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("CRC32 r32,r8 (crc32_u8 [0,1])")
step("Verify: CRC32 r32,r8 (crc32_u8 [0,1])")
val result = lower_cipher_intrinsic_x86("crc32_u8", [0, 1], TEST_X86_CAPS)
expect(result.lowered).to_equal(true)
expect(result.reason).to_equal("")
expect(_list_hex(result.bytes)).to_equal("f20f38f0c1")
```

</details>

#### CRC32 r32,r8 output length is 5 bytes

- CRC32 r32,r8 output length is 5 bytes
- Verify: CRC32 r32,r8 output length is 5 bytes
   - Expected: result.bytes.len() equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("CRC32 r32,r8 output length is 5 bytes")
step("Verify: CRC32 r32,r8 output length is 5 bytes")
val result = lower_cipher_intrinsic_x86("crc32_u8", [0, 1], TEST_X86_CAPS)
expect(result.bytes.len()).to_equal(5)
```

</details>

#### CRC32 r64,r64 with REX.W (crc32_u64 [0,0])

- CRC32 r64,r64 with REX.W (crc32_u64 [0,0])
- Verify: CRC32 r64,r64 with REX.W (crc32_u64 [0,0])
   - Expected: result.lowered is true
   - Expected: result.reason equals ``
   - Expected: _list_hex(result.bytes) equals `f2480f38f1c0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("CRC32 r64,r64 with REX.W (crc32_u64 [0,0])")
step("Verify: CRC32 r64,r64 with REX.W (crc32_u64 [0,0])")
val result = lower_cipher_intrinsic_x86("crc32_u64", [0, 0], TEST_X86_CAPS)
expect(result.lowered).to_equal(true)
expect(result.reason).to_equal("")
expect(_list_hex(result.bytes)).to_equal("f2480f38f1c0")
```

</details>

#### CRC32 r64,r64 output length is 6 bytes (REX prefix)

- CRC32 r64,r64 output length is 6 bytes (REX prefix)
- Verify: CRC32 r64,r64 output length is 6 bytes (REX prefix)
   - Expected: result.bytes.len() equals `6`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("CRC32 r64,r64 output length is 6 bytes (REX prefix)")
step("Verify: CRC32 r64,r64 output length is 6 bytes (REX prefix)")
val result = lower_cipher_intrinsic_x86("crc32_u64", [0, 0], TEST_X86_CAPS)
expect(result.bytes.len()).to_equal(6)
```

</details>

### x86 cipher intrinsic lowering — PCLMULQDQ

#### PCLMULQDQ xmm0,xmm1,0x00 (clmul_lo [0,1])

- PCLMULQDQ xmm0,xmm1,0x00 (clmul_lo [0,1])
- Verify: PCLMULQDQ xmm0,xmm1,0x00 (clmul_lo [0,1])
   - Expected: result.lowered is true
   - Expected: result.reason equals ``
   - Expected: _list_hex(result.bytes) equals `660f3a44c100`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("PCLMULQDQ xmm0,xmm1,0x00 (clmul_lo [0,1])")
step("Verify: PCLMULQDQ xmm0,xmm1,0x00 (clmul_lo [0,1])")
val result = lower_cipher_intrinsic_x86("clmul_lo", [0, 1], TEST_X86_CAPS)
expect(result.lowered).to_equal(true)
expect(result.reason).to_equal("")
expect(_list_hex(result.bytes)).to_equal("660f3a44c100")
```

</details>

#### PCLMULQDQ clmul_lo output length is 6 bytes

- PCLMULQDQ clmul_lo output length is 6 bytes
- Verify: PCLMULQDQ clmul_lo output length is 6 bytes
   - Expected: result.bytes.len() equals `6`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("PCLMULQDQ clmul_lo output length is 6 bytes")
step("Verify: PCLMULQDQ clmul_lo output length is 6 bytes")
val result = lower_cipher_intrinsic_x86("clmul_lo", [0, 1], TEST_X86_CAPS)
expect(result.bytes.len()).to_equal(6)
```

</details>

#### PCLMULQDQ xmm0,xmm1,0x11 (clmul_hi [0,1])

- PCLMULQDQ xmm0,xmm1,0x11 (clmul_hi [0,1])
- Verify: PCLMULQDQ xmm0,xmm1,0x11 (clmul_hi [0,1])
   - Expected: result.lowered is true
   - Expected: result.reason equals ``
   - Expected: _list_hex(result.bytes) equals `660f3a44c111`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("PCLMULQDQ xmm0,xmm1,0x11 (clmul_hi [0,1])")
step("Verify: PCLMULQDQ xmm0,xmm1,0x11 (clmul_hi [0,1])")
val result = lower_cipher_intrinsic_x86("clmul_hi", [0, 1], TEST_X86_CAPS)
expect(result.lowered).to_equal(true)
expect(result.reason).to_equal("")
expect(_list_hex(result.bytes)).to_equal("660f3a44c111")
```

</details>

#### PCLMULQDQ clmul_hi output length is 6 bytes

- PCLMULQDQ clmul_hi output length is 6 bytes
- Verify: PCLMULQDQ clmul_hi output length is 6 bytes
   - Expected: result.bytes.len() equals `6`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("PCLMULQDQ clmul_hi output length is 6 bytes")
step("Verify: PCLMULQDQ clmul_hi output length is 6 bytes")
val result = lower_cipher_intrinsic_x86("clmul_hi", [0, 1], TEST_X86_CAPS)
expect(result.bytes.len()).to_equal(6)
```

</details>

### x86 cipher intrinsic lowering — failure cases

#### unknown intrinsic name returns lowered=false, reason=unknown

- unknown intrinsic name returns lowered=false, reason=unknown
- Verify: unknown intrinsic name returns lowered=false, reason=unknown
   - Expected: result.lowered is false
   - Expected: result.reason equals `unknown`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("unknown intrinsic name returns lowered=false, reason=unknown")
step("Verify: unknown intrinsic name returns lowered=false, reason=unknown")
val result = lower_cipher_intrinsic_x86("sha_not_real", [0, 1], TEST_X86_CAPS)
expect(result.lowered).to_equal(false)
expect(result.reason).to_equal("unknown")
```

</details>

#### crypto_aes_round with 1 arg returns lowered=false, reason=bad-arity

- crypto_aes_round with 1 arg returns lowered=false, reason=bad-arity
- Verify: crypto_aes_round with 1 arg returns lowered=false, reason=bad-arity
   - Expected: result.lowered is false
   - Expected: result.reason equals `bad-arity`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("crypto_aes_round with 1 arg returns lowered=false, reason=bad-arity")
step("Verify: crypto_aes_round with 1 arg returns lowered=false, reason=bad-arity")
val result = lower_cipher_intrinsic_x86("crypto_aes_round", [0], TEST_X86_CAPS)
expect(result.lowered).to_equal(false)
expect(result.reason).to_equal("bad-arity")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 16 |
| Active scenarios | 16 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-COMPILER`
- `REQ-COMP-X86-CIPHER-INTRINSIC-LOWERING-AES-NI-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `1ad7d6a4431ebb7f26611d7262b1f628169144f12af582efd6fa3cb9e0a14be6`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `1ad7d6a4431ebb7f26611d7262b1f628169144f12af582efd6fa3cb9e0a14be6`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `1ad7d6a4431ebb7f26611d7262b1f628169144f12af582efd6fa3cb9e0a14be6`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/compiler/backend/lowering_x86_crypto_spec.spl
mirror: doc/06_spec/01_unit/compiler/backend/lowering_x86_crypto_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/backend/lowering_x86_crypto_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/backend/lowering_x86_crypto_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/backend/lowering_x86_crypto_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 7 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/backend/lowering_x86_crypto_spec.spl:55:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AESENC xmm0,xmm1 (crypto_aes_round [0,1])' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/backend/lowering_x86_crypto_spec.spl:65:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AESENC output length is 5 bytes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/backend/lowering_x86_crypto_spec.spl:72:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AESENCLAST xmm0,xmm1 (crypto_aes_round_last [0,1])' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

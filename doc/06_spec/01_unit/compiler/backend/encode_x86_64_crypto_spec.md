# encode_x86_64_crypto_spec

> Purpose: Prove that x86 AES-NI encoder — golden bytes.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 14 | 14 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# encode_x86_64_crypto_spec

Purpose: Prove that x86 AES-NI encoder — golden bytes.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/backend/encode_x86_64_crypto_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Prove that x86 AES-NI encoder — golden bytes.
Audience: COMP maintainers who read this spec to confirm the behavior still holds.

## Scenarios

### x86 AES-NI encoder — golden bytes

#### emit_aesenc(0,0) → [0x66, 0x0F, 0x38, 0xDC, 0xC0]

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- emit_aesenc(0,0) → [0x66, 0x0F, 0x38, 0xDC, 0xC0]
- Verify: emit_aesenc(0,0) → [0x66, 0x0F, 0x38, 0xDC, 0xC0]
   - Expected: bytes.len() equals `5`
   - Expected: bytes[0] equals `0x66`
   - Expected: bytes[1] equals `0x0F`
   - Expected: bytes[2] equals `0x38`
   - Expected: bytes[3] equals `0xDC`
   - Expected: bytes[4] equals `0xC0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("emit_aesenc(0,0) → [0x66, 0x0F, 0x38, 0xDC, 0xC0]")
step("Verify: emit_aesenc(0,0) → [0x66, 0x0F, 0x38, 0xDC, 0xC0]")
# @req: REQ-COMP-X86-AES-NI-ENCODER-GOLDEN-BYTES-001
val bytes = emit_aesenc(0, 0)
expect(bytes.len()).to_equal(5)
expect(bytes[0]).to_equal(0x66)
expect(bytes[1]).to_equal(0x0F)
expect(bytes[2]).to_equal(0x38)
expect(bytes[3]).to_equal(0xDC)
expect(bytes[4]).to_equal(0xC0)
```

</details>

#### emit_aesenc(8,0) → [0x66, 0x44, 0x0F, 0x38, 0xDC, 0xC0] (REX.R for dst>=8)

- emit_aesenc(8,0) → [0x66, 0x44, 0x0F, 0x38, 0xDC, 0xC0] (REX.R for dst>=8)
- Verify: emit_aesenc(8,0) → [0x66, 0x44, 0x0F, 0x38, 0xDC, 0xC0] (REX.R for dst>=8)
   - Expected: bytes.len() equals `6`
   - Expected: bytes[0] equals `0x66`
   - Expected: bytes[1] equals `0x44`
   - Expected: bytes[2] equals `0x0F`
   - Expected: bytes[3] equals `0x38`
   - Expected: bytes[4] equals `0xDC`
   - Expected: bytes[5] equals `0xC0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("emit_aesenc(8,0) → [0x66, 0x44, 0x0F, 0x38, 0xDC, 0xC0] (REX.R for dst>=8)")
step("Verify: emit_aesenc(8,0) → [0x66, 0x44, 0x0F, 0x38, 0xDC, 0xC0] (REX.R for dst>=8)")
val bytes = emit_aesenc(8, 0)
expect(bytes.len()).to_equal(6)
expect(bytes[0]).to_equal(0x66)
expect(bytes[1]).to_equal(0x44)
expect(bytes[2]).to_equal(0x0F)
expect(bytes[3]).to_equal(0x38)
expect(bytes[4]).to_equal(0xDC)
expect(bytes[5]).to_equal(0xC0)
```

</details>

#### emit_aesenclast(0,0) → [0x66, 0x0F, 0x38, 0xDD, 0xC0]

- emit_aesenclast(0,0) → [0x66, 0x0F, 0x38, 0xDD, 0xC0]
- Verify: emit_aesenclast(0,0) → [0x66, 0x0F, 0x38, 0xDD, 0xC0]
   - Expected: bytes.len() equals `5`
   - Expected: bytes[0] equals `0x66`
   - Expected: bytes[1] equals `0x0F`
   - Expected: bytes[2] equals `0x38`
   - Expected: bytes[3] equals `0xDD`
   - Expected: bytes[4] equals `0xC0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("emit_aesenclast(0,0) → [0x66, 0x0F, 0x38, 0xDD, 0xC0]")
step("Verify: emit_aesenclast(0,0) → [0x66, 0x0F, 0x38, 0xDD, 0xC0]")
val bytes = emit_aesenclast(0, 0)
expect(bytes.len()).to_equal(5)
expect(bytes[0]).to_equal(0x66)
expect(bytes[1]).to_equal(0x0F)
expect(bytes[2]).to_equal(0x38)
expect(bytes[3]).to_equal(0xDD)
expect(bytes[4]).to_equal(0xC0)
```

</details>

#### emit_aesdec(0,0) → [0x66, 0x0F, 0x38, 0xDE, 0xC0]

- emit_aesdec(0,0) → [0x66, 0x0F, 0x38, 0xDE, 0xC0]
- Verify: emit_aesdec(0,0) → [0x66, 0x0F, 0x38, 0xDE, 0xC0]
   - Expected: bytes.len() equals `5`
   - Expected: bytes[0] equals `0x66`
   - Expected: bytes[1] equals `0x0F`
   - Expected: bytes[2] equals `0x38`
   - Expected: bytes[3] equals `0xDE`
   - Expected: bytes[4] equals `0xC0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("emit_aesdec(0,0) → [0x66, 0x0F, 0x38, 0xDE, 0xC0]")
step("Verify: emit_aesdec(0,0) → [0x66, 0x0F, 0x38, 0xDE, 0xC0]")
val bytes = emit_aesdec(0, 0)
expect(bytes.len()).to_equal(5)
expect(bytes[0]).to_equal(0x66)
expect(bytes[1]).to_equal(0x0F)
expect(bytes[2]).to_equal(0x38)
expect(bytes[3]).to_equal(0xDE)
expect(bytes[4]).to_equal(0xC0)
```

</details>

#### emit_aesdeclast(0,0) → [0x66, 0x0F, 0x38, 0xDF, 0xC0]

- emit_aesdeclast(0,0) → [0x66, 0x0F, 0x38, 0xDF, 0xC0]
- Verify: emit_aesdeclast(0,0) → [0x66, 0x0F, 0x38, 0xDF, 0xC0]
   - Expected: bytes.len() equals `5`
   - Expected: bytes[0] equals `0x66`
   - Expected: bytes[1] equals `0x0F`
   - Expected: bytes[2] equals `0x38`
   - Expected: bytes[3] equals `0xDF`
   - Expected: bytes[4] equals `0xC0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("emit_aesdeclast(0,0) → [0x66, 0x0F, 0x38, 0xDF, 0xC0]")
step("Verify: emit_aesdeclast(0,0) → [0x66, 0x0F, 0x38, 0xDF, 0xC0]")
val bytes = emit_aesdeclast(0, 0)
expect(bytes.len()).to_equal(5)
expect(bytes[0]).to_equal(0x66)
expect(bytes[1]).to_equal(0x0F)
expect(bytes[2]).to_equal(0x38)
expect(bytes[3]).to_equal(0xDF)
expect(bytes[4]).to_equal(0xC0)
```

</details>

#### emit_aesimc(0,0) → [0x66, 0x0F, 0x38, 0xDB, 0xC0]

- emit_aesimc(0,0) → [0x66, 0x0F, 0x38, 0xDB, 0xC0]
- Verify: emit_aesimc(0,0) → [0x66, 0x0F, 0x38, 0xDB, 0xC0]
   - Expected: bytes.len() equals `5`
   - Expected: bytes[0] equals `0x66`
   - Expected: bytes[1] equals `0x0F`
   - Expected: bytes[2] equals `0x38`
   - Expected: bytes[3] equals `0xDB`
   - Expected: bytes[4] equals `0xC0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("emit_aesimc(0,0) → [0x66, 0x0F, 0x38, 0xDB, 0xC0]")
step("Verify: emit_aesimc(0,0) → [0x66, 0x0F, 0x38, 0xDB, 0xC0]")
val bytes = emit_aesimc(0, 0)
expect(bytes.len()).to_equal(5)
expect(bytes[0]).to_equal(0x66)
expect(bytes[1]).to_equal(0x0F)
expect(bytes[2]).to_equal(0x38)
expect(bytes[3]).to_equal(0xDB)
expect(bytes[4]).to_equal(0xC0)
```

</details>

#### emit_aeskeygenassist(0,0,0x10) → [0x66, 0x0F, 0x3A, 0xDF, 0xC0, 0x10]

- emit_aeskeygenassist(0,0,0x10) → [0x66, 0x0F, 0x3A, 0xDF, 0xC0, 0x10]
- Verify: emit_aeskeygenassist(0,0,0x10) → [0x66, 0x0F, 0x3A, 0xDF, 0xC0, 0x10]
   - Expected: bytes.len() equals `6`
   - Expected: bytes[0] equals `0x66`
   - Expected: bytes[1] equals `0x0F`
   - Expected: bytes[2] equals `0x3A`
   - Expected: bytes[3] equals `0xDF`
   - Expected: bytes[4] equals `0xC0`
   - Expected: bytes[5] equals `0x10`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("emit_aeskeygenassist(0,0,0x10) → [0x66, 0x0F, 0x3A, 0xDF, 0xC0, 0x10]")
step("Verify: emit_aeskeygenassist(0,0,0x10) → [0x66, 0x0F, 0x3A, 0xDF, 0xC0, 0x10]")
val bytes = emit_aeskeygenassist(0, 0, 0x10)
expect(bytes.len()).to_equal(6)
expect(bytes[0]).to_equal(0x66)
expect(bytes[1]).to_equal(0x0F)
expect(bytes[2]).to_equal(0x3A)
expect(bytes[3]).to_equal(0xDF)
expect(bytes[4]).to_equal(0xC0)
expect(bytes[5]).to_equal(0x10)
```

</details>

### x86 SHA-NI encoder — golden bytes

#### emit_sha256rnds2(0,0) → [0x0F, 0x38, 0xCB, 0xC0]

- emit_sha256rnds2(0,0) → [0x0F, 0x38, 0xCB, 0xC0]
- Verify: emit_sha256rnds2(0,0) → [0x0F, 0x38, 0xCB, 0xC0]
   - Expected: bytes.len() equals `4`
   - Expected: bytes[0] equals `0x0F`
   - Expected: bytes[1] equals `0x38`
   - Expected: bytes[2] equals `0xCB`
   - Expected: bytes[3] equals `0xC0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("emit_sha256rnds2(0,0) → [0x0F, 0x38, 0xCB, 0xC0]")
step("Verify: emit_sha256rnds2(0,0) → [0x0F, 0x38, 0xCB, 0xC0]")
val bytes = emit_sha256rnds2(0, 0)
expect(bytes.len()).to_equal(4)
expect(bytes[0]).to_equal(0x0F)
expect(bytes[1]).to_equal(0x38)
expect(bytes[2]).to_equal(0xCB)
expect(bytes[3]).to_equal(0xC0)
```

</details>

#### emit_sha256msg1(0,0) → [0x0F, 0x38, 0xCC, 0xC0]

- emit_sha256msg1(0,0) → [0x0F, 0x38, 0xCC, 0xC0]
- Verify: emit_sha256msg1(0,0) → [0x0F, 0x38, 0xCC, 0xC0]
   - Expected: bytes.len() equals `4`
   - Expected: bytes[0] equals `0x0F`
   - Expected: bytes[1] equals `0x38`
   - Expected: bytes[2] equals `0xCC`
   - Expected: bytes[3] equals `0xC0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("emit_sha256msg1(0,0) → [0x0F, 0x38, 0xCC, 0xC0]")
step("Verify: emit_sha256msg1(0,0) → [0x0F, 0x38, 0xCC, 0xC0]")
val bytes = emit_sha256msg1(0, 0)
expect(bytes.len()).to_equal(4)
expect(bytes[0]).to_equal(0x0F)
expect(bytes[1]).to_equal(0x38)
expect(bytes[2]).to_equal(0xCC)
expect(bytes[3]).to_equal(0xC0)
```

</details>

#### emit_sha256msg2(0,0) → [0x0F, 0x38, 0xCD, 0xC0]

- emit_sha256msg2(0,0) → [0x0F, 0x38, 0xCD, 0xC0]
- Verify: emit_sha256msg2(0,0) → [0x0F, 0x38, 0xCD, 0xC0]
   - Expected: bytes.len() equals `4`
   - Expected: bytes[0] equals `0x0F`
   - Expected: bytes[1] equals `0x38`
   - Expected: bytes[2] equals `0xCD`
   - Expected: bytes[3] equals `0xC0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("emit_sha256msg2(0,0) → [0x0F, 0x38, 0xCD, 0xC0]")
step("Verify: emit_sha256msg2(0,0) → [0x0F, 0x38, 0xCD, 0xC0]")
val bytes = emit_sha256msg2(0, 0)
expect(bytes.len()).to_equal(4)
expect(bytes[0]).to_equal(0x0F)
expect(bytes[1]).to_equal(0x38)
expect(bytes[2]).to_equal(0xCD)
expect(bytes[3]).to_equal(0xC0)
```

</details>

### x86 CRC32 encoder — golden bytes

#### emit_crc32_r32_r32(0,0) → [0xF2, 0x0F, 0x38, 0xF1, 0xC0]

- emit_crc32_r32_r32(0,0) → [0xF2, 0x0F, 0x38, 0xF1, 0xC0]
- Verify: emit_crc32_r32_r32(0,0) → [0xF2, 0x0F, 0x38, 0xF1, 0xC0]
   - Expected: bytes.len() equals `5`
   - Expected: bytes[0] equals `0xF2`
   - Expected: bytes[1] equals `0x0F`
   - Expected: bytes[2] equals `0x38`
   - Expected: bytes[3] equals `0xF1`
   - Expected: bytes[4] equals `0xC0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("emit_crc32_r32_r32(0,0) → [0xF2, 0x0F, 0x38, 0xF1, 0xC0]")
step("Verify: emit_crc32_r32_r32(0,0) → [0xF2, 0x0F, 0x38, 0xF1, 0xC0]")
val bytes = emit_crc32_r32_r32(0, 0)
expect(bytes.len()).to_equal(5)
expect(bytes[0]).to_equal(0xF2)
expect(bytes[1]).to_equal(0x0F)
expect(bytes[2]).to_equal(0x38)
expect(bytes[3]).to_equal(0xF1)
expect(bytes[4]).to_equal(0xC0)
```

</details>

#### emit_crc32_r64_r64(0,0) → [0xF2, 0x48, 0x0F, 0x38, 0xF1, 0xC0]

- emit_crc32_r64_r64(0,0) → [0xF2, 0x48, 0x0F, 0x38, 0xF1, 0xC0]
- Verify: emit_crc32_r64_r64(0,0) → [0xF2, 0x48, 0x0F, 0x38, 0xF1, 0xC0]
   - Expected: bytes.len() equals `6`
   - Expected: bytes[0] equals `0xF2`
   - Expected: bytes[1] equals `0x48`
   - Expected: bytes[2] equals `0x0F`
   - Expected: bytes[3] equals `0x38`
   - Expected: bytes[4] equals `0xF1`
   - Expected: bytes[5] equals `0xC0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("emit_crc32_r64_r64(0,0) → [0xF2, 0x48, 0x0F, 0x38, 0xF1, 0xC0]")
step("Verify: emit_crc32_r64_r64(0,0) → [0xF2, 0x48, 0x0F, 0x38, 0xF1, 0xC0]")
val bytes = emit_crc32_r64_r64(0, 0)
expect(bytes.len()).to_equal(6)
expect(bytes[0]).to_equal(0xF2)
expect(bytes[1]).to_equal(0x48)
expect(bytes[2]).to_equal(0x0F)
expect(bytes[3]).to_equal(0x38)
expect(bytes[4]).to_equal(0xF1)
expect(bytes[5]).to_equal(0xC0)
```

</details>

### x86 PCLMULQDQ encoder

#### emit_pclmulqdq(0,0,0x00) → [0x66, 0x0F, 0x3A, 0x44, 0xC0, 0x00]

- emit_pclmulqdq(0,0,0x00) → [0x66, 0x0F, 0x3A, 0x44, 0xC0, 0x00]
- Verify: emit_pclmulqdq(0,0,0x00) → [0x66, 0x0F, 0x3A, 0x44, 0xC0, 0x00]
   - Expected: bytes.len() equals `6`
   - Expected: bytes[0] equals `0x66`
   - Expected: bytes[1] equals `0x0F`
   - Expected: bytes[2] equals `0x3A`
   - Expected: bytes[3] equals `0x44`
   - Expected: bytes[4] equals `0xC0`
   - Expected: bytes[5] equals `0x00`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("emit_pclmulqdq(0,0,0x00) → [0x66, 0x0F, 0x3A, 0x44, 0xC0, 0x00]")
step("Verify: emit_pclmulqdq(0,0,0x00) → [0x66, 0x0F, 0x3A, 0x44, 0xC0, 0x00]")
val bytes = emit_pclmulqdq(0, 0, 0x00)
expect(bytes.len()).to_equal(6)
expect(bytes[0]).to_equal(0x66)
expect(bytes[1]).to_equal(0x0F)
expect(bytes[2]).to_equal(0x3A)
expect(bytes[3]).to_equal(0x44)
expect(bytes[4]).to_equal(0xC0)
expect(bytes[5]).to_equal(0x00)
```

</details>

#### emit_pclmulqdq(0,0,0x11) → [0x66, 0x0F, 0x3A, 0x44, 0xC0, 0x11]

- emit_pclmulqdq(0,0,0x11) → [0x66, 0x0F, 0x3A, 0x44, 0xC0, 0x11]
- Verify: emit_pclmulqdq(0,0,0x11) → [0x66, 0x0F, 0x3A, 0x44, 0xC0, 0x11]
   - Expected: bytes.len() equals `6`
   - Expected: bytes[0] equals `0x66`
   - Expected: bytes[1] equals `0x0F`
   - Expected: bytes[2] equals `0x3A`
   - Expected: bytes[3] equals `0x44`
   - Expected: bytes[4] equals `0xC0`
   - Expected: bytes[5] equals `0x11`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("emit_pclmulqdq(0,0,0x11) → [0x66, 0x0F, 0x3A, 0x44, 0xC0, 0x11]")
step("Verify: emit_pclmulqdq(0,0,0x11) → [0x66, 0x0F, 0x3A, 0x44, 0xC0, 0x11]")
val bytes = emit_pclmulqdq(0, 0, 0x11)
expect(bytes.len()).to_equal(6)
expect(bytes[0]).to_equal(0x66)
expect(bytes[1]).to_equal(0x0F)
expect(bytes[2]).to_equal(0x3A)
expect(bytes[3]).to_equal(0x44)
expect(bytes[4]).to_equal(0xC0)
expect(bytes[5]).to_equal(0x11)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 14 |
| Active scenarios | 14 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-COMPILER`
- `REQ-COMP-X86-AES-NI-ENCODER-GOLDEN-BYTES-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `09beb20587dd2ce0343f0224a6e50363f8748b1c70bf463cc5d1828aa266a516`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `09beb20587dd2ce0343f0224a6e50363f8748b1c70bf463cc5d1828aa266a516`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `09beb20587dd2ce0343f0224a6e50363f8748b1c70bf463cc5d1828aa266a516`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/compiler/backend/encode_x86_64_crypto_spec.spl
mirror: doc/06_spec/01_unit/compiler/backend/encode_x86_64_crypto_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/backend/encode_x86_64_crypto_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/backend/encode_x86_64_crypto_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/backend/encode_x86_64_crypto_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 14 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/backend/encode_x86_64_crypto_spec.spl:52:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'emit_aesenc(0,0) → [0x66, 0x0F, 0x38, 0xDC, 0xC0]' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/backend/encode_x86_64_crypto_spec.spl:65:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'emit_aesenc(8,0) → [0x66, 0x44, 0x0F, 0x38, 0xDC, 0xC0] (REX.R for dst>=8)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/backend/encode_x86_64_crypto_spec.spl:78:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'emit_aesenclast(0,0) → [0x66, 0x0F, 0x38, 0xDD, 0xC0]' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

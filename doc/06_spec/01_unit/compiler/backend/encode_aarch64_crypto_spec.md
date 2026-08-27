# encode_aarch64_crypto_spec

> Purpose: Prove that emit_aese — AES single-round encryption.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 15 | 15 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# encode_aarch64_crypto_spec

Purpose: Prove that emit_aese — AES single-round encryption.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/backend/encode_aarch64_crypto_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Prove that emit_aese — AES single-round encryption.
Audience: COMP maintainers who read this spec to confirm the behavior still holds.

## Scenarios

### emit_aese — AES single-round encryption

#### AESE V1, V2 encodes to correct LE bytes

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- AESE V1, V2 encodes to correct LE bytes
- Verify: AESE V1, V2 encodes to correct LE bytes
   - Expected: b.len() equals `4`
   - Expected: b[0] equals `0x41`
   - Expected: b[1] equals `0x48`
   - Expected: b[2] equals `0x28`
   - Expected: b[3] equals `0x4E`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("AESE V1, V2 encodes to correct LE bytes")
step("Verify: AESE V1, V2 encodes to correct LE bytes")
# @req: REQ-COMP-EMIT-AESE-AES-SINGLE-ROUND-ENCRYPTION-001
var b = emit_aese(1, 2)
expect(b.len()).to_equal(4)
expect(b[0]).to_equal(0x41)
expect(b[1]).to_equal(0x48)
expect(b[2]).to_equal(0x28)
expect(b[3]).to_equal(0x4E)
```

</details>

#### AESE V0, V0 produces base opcode bytes

- AESE V0, V0 produces base opcode bytes
- Verify: AESE V0, V0 produces base opcode bytes
   - Expected: b[0] equals `0x00`
   - Expected: b[1] equals `0x48`
   - Expected: b[2] equals `0x28`
   - Expected: b[3] equals `0x4E`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("AESE V0, V0 produces base opcode bytes")
step("Verify: AESE V0, V0 produces base opcode bytes")
var b = emit_aese(0, 0)
expect(b[0]).to_equal(0x00)
expect(b[1]).to_equal(0x48)
expect(b[2]).to_equal(0x28)
expect(b[3]).to_equal(0x4E)
```

</details>

### emit_aesd — AES single-round decryption

#### AESD V1, V2 encodes to correct LE bytes

- AESD V1, V2 encodes to correct LE bytes
- Verify: AESD V1, V2 encodes to correct LE bytes
   - Expected: b.len() equals `4`
   - Expected: b[0] equals `0x41`
   - Expected: b[1] equals `0x58`
   - Expected: b[2] equals `0x28`
   - Expected: b[3] equals `0x4E`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("AESD V1, V2 encodes to correct LE bytes")
step("Verify: AESD V1, V2 encodes to correct LE bytes")
var b = emit_aesd(1, 2)
expect(b.len()).to_equal(4)
expect(b[0]).to_equal(0x41)
expect(b[1]).to_equal(0x58)
expect(b[2]).to_equal(0x28)
expect(b[3]).to_equal(0x4E)
```

</details>

### emit_aesmc_aarch64 — AES mix columns

#### AESMC V1, V1 encodes to correct LE bytes

- AESMC V1, V1 encodes to correct LE bytes
- Verify: AESMC V1, V1 encodes to correct LE bytes
   - Expected: b.len() equals `4`
   - Expected: b[0] equals `0x21`
   - Expected: b[1] equals `0x68`
   - Expected: b[2] equals `0x28`
   - Expected: b[3] equals `0x4E`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("AESMC V1, V1 encodes to correct LE bytes")
step("Verify: AESMC V1, V1 encodes to correct LE bytes")
var b = emit_aesmc_aarch64(1, 1)
expect(b.len()).to_equal(4)
expect(b[0]).to_equal(0x21)
expect(b[1]).to_equal(0x68)
expect(b[2]).to_equal(0x28)
expect(b[3]).to_equal(0x4E)
```

</details>

### emit_aesimc_aarch64 — AES inverse mix columns

#### AESIMC V1, V2 encodes to correct LE bytes

- AESIMC V1, V2 encodes to correct LE bytes
- Verify: AESIMC V1, V2 encodes to correct LE bytes
   - Expected: b.len() equals `4`
   - Expected: b[0] equals `0x41`
   - Expected: b[1] equals `0x78`
   - Expected: b[2] equals `0x28`
   - Expected: b[3] equals `0x4E`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("AESIMC V1, V2 encodes to correct LE bytes")
step("Verify: AESIMC V1, V2 encodes to correct LE bytes")
var b = emit_aesimc_aarch64(1, 2)
expect(b.len()).to_equal(4)
expect(b[0]).to_equal(0x41)
expect(b[1]).to_equal(0x78)
expect(b[2]).to_equal(0x28)
expect(b[3]).to_equal(0x4E)
```

</details>

### emit_sha256h — SHA-256 hash update part 1

#### SHA256H Q0, Q1, V2 encodes to correct LE bytes

- SHA256H Q0, Q1, V2 encodes to correct LE bytes
- Verify: SHA256H Q0, Q1, V2 encodes to correct LE bytes
   - Expected: b.len() equals `4`
   - Expected: b[0] equals `0x20`
   - Expected: b[1] equals `0x40`
   - Expected: b[2] equals `0x02`
   - Expected: b[3] equals `0x5E`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("SHA256H Q0, Q1, V2 encodes to correct LE bytes")
step("Verify: SHA256H Q0, Q1, V2 encodes to correct LE bytes")
var b = emit_sha256h(0, 1, 2)
expect(b.len()).to_equal(4)
expect(b[0]).to_equal(0x20)
expect(b[1]).to_equal(0x40)
expect(b[2]).to_equal(0x02)
expect(b[3]).to_equal(0x5E)
```

</details>

### emit_sha256h2 — SHA-256 hash update part 2

#### SHA256H2 Q0, Q1, V2 encodes to correct LE bytes

- SHA256H2 Q0, Q1, V2 encodes to correct LE bytes
- Verify: SHA256H2 Q0, Q1, V2 encodes to correct LE bytes
   - Expected: b.len() equals `4`
   - Expected: b[0] equals `0x20`
   - Expected: b[1] equals `0x50`
   - Expected: b[2] equals `0x02`
   - Expected: b[3] equals `0x5E`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("SHA256H2 Q0, Q1, V2 encodes to correct LE bytes")
step("Verify: SHA256H2 Q0, Q1, V2 encodes to correct LE bytes")
var b = emit_sha256h2(0, 1, 2)
expect(b.len()).to_equal(4)
expect(b[0]).to_equal(0x20)
expect(b[1]).to_equal(0x50)
expect(b[2]).to_equal(0x02)
expect(b[3]).to_equal(0x5E)
```

</details>

### emit_sha256su0 — SHA-256 schedule update 0

#### SHA256SU0 V1, V2 encodes to correct LE bytes

- SHA256SU0 V1, V2 encodes to correct LE bytes
- Verify: SHA256SU0 V1, V2 encodes to correct LE bytes
   - Expected: b.len() equals `4`
   - Expected: b[0] equals `0x41`
   - Expected: b[1] equals `0x28`
   - Expected: b[2] equals `0x28`
   - Expected: b[3] equals `0x5E`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("SHA256SU0 V1, V2 encodes to correct LE bytes")
step("Verify: SHA256SU0 V1, V2 encodes to correct LE bytes")
var b = emit_sha256su0(1, 2)
expect(b.len()).to_equal(4)
expect(b[0]).to_equal(0x41)
expect(b[1]).to_equal(0x28)
expect(b[2]).to_equal(0x28)
expect(b[3]).to_equal(0x5E)
```

</details>

### emit_sha256su1 — SHA-256 schedule update 1

#### SHA256SU1 V0, V1, V2 encodes to correct LE bytes

- SHA256SU1 V0, V1, V2 encodes to correct LE bytes
- Verify: SHA256SU1 V0, V1, V2 encodes to correct LE bytes
   - Expected: b.len() equals `4`
   - Expected: b[0] equals `0x20`
   - Expected: b[1] equals `0x60`
   - Expected: b[2] equals `0x02`
   - Expected: b[3] equals `0x5E`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("SHA256SU1 V0, V1, V2 encodes to correct LE bytes")
step("Verify: SHA256SU1 V0, V1, V2 encodes to correct LE bytes")
var b = emit_sha256su1(0, 1, 2)
expect(b.len()).to_equal(4)
expect(b[0]).to_equal(0x20)
expect(b[1]).to_equal(0x60)
expect(b[2]).to_equal(0x02)
expect(b[3]).to_equal(0x5E)
```

</details>

### emit_pmull — polynomial multiply lower halves

#### PMULL V0, V1, V2 encodes to correct LE bytes

- PMULL V0, V1, V2 encodes to correct LE bytes
- Verify: PMULL V0, V1, V2 encodes to correct LE bytes
   - Expected: b.len() equals `4`
   - Expected: b[0] equals `0x20`
   - Expected: b[1] equals `0xE0`
   - Expected: b[2] equals `0xE2`
   - Expected: b[3] equals `0x0E`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("PMULL V0, V1, V2 encodes to correct LE bytes")
step("Verify: PMULL V0, V1, V2 encodes to correct LE bytes")
var b = emit_pmull(0, 1, 2)
expect(b.len()).to_equal(4)
expect(b[0]).to_equal(0x20)
expect(b[1]).to_equal(0xE0)
expect(b[2]).to_equal(0xE2)
expect(b[3]).to_equal(0x0E)
```

</details>

### emit_pmull2 — polynomial multiply upper halves

#### PMULL2 V0, V1, V2 encodes to correct LE bytes

- PMULL2 V0, V1, V2 encodes to correct LE bytes
- Verify: PMULL2 V0, V1, V2 encodes to correct LE bytes
   - Expected: b.len() equals `4`
   - Expected: b[0] equals `0x20`
   - Expected: b[1] equals `0xE0`
   - Expected: b[2] equals `0xE2`
   - Expected: b[3] equals `0x4E`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("PMULL2 V0, V1, V2 encodes to correct LE bytes")
step("Verify: PMULL2 V0, V1, V2 encodes to correct LE bytes")
var b = emit_pmull2(0, 1, 2)
expect(b.len()).to_equal(4)
expect(b[0]).to_equal(0x20)
expect(b[1]).to_equal(0xE0)
expect(b[2]).to_equal(0xE2)
expect(b[3]).to_equal(0x4E)
```

</details>

### emit_crc32b — CRC32 byte accumulate

#### CRC32B W0, W1, W2 encodes to correct LE bytes

- CRC32B W0, W1, W2 encodes to correct LE bytes
- Verify: CRC32B W0, W1, W2 encodes to correct LE bytes
   - Expected: b.len() equals `4`
   - Expected: b[0] equals `0x20`
   - Expected: b[1] equals `0x40`
   - Expected: b[2] equals `0xC2`
   - Expected: b[3] equals `0x1A`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("CRC32B W0, W1, W2 encodes to correct LE bytes")
step("Verify: CRC32B W0, W1, W2 encodes to correct LE bytes")
var b = emit_crc32b(0, 1, 2)
expect(b.len()).to_equal(4)
expect(b[0]).to_equal(0x20)
expect(b[1]).to_equal(0x40)
expect(b[2]).to_equal(0xC2)
expect(b[3]).to_equal(0x1A)
```

</details>

### emit_crc32h — CRC32 halfword accumulate

#### CRC32H W0, W1, W2 encodes to correct LE bytes

- CRC32H W0, W1, W2 encodes to correct LE bytes
- Verify: CRC32H W0, W1, W2 encodes to correct LE bytes
   - Expected: b.len() equals `4`
   - Expected: b[0] equals `0x20`
   - Expected: b[1] equals `0x44`
   - Expected: b[2] equals `0xC2`
   - Expected: b[3] equals `0x1A`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("CRC32H W0, W1, W2 encodes to correct LE bytes")
step("Verify: CRC32H W0, W1, W2 encodes to correct LE bytes")
var b = emit_crc32h(0, 1, 2)
expect(b.len()).to_equal(4)
expect(b[0]).to_equal(0x20)
expect(b[1]).to_equal(0x44)
expect(b[2]).to_equal(0xC2)
expect(b[3]).to_equal(0x1A)
```

</details>

### emit_crc32w — CRC32 word accumulate

#### CRC32W W0, W1, W2 encodes to correct LE bytes

- CRC32W W0, W1, W2 encodes to correct LE bytes
- Verify: CRC32W W0, W1, W2 encodes to correct LE bytes
   - Expected: b.len() equals `4`
   - Expected: b[0] equals `0x20`
   - Expected: b[1] equals `0x48`
   - Expected: b[2] equals `0xC2`
   - Expected: b[3] equals `0x1A`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("CRC32W W0, W1, W2 encodes to correct LE bytes")
step("Verify: CRC32W W0, W1, W2 encodes to correct LE bytes")
var b = emit_crc32w(0, 1, 2)
expect(b.len()).to_equal(4)
expect(b[0]).to_equal(0x20)
expect(b[1]).to_equal(0x48)
expect(b[2]).to_equal(0xC2)
expect(b[3]).to_equal(0x1A)
```

</details>

### emit_crc32x — CRC32 doubleword accumulate

#### CRC32X W0, W1, X2 encodes to correct LE bytes

- CRC32X W0, W1, X2 encodes to correct LE bytes
- Verify: CRC32X W0, W1, X2 encodes to correct LE bytes
   - Expected: b.len() equals `4`
   - Expected: b[0] equals `0x20`
   - Expected: b[1] equals `0x4C`
   - Expected: b[2] equals `0xC2`
   - Expected: b[3] equals `0x9A`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("CRC32X W0, W1, X2 encodes to correct LE bytes")
step("Verify: CRC32X W0, W1, X2 encodes to correct LE bytes")
var b = emit_crc32x(0, 1, 2)
expect(b.len()).to_equal(4)
expect(b[0]).to_equal(0x20)
expect(b[1]).to_equal(0x4C)
expect(b[2]).to_equal(0xC2)
expect(b[3]).to_equal(0x9A)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 15 |
| Active scenarios | 15 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-COMPILER`
- `REQ-COMP-EMIT-AESE-AES-SINGLE-ROUND-ENCRYPTION-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `a3f7ad0dc5ec83dd0f6b3b5e3903b4aab53074167d42e55176ec751a3aa5a3ed`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `a3f7ad0dc5ec83dd0f6b3b5e3903b4aab53074167d42e55176ec751a3aa5a3ed`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `a3f7ad0dc5ec83dd0f6b3b5e3903b4aab53074167d42e55176ec751a3aa5a3ed`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/compiler/backend/encode_aarch64_crypto_spec.spl
mirror: doc/06_spec/01_unit/compiler/backend/encode_aarch64_crypto_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/backend/encode_aarch64_crypto_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/backend/encode_aarch64_crypto_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/backend/encode_aarch64_crypto_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 14 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/backend/encode_aarch64_crypto_spec.spl:53:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AESE V1, V2 encodes to correct LE bytes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/backend/encode_aarch64_crypto_spec.spl:65:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AESE V0, V0 produces base opcode bytes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/backend/encode_aarch64_crypto_spec.spl:81:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AESD V1, V2 encodes to correct LE bytes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

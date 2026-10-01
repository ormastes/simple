# lowering_riscv_crypto_spec

> Purpose: Prove that RV64 Zvk cipher intrinsic lowering — AES rounds.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# lowering_riscv_crypto_spec

Purpose: Prove that RV64 Zvk cipher intrinsic lowering — AES rounds.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/backend/lowering_riscv_crypto_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Prove that RV64 Zvk cipher intrinsic lowering — AES rounds.
Audience: COMP maintainers who read this spec to confirm the behavior still holds.

## Scenarios

### RV64 Zvk cipher intrinsic lowering — AES rounds

#### vaesem.vv v1,v2 (crypto_aes_round [1,2]) — mid-round encrypt

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- vaesem.vv v1,v2 (crypto_aes_round [1,2]) — mid-round encrypt
- Verify: vaesem.vv v1,v2 (crypto_aes_round [1,2]) — mid-round encrypt
   - Expected: result.lowered is true
   - Expected: result.reason equals ``
   - Expected: _list_hex(result.bytes) equals `d72020a6`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("vaesem.vv v1,v2 (crypto_aes_round [1,2]) — mid-round encrypt")
step("Verify: vaesem.vv v1,v2 (crypto_aes_round [1,2]) — mid-round encrypt")
# @req: REQ-COMP-RV64-ZVK-CIPHER-INTRINSIC-LOWERING-AES-R-001
val result = lower_cipher_intrinsic_riscv("crypto_aes_round", [1, 2], TEST_RV64_CAPS)
expect(result.lowered).to_equal(true)
expect(result.reason).to_equal("")
expect(_list_hex(result.bytes)).to_equal("d72020a6")
```

</details>

#### vaesem.vv output length is 4 bytes

- vaesem.vv output length is 4 bytes
- Verify: vaesem.vv output length is 4 bytes
   - Expected: result.bytes.len() equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("vaesem.vv output length is 4 bytes")
step("Verify: vaesem.vv output length is 4 bytes")
val result = lower_cipher_intrinsic_riscv("crypto_aes_round", [1, 2], TEST_RV64_CAPS)
expect(result.bytes.len()).to_equal(4)
```

</details>

#### vaesef.vv v1,v2 (crypto_aes_round_last [1,2]) — final-round encrypt

- vaesef.vv v1,v2 (crypto_aes_round_last [1,2]) — final-round encrypt
- Verify: vaesef.vv v1,v2 (crypto_aes_round_last [1,2]) — final-round encrypt
   - Expected: result.lowered is true
   - Expected: result.reason equals ``
   - Expected: _list_hex(result.bytes) equals `d72020a2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("vaesef.vv v1,v2 (crypto_aes_round_last [1,2]) — final-round encrypt")
step("Verify: vaesef.vv v1,v2 (crypto_aes_round_last [1,2]) — final-round encrypt")
val result = lower_cipher_intrinsic_riscv("crypto_aes_round_last", [1, 2], TEST_RV64_CAPS)
expect(result.lowered).to_equal(true)
expect(result.reason).to_equal("")
expect(_list_hex(result.bytes)).to_equal("d72020a2")
```

</details>

#### vaesef.vv output length is 4 bytes

- vaesef.vv output length is 4 bytes
- Verify: vaesef.vv output length is 4 bytes
   - Expected: result.bytes.len() equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("vaesef.vv output length is 4 bytes")
step("Verify: vaesef.vv output length is 4 bytes")
val result = lower_cipher_intrinsic_riscv("crypto_aes_round_last", [1, 2], TEST_RV64_CAPS)
expect(result.bytes.len()).to_equal(4)
```

</details>

#### vaesdm.vv v1,v2 (crypto_aes_inv_round [1,2]) — mid-round decrypt

- vaesdm.vv v1,v2 (crypto_aes_inv_round [1,2]) — mid-round decrypt
- Verify: vaesdm.vv v1,v2 (crypto_aes_inv_round [1,2]) — mid-round decrypt
   - Expected: result.lowered is true
   - Expected: result.reason equals ``
   - Expected: _list_hex(result.bytes) equals `d72020ae`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("vaesdm.vv v1,v2 (crypto_aes_inv_round [1,2]) — mid-round decrypt")
step("Verify: vaesdm.vv v1,v2 (crypto_aes_inv_round [1,2]) — mid-round decrypt")
val result = lower_cipher_intrinsic_riscv("crypto_aes_inv_round", [1, 2], TEST_RV64_CAPS)
expect(result.lowered).to_equal(true)
expect(result.reason).to_equal("")
expect(_list_hex(result.bytes)).to_equal("d72020ae")
```

</details>

#### vaesdm.vv output length is 4 bytes

- vaesdm.vv output length is 4 bytes
- Verify: vaesdm.vv output length is 4 bytes
   - Expected: result.bytes.len() equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("vaesdm.vv output length is 4 bytes")
step("Verify: vaesdm.vv output length is 4 bytes")
val result = lower_cipher_intrinsic_riscv("crypto_aes_inv_round", [1, 2], TEST_RV64_CAPS)
expect(result.bytes.len()).to_equal(4)
```

</details>

#### vaesdf.vv v1,v2 (crypto_aes_inv_round_last [1,2]) — final-round decrypt

- vaesdf.vv v1,v2 (crypto_aes_inv_round_last [1,2]) — final-round decrypt
- Verify: vaesdf.vv v1,v2 (crypto_aes_inv_round_last [1,2]) — final-round decrypt
   - Expected: result.lowered is true
   - Expected: result.reason equals ``
   - Expected: _list_hex(result.bytes) equals `d72020aa`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("vaesdf.vv v1,v2 (crypto_aes_inv_round_last [1,2]) — final-round decrypt")
step("Verify: vaesdf.vv v1,v2 (crypto_aes_inv_round_last [1,2]) — final-round decrypt")
val result = lower_cipher_intrinsic_riscv("crypto_aes_inv_round_last", [1, 2], TEST_RV64_CAPS)
expect(result.lowered).to_equal(true)
expect(result.reason).to_equal("")
expect(_list_hex(result.bytes)).to_equal("d72020aa")
```

</details>

#### vaesdf.vv output length is 4 bytes

- vaesdf.vv output length is 4 bytes
- Verify: vaesdf.vv output length is 4 bytes
   - Expected: result.bytes.len() equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("vaesdf.vv output length is 4 bytes")
step("Verify: vaesdf.vv output length is 4 bytes")
val result = lower_cipher_intrinsic_riscv("crypto_aes_inv_round_last", [1, 2], TEST_RV64_CAPS)
expect(result.bytes.len()).to_equal(4)
```

</details>

### RV64 Zvk cipher intrinsic lowering — failure cases

#### unknown intrinsic returns lowered=false, reason=unknown

- unknown intrinsic returns lowered=false, reason=unknown
- Verify: unknown intrinsic returns lowered=false, reason=unknown
   - Expected: result.lowered is false
   - Expected: result.reason equals `unknown`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("unknown intrinsic returns lowered=false, reason=unknown")
step("Verify: unknown intrinsic returns lowered=false, reason=unknown")
val result = lower_cipher_intrinsic_riscv("unknown_intrinsic", [0, 0], TEST_RV64_CAPS)
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
val result = lower_cipher_intrinsic_riscv("crypto_aes_round", [0], TEST_RV64_CAPS)
expect(result.lowered).to_equal(false)
expect(result.reason).to_equal("bad-arity")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 10 |
| Active scenarios | 10 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-COMPILER`
- `REQ-COMP-RV64-ZVK-CIPHER-INTRINSIC-LOWERING-AES-R-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `5c9538c6c5954a30de9e192b0a50a60fa5bcecad84a6ea787e5e714518cd1cdd`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `5c9538c6c5954a30de9e192b0a50a60fa5bcecad84a6ea787e5e714518cd1cdd`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `5c9538c6c5954a30de9e192b0a50a60fa5bcecad84a6ea787e5e714518cd1cdd`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/compiler/backend/lowering_riscv_crypto_spec.spl
mirror: doc/06_spec/01_unit/compiler/backend/lowering_riscv_crypto_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/backend/lowering_riscv_crypto_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/backend/lowering_riscv_crypto_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/backend/lowering_riscv_crypto_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 4 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/backend/lowering_riscv_crypto_spec.spl:55:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'vaesem.vv v1,v2 (crypto_aes_round [1,2]) — mid-round encrypt' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/backend/lowering_riscv_crypto_spec.spl:65:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'vaesem.vv output length is 4 bytes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/backend/lowering_riscv_crypto_spec.spl:72:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'vaesef.vv v1,v2 (crypto_aes_round_last [1,2]) — final-round encrypt' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

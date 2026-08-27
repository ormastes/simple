# Twofish Kat Specification

> Tests covering Twofish — known-answer vectors (Twofish paper Table 4).

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Twofish Kat Specification

## Scenarios

### Twofish — known-answer vectors (Twofish paper Table 4)

#### Twofish-128: encrypt all-zero key + all-zero PT

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- Twofish-128: encrypt all-zero key + all-zero PT
   - Expected: _bytes_to_hex(ct) equals `9f589f5cf6122c32b6bfec2f2ae8c35a`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Twofish-128: encrypt all-zero key + all-zero PT")
val ct = twofish_encrypt_block(_zero16(), _zero16())
expect(_bytes_to_hex(ct)).to_equal("9f589f5cf6122c32b6bfec2f2ae8c35a")
```

</details>

#### Twofish-128: ciphertext is 16 bytes

- Twofish-128: ciphertext is 16 bytes
   - Expected: ct.len() equals `16`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Twofish-128: ciphertext is 16 bytes")
val ct = twofish_encrypt_block(_zero16(), _zero16())
expect(ct.len()).to_equal(16)
```

</details>

#### Twofish-128: decrypt round-trip recovers plaintext

- Twofish-128: decrypt round-trip recovers plaintext
   - Expected: _bytes_to_hex(pt) equals `00000000000000000000000000000000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Twofish-128: decrypt round-trip recovers plaintext")
val ct = twofish_encrypt_block(_zero16(), _zero16())
val pt = twofish_decrypt_block(_zero16(), ct)
expect(_bytes_to_hex(pt)).to_equal("00000000000000000000000000000000")
```

</details>

#### Twofish-128: decrypt known ciphertext recovers all-zero PT

- Twofish-128: decrypt known ciphertext recovers all-zero PT
   - Expected: _bytes_to_hex(pt) equals `00000000000000000000000000000000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Twofish-128: decrypt known ciphertext recovers all-zero PT")
val pt = twofish_decrypt_block(_zero16(), _ct_128_expected())
expect(_bytes_to_hex(pt)).to_equal("00000000000000000000000000000000")
```

</details>

#### Twofish-256: encrypt all-zero key + all-zero PT

- Twofish-256: encrypt all-zero key + all-zero PT
   - Expected: _bytes_to_hex(ct) equals `57ff739d4dc92c1bd7fc01700cc8216f`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Twofish-256: encrypt all-zero key + all-zero PT")
val ct = twofish_encrypt_block(_zero32(), _zero16())
expect(_bytes_to_hex(ct)).to_equal("57ff739d4dc92c1bd7fc01700cc8216f")
```

</details>

#### Twofish-256: ciphertext is 16 bytes

- Twofish-256: ciphertext is 16 bytes
   - Expected: ct.len() equals `16`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Twofish-256: ciphertext is 16 bytes")
val ct = twofish_encrypt_block(_zero32(), _zero16())
expect(ct.len()).to_equal(16)
```

</details>

#### Twofish-256: decrypt round-trip recovers plaintext

- Twofish-256: decrypt round-trip recovers plaintext
   - Expected: _bytes_to_hex(pt) equals `00000000000000000000000000000000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Twofish-256: decrypt round-trip recovers plaintext")
val ct = twofish_encrypt_block(_zero32(), _zero16())
val pt = twofish_decrypt_block(_zero32(), ct)
expect(_bytes_to_hex(pt)).to_equal("00000000000000000000000000000000")
```

</details>

#### Twofish-256: decrypt known ciphertext recovers all-zero PT

- Twofish-256: decrypt known ciphertext recovers all-zero PT
   - Expected: _bytes_to_hex(pt) equals `00000000000000000000000000000000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Twofish-256: decrypt known ciphertext recovers all-zero PT")
val pt = twofish_decrypt_block(_zero32(), _ct_256_expected())
expect(_bytes_to_hex(pt)).to_equal("00000000000000000000000000000000")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/unit/os/crypto/twofish_kat_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Twofish — known-answer vectors (Twofish paper Table 4).
- Twofish — known-answer vectors (Twofish paper Table 4)

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
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

- Canonical SPipe generation for source `e70965c6dea1f998a7b026a7c1171957428d59de0bf5f404506e73e3905b85db`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `e70965c6dea1f998a7b026a7c1171957428d59de0bf5f404506e73e3905b85db`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `e70965c6dea1f998a7b026a7c1171957428d59de0bf5f404506e73e3905b85db`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/unit/os/crypto/twofish_kat_spec.spl
mirror: doc/06_spec/unit/os/crypto/twofish_kat_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/os/crypto/twofish_kat_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/os/crypto/twofish_kat_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/os/crypto/twofish_kat_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/os/crypto/twofish_kat_spec.spl:155:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'Twofish-128: encrypt all-zero key + all-zero PT' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/os/crypto/twofish_kat_spec.spl:161:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'Twofish-128: ciphertext is 16 bytes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/os/crypto/twofish_kat_spec.spl:167:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'Twofish-128: decrypt round-trip recovers plaintext' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

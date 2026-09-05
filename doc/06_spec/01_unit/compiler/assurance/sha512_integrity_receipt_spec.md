# Sha512 Integrity Receipt Specification

> Tests covering FV2 optional SHA-512 integrity receipt.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Sha512 Integrity Receipt Specification

## Scenarios

### FV2 optional SHA-512 integrity receipt

#### binds SHA-512 to, but does not replace, the frozen SHA-256 identity

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- binds SHA-512 to, but does not replace, the frozen SHA-256 identity
   - Expected: receipt.diagnostic() equals ``
   - Expected: receipt.subject_sha256.len() equals `64`
   - Expected: receipt.subject_sha512.len() equals `128`
   - Expected: receipt.binds_content(content) is true
   - Expected: receipt.receipt_hash().len() equals `64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("binds SHA-512 to, but does not replace, the frozen SHA-256 identity")
val content = "artifact bytes\\n"
val receipt = materialize_optional_sha512_integrity_receipt_v1(
    "artifact", content, sha256_text(content))
expect(receipt.diagnostic()).to_equal("")
expect(receipt.subject_sha256.len()).to_equal(64)
expect(receipt.subject_sha512.len()).to_equal(128)
expect(receipt.binds_content(content)).to_equal(true)
expect(receipt.receipt_hash().len()).to_equal(64)
```

</details>

#### rejects a stale frozen identity instead of silently promoting SHA-512

- rejects a stale frozen identity instead of silently promoting SHA-512
   - Expected: receipt.receipt_hash() equals ``
   - Expected: receipt.binds_content("current") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("rejects a stale frozen identity instead of silently promoting SHA-512")
val receipt = materialize_optional_sha512_integrity_receipt_v1(
    "artifact", "current", sha256_text("stale"))
expect(receipt.diagnostic()).to_contain("SHA512")
expect(receipt.receipt_hash()).to_equal("")
expect(receipt.binds_content("current")).to_equal(false)
```

</details>

#### changes the additive receipt when the exact content changes

- changes the additive receipt when the exact content changes
   - Expected: first.receipt_hash() == second.receipt_hash() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("changes the additive receipt when the exact content changes")
val first = materialize_optional_sha512_integrity_receipt_v1(
    "evidence", "first", sha256_text("first"))
val second = materialize_optional_sha512_integrity_receipt_v1(
    "evidence", "second", sha256_text("second"))
expect(first.receipt_hash() == second.receipt_hash()).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/assurance/sha512_integrity_receipt_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering FV2 optional SHA-512 integrity receipt.
- FV2 optional SHA-512 integrity receipt

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-COMPILER`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `701b002a8629bb2d4bd55f1fb6e5f6627835079a1e0ee04861b14276a9f6661f`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `701b002a8629bb2d4bd55f1fb6e5f6627835079a1e0ee04861b14276a9f6661f`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `701b002a8629bb2d4bd55f1fb6e5f6627835079a1e0ee04861b14276a9f6661f`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/compiler/assurance/sha512_integrity_receipt_spec.spl
mirror: doc/06_spec/01_unit/compiler/assurance/sha512_integrity_receipt_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/assurance/sha512_integrity_receipt_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/assurance/sha512_integrity_receipt_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/assurance/sha512_integrity_receipt_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 3 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/assurance/sha512_integrity_receipt_spec.spl:20:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'binds SHA-512 to, but does not replace, the frozen SHA-256 identity' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/assurance/sha512_integrity_receipt_spec.spl:32:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects a stale frozen identity instead of silently promoting SHA-512' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/assurance/sha512_integrity_receipt_spec.spl:41:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'changes the additive receipt when the exact content changes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

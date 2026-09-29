# Inline Asm Matrix Specification

> Tests covering Inline asm canonical block syntax, Inline asm x86_32 matrix, Inline asm x86_64 matrix, Inline asm arm32 matrix, Inline asm arm64 matrix, Inline asm riscv32 matrix, Inline asm riscv64 matrix, Inline asm mode contracts.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 24 | 24 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Inline Asm Matrix Specification

## Scenarios

- uses braced raw asm for non-volatile instructions
- uses braced raw asm for volatile instructions
- keeps parenthesized syntax out of raw embedded asm fixtures
- covers x86_32 interpreter mode
- covers x86_32 loader mode
- covers x86_32 compiler mode
- covers x86_64 interpreter mode
- covers x86_64 loader mode
- covers x86_64 compiler mode
- covers arm32 interpreter mode
- covers arm32 loader mode
- covers arm32 compiler mode
- covers arm64 interpreter mode
- covers arm64 loader mode
- covers arm64 compiler mode
- covers riscv32 interpreter mode
- covers riscv32 loader mode
- covers riscv32 compiler mode
- covers riscv64 interpreter mode
- covers riscv64 loader mode
- covers riscv64 compiler mode
- documents interpreter as parse-and-skip only
- documents loader as preservation and linking
- documents compiler as raw instruction emission

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/unit/compiler/native/inline_asm_matrix_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Inline asm canonical block syntax, Inline asm x86_32 matrix, Inline asm x86_64 matrix, Inline asm arm32 matrix, Inline asm arm64 matrix, Inline asm riscv32 matrix, Inline asm riscv64 matrix, Inline asm mode contracts.
- Inline asm canonical block syntax
- Inline asm x86_32 matrix
- Inline asm x86_64 matrix
- Inline asm arm32 matrix
- Inline asm arm64 matrix
- Inline asm riscv32 matrix
- Inline asm riscv64 matrix
- Inline asm mode contracts

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 24 |
| Active scenarios | 24 |
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

- Canonical SPipe generation for source `ded9ecc735c64ef8e3dff4e5761a6af18dc457f96dee04f910d3b34191f18331`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `ded9ecc735c64ef8e3dff4e5761a6af18dc457f96dee04f910d3b34191f18331`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `ded9ecc735c64ef8e3dff4e5761a6af18dc457f96dee04f910d3b34191f18331`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/compiler/native/inline_asm_matrix_spec.spl
mirror: doc/06_spec/unit/compiler/native/inline_asm_matrix_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/compiler/native/inline_asm_matrix_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/compiler/native/inline_asm_matrix_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/compiler/native/inline_asm_matrix_spec.spl:45:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'uses braced raw asm for non-volatile instructions' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/native/inline_asm_matrix_spec.spl:51:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'uses braced raw asm for volatile instructions' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/native/inline_asm_matrix_spec.spl:57:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps parenthesized syntax out of raw embedded asm fixtures' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

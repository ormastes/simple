# Nat Normalizer Receipt Specification

> Tests covering bounded Nat normalizer evidence.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Nat Normalizer Receipt Specification

## Scenarios

### bounded Nat normalizer evidence

#### binds the exact bounded candidate identity without calling it replay

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- binds the exact bounded candidate identity without calling it replay
   - Expected: receipt.is_candidate() is true
   - Expected: receipt.hash() == "" is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("binds the exact bounded candidate identity without calling it replay")
val receipt = candidate()
expect(receipt.is_candidate()).to_equal(true)
expect(receipt.hash() == "").to_equal(false)
expect(nat_normalizer_cannot_close_replay_v1(receipt)).to_contain(
    "NONPROMOTING")
```

</details>

#### rejects native extensions even when an export was normalized

- rejects native extensions even when an export was normalized
   - Expected: receipt.is_candidate() is false
   - Expected: receipt.hash() equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects native extensions even when an export was normalized")
val receipt = candidate()
receipt.native_extensions_enabled = true
expect(receipt.is_candidate()).to_equal(false)
expect(receipt.candidate_diagnostic()).to_contain("NATIVE")
expect(receipt.hash()).to_equal("")
```

</details>

#### rejects unbounded and nonexecuted candidate declarations

- rejects unbounded and nonexecuted candidate declarations


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects unbounded and nonexecuted candidate declarations")
val unbounded = candidate()
unbounded.max_rewrite_steps = 0
expect(unbounded.candidate_diagnostic()).to_contain("BOUNDS")
val not_run = candidate()
not_run.outcome = BoundedNatNormalizerOutcomeV1.NotRun
expect(not_run.candidate_diagnostic()).to_contain("OUTCOME")
```

</details>

#### rejects an identity transform

- rejects an identity transform


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects an identity transform")
val receipt = candidate()
receipt.normalized_export_hash = receipt.source_export_hash
expect(receipt.candidate_diagnostic()).to_contain("IDENTITY-TRANSFORM")
```

</details>

#### rejects malformed hashes instead of treating labels as artifact identities

- rejects malformed hashes instead of treating labels as artifact identities


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects malformed hashes instead of treating labels as artifact identities")
val binary = candidate()
binary.normalizer_binary_hash = "normalizer-bin"
expect(binary.candidate_diagnostic()).to_contain("IDENTITY")
val source = candidate()
source.source_export_hash = "export-before"
expect(source.candidate_diagnostic()).to_contain("EXPORT")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/assurance/nat_normalizer_receipt_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering bounded Nat normalizer evidence.
- bounded Nat normalizer evidence

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
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

- Canonical SPipe generation for source `730fb7f60a4ba74153b9f732c36efa222e18ad30f29cb6ed51161654cc7ab94d`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `730fb7f60a4ba74153b9f732c36efa222e18ad30f29cb6ed51161654cc7ab94d`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `730fb7f60a4ba74153b9f732c36efa222e18ad30f29cb6ed51161654cc7ab94d`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/compiler/assurance/nat_normalizer_receipt_spec.spl
mirror: doc/06_spec/01_unit/compiler/assurance/nat_normalizer_receipt_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/assurance/nat_normalizer_receipt_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/assurance/nat_normalizer_receipt_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/assurance/nat_normalizer_receipt_spec.spl:24:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'binds the exact bounded candidate identity without calling it replay' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/assurance/nat_normalizer_receipt_spec.spl:33:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects native extensions even when an export was normalized' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/assurance/nat_normalizer_receipt_spec.spl:42:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects unbounded and nonexecuted candidate declarations' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

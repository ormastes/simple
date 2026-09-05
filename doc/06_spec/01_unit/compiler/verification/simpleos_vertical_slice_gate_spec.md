# Simpleos Vertical Slice Gate Specification

> Tests covering FV2 SimpleOS vertical-slice gate collector.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Simpleos Vertical Slice Gate Specification

## Scenarios

### FV2 SimpleOS vertical-slice gate collector

#### materializes seven source refinements and an aggregate receipt

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- materializes seven source refinements and an aggregate receipt
   - Expected: collection.gate_evidence.status.name() equals `passed`
   - Expected: collection.gate_evidence.receipt_hashes.len() equals `15`
   - Expected: collection.receipt_files.len() equals `15`
   - Expected: sha256_text(file.content) equals `file.receipt_hash`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("materializes seven source refinements and an aggregate receipt")
val collection = collect_simpleos_vertical_slice_gate_v1(
    complete_os_slice())
expect(collection.gate_evidence.status.name()).to_equal("passed")
expect(collection.gate_evidence.receipt_hashes.len()).to_equal(15)
expect(collection.receipt_files.len()).to_equal(15)
for file in collection.receipt_files:
    expect(sha256_text(file.content)).to_equal(file.receipt_hash)
```

</details>

#### rejects missing reordered or model-only subsystem evidence

- rejects missing reordered or model-only subsystem evidence


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("rejects missing reordered or model-only subsystem evidence")
var missing = complete_os_slice()
missing.pop()
expect(collect_simpleos_vertical_slice_gate_v1(
    missing).gate_evidence.diagnostic).to_contain("COUNT")
var reordered = complete_os_slice()
val temporary = reordered[0]
reordered[0] = reordered[1]
reordered[1] = temporary
expect(collect_simpleos_vertical_slice_gate_v1(
    reordered).gate_evidence.diagnostic).to_contain("ORDER")
var model_only = complete_os_slice()
model_only[2].status = FormalStatus.ModelProven
expect(collect_simpleos_vertical_slice_gate_v1(
    model_only).gate_evidence.diagnostic).to_contain("STATUS")
```

</details>

#### rejects stale source material artifact drift and duplicate proof roots

- rejects stale source material artifact drift and duplicate proof roots


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("rejects stale source material artifact drift and duplicate proof roots")
var stale = complete_os_slice()
stale[3].source_receipt_content = "changed"
expect(collect_simpleos_vertical_slice_gate_v1(
    stale).gate_evidence.diagnostic).to_contain("RECEIPT")
var drift = complete_os_slice()
drift[4].axiom_report_artifact_hash = sha256_text("other-artifact")
expect(collect_simpleos_vertical_slice_gate_v1(
    drift).gate_evidence.diagnostic).to_contain("ARTIFACT")
var duplicate = complete_os_slice()
duplicate[6].proof.proof_root = duplicate[5].proof.proof_root
expect(collect_simpleos_vertical_slice_gate_v1(
    duplicate).gate_evidence.status.name()).to_equal("failed")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/verification/simpleos_vertical_slice_gate_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering FV2 SimpleOS vertical-slice gate collector.
- FV2 SimpleOS vertical-slice gate collector

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

- Canonical SPipe generation for source `ef822edb0b947be18e8485460590fbceb71e38e4af0ee0edade9b2bdfbc361a2`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `ef822edb0b947be18e8485460590fbceb71e38e4af0ee0edade9b2bdfbc361a2`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `ef822edb0b947be18e8485460590fbceb71e38e4af0ee0edade9b2bdfbc361a2`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/01_unit/compiler/verification/simpleos_vertical_slice_gate_spec.spl
mirror: doc/06_spec/01_unit/compiler/verification/simpleos_vertical_slice_gate_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/verification/simpleos_vertical_slice_gate_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/verification/simpleos_vertical_slice_gate_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/verification/simpleos_vertical_slice_gate_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/verification/simpleos_vertical_slice_gate_spec.spl:76:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'materializes seven source refinements and an aggregate receipt' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/verification/simpleos_vertical_slice_gate_spec.spl:87:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects missing reordered or model-only subsystem evidence' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/verification/simpleos_vertical_slice_gate_spec.spl:105:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects stale source material artifact drift and duplicate proof roots' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

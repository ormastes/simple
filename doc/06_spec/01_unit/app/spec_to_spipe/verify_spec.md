# Verify Specification

> Tests covering Spec-to-SPipe Phase 0 verification gates, REQ-S2S-COV-001: exact source coverage, REQ-S2S-REC-001: explicit tolerant-parser recovery, REQ-S2S-ID-001: reproducible manifest identity.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Verify Specification

## Scenarios

### Spec-to-SPipe Phase 0 verification gates

### REQ-S2S-COV-001: exact source coverage

#### should accept adjacent spans that account for every source byte
#### should reject a dropped byte range

- should reject a dropped byte range
- Leave bytes 4 through 6 absent from the ledger
   - Expected: result.accepted is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("should reject a dropped byte range")
step("Leave bytes 4 through 6 absent from the ledger")
val result = verify_exact_coverage(10, [
    ledger_span(0, 4, SpecDisposition.Normative),
    ledger_span(6, 10, SpecDisposition.Normative)])
expect(result.accepted).to_equal(false)
expect(result.rule_ids).to_contain("SPEC-COV-004")
```

</details>

#### should reject overlapping bytes and an unreasoned exclusion

- should reject overlapping bytes and an unreasoned exclusion
- Overlap two entries and omit the exclusion rationale


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("should reject overlapping bytes and an unreasoned exclusion")
step("Overlap two entries and omit the exclusion rationale")
val result = verify_exact_coverage(10, [
    ledger_span(0, 7, SpecDisposition.Normative),
    ledger_span(6, 10, SpecDisposition.Unsupported)])
expect(result.rule_ids).to_contain("SPEC-COV-003")
expect(result.rule_ids).to_contain("SPEC-COV-006")
```

</details>

### REQ-S2S-REC-001: explicit tolerant-parser recovery

#### should accept a source-preserving manifest-approved recovery

- should accept a source-preserving manifest-approved recovery
- Verify a diagnostic-bearing ErrorNode recovery in compatibility mode
   - Expected: result.accepted is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("should accept a source-preserving manifest-approved recovery")
step("Verify a diagnostic-bearing ErrorNode recovery in compatibility mode")
val child = SpecErrorNode(node_kind: "bad-cell",
    source_span: SourceSpan(byte_start: 2, byte_end: 4),
    raw_source: "br", adapter_rule_id: "MD-TABLE-001",
    diagnostic_id: "diag-child", recovered: true, children: [], extensions: [])
val result = verify_no_silent_recovery([
    error_node("MD-TABLE-001", children: [child])], false, ["MD-TABLE-001"])
expect(result.accepted).to_equal(true)
```

</details>

#### should reject every recovery in strict mode

- should reject every recovery in strict mode
- Submit an otherwise valid recovery to strict mode


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("should reject every recovery in strict mode")
step("Submit an otherwise valid recovery to strict mode")
val result = verify_no_silent_recovery([
    error_node("MD-TABLE-001")], true, ["MD-TABLE-001"])
expect(result.rule_ids).to_contain("SPEC-REC-006")
```

</details>

#### should reject silent or unapproved recovery

- should reject silent or unapproved recovery
- Omit diagnostic evidence and manifest approval


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("should reject silent or unapproved recovery")
step("Omit diagnostic evidence and manifest approval")
val result = verify_no_silent_recovery([
    error_node("MD-UNKNOWN-999", diagnostic_id: "")], false, ["MD-TABLE-001"])
expect(result.rule_ids).to_contain("SPEC-REC-004")
expect(result.rule_ids).to_contain("SPEC-REC-007")
```

</details>

### REQ-S2S-ID-001: reproducible manifest identity

#### should accept a fully pinned matching identity

- should accept a fully pinned matching identity
- Compare the manifest with the selected version and observed source hash
   - Expected: result.accepted is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("should accept a fully pinned matching identity")
step("Compare the manifest with the selected version and observed source hash")
val value = manifest()
val result = verify_manifest_identity(value, "1.0", value.source.source_sha256)
expect(result.accepted).to_equal(true)
```

</details>

#### should reject an unknown schema and stale source hash

- should reject an unknown schema and stale source hash
- Verify the manifest against a newer schema and different observed bytes


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("should reject an unknown schema and stale source hash")
step("Verify the manifest against a newer schema and different observed bytes")
var value = manifest()
value.schema_version = 99
val result = verify_manifest_identity(value, "1.0", SHA_B)
expect(result.rule_ids).to_contain("SPEC-ID-001")
expect(result.rule_ids).to_contain("SPEC-ID-006")
```

</details>

#### should reject a floating or stale published version

- should reject a floating or stale published version
- Use a floating published version where a pinned version is required


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("should reject a floating or stale published version")
step("Use a floating published version where a pinned version is required")
val value = manifest(version: "latest")
val result = verify_manifest_identity(value, "1.0", value.source.source_sha256)
expect(result.rule_ids).to_contain("SPEC-ID-003")
expect(result.rule_ids).to_contain("SPEC-ID-004")
```

</details>

#### should reject malformed digest identity

- should reject malformed digest identity
- Use a digest that cannot identify immutable source bytes


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("should reject malformed digest identity")
step("Use a digest that cannot identify immutable source bytes")
var value = manifest()
value.source.source_sha256 = "not-a-sha"
val result = verify_manifest_identity(value, "1.0", "not-a-sha")
expect(result.rule_ids).to_contain("SPEC-ID-005")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/spec_to_spipe/verify_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Spec-to-SPipe Phase 0 verification gates, REQ-S2S-COV-001: exact source coverage, REQ-S2S-REC-001: explicit tolerant-parser recovery, REQ-S2S-ID-001: reproducible manifest identity.
- Spec-to-SPipe Phase 0 verification gates
- REQ-S2S-COV-001: exact source coverage
- REQ-S2S-REC-001: explicit tolerant-parser recovery
- REQ-S2S-ID-001: reproducible manifest identity

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

- `REQ-SSPEC-APP`
- `REQ-S2S-COV-001`
- `REQ-S2S-REC-001`
- `REQ-S2S-ID-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `ebe505f9e2b484260f9ab71bfdaa9d5f98979c1941bcdec086d2ef4095b7bf46`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `ebe505f9e2b484260f9ab71bfdaa9d5f98979c1941bcdec086d2ef4095b7bf46`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `ebe505f9e2b484260f9ab71bfdaa9d5f98979c1941bcdec086d2ef4095b7bf46`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **81/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/app/spec_to_spipe/verify_spec.spl
mirror: doc/06_spec/01_unit/app/spec_to_spipe/verify_spec.md (current)
findings: 12 blockers: 1
  narrative=100 structure=60 oracle=100
  traceability=60 evidence=70 coverage=100 maintainability=80
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=81; blocker cap makes effective=49
doc/06_spec/01_unit/app/spec_to_spipe/verify_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/spec_to_spipe/verify_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 3 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/app/spec_to_spipe/verify_spec.spl:51:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'should accept adjacent spans that account for every source byte' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/01_unit/app/spec_to_spipe/verify_spec.spl:51:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should accept adjacent spans that account for every source byte' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/app/spec_to_spipe/verify_spec.spl:65:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should reject a dropped byte range' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/app/spec_to_spipe/verify_spec.spl:65:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should reject a dropped byte range' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/spec_to_spipe/verify_spec.spl:75:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should reject overlapping bytes and an unreasoned exclusion' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/app/spec_to_spipe/verify_spec.spl:75:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should reject overlapping bytes and an unreasoned exclusion' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/spec_to_spipe/verify_spec.spl:86:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should accept a source-preserving manifest-approved recovery' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/app/spec_to_spipe/verify_spec.spl:86:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should accept a source-preserving manifest-approved recovery' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/spec_to_spipe/verify_spec.spl:98:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should reject every recovery in strict mode' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/app/spec_to_spipe/verify_spec.spl:106:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should reject silent or unapproved recovery' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->

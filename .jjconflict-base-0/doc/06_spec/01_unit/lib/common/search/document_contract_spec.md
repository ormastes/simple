# Document Contract Specification

> Tests covering canonical and scoped search documents.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Document Contract Specification

## Scenarios

### canonical and scoped search documents

#### requires the five weighted canonical fields in order

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- requires the five weighted canonical fields in order
- Validate canonical field contract
   - Expected: SearchDocumentV1.of("a", "r", fields, [], "sha256:v", "sha256:c").has_canonical_field_contract() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("requires the five weighted canonical fields in order")
step("Validate canonical field contract")
val fields = [SearchField.of("identifier", "a", 4000), SearchField.of("title", "t", 4000), SearchField.of("heading", "h", 2500), SearchField.of("classification", "c", 2000), SearchField.of("body", "b", 1000)]
expect(SearchDocumentV1.of("a", "r", fields, [], "sha256:v", "sha256:c").has_canonical_field_contract()).to_equal(true)
```

</details>

#### binds a scoped document to exactly one authorization scope

- binds a scoped document to exactly one authorization scope
- Validate scope digest binding
   - Expected: doc.is_bound_to(scope) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("binds a scoped document to exactly one authorization scope")
step("Validate scope digest binding")
val scope = SearchScopeV1.of("p", "w", "r", "1", "sha256:p", [], [], ["body"], [], "sha256:s")
val doc = ScopedSearchDocumentV1.of("a", "r", [ScopedFieldV1.of("body", "x")], [], "sha256:v", "sha256:c", "sha256:s")
expect(doc.is_bound_to(scope)).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/search/document_contract_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering canonical and scoped search documents.
- canonical and scoped search documents

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
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

- Canonical SPipe generation for source `c7889ffea66527bbd99850efc0e8ab58e14f65695e667965f01c4df637b0efa5`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `c7889ffea66527bbd99850efc0e8ab58e14f65695e667965f01c4df637b0efa5`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `c7889ffea66527bbd99850efc0e8ab58e14f65695e667965f01c4df637b0efa5`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **94/100**; effective score: **94/100**; blockers: **0**.

SSpec documentization score: 94/100
source: test/01_unit/lib/common/search/document_contract_spec.spl
mirror: doc/06_spec/01_unit/lib/common/search/document_contract_spec.md (current)
findings: 4 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/common/search/document_contract_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/search/document_contract_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/search/document_contract_spec.spl:12:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'requires the five weighted canonical fields in order' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/search/document_contract_spec.spl:19:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'binds a scoped document to exactly one authorization scope' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

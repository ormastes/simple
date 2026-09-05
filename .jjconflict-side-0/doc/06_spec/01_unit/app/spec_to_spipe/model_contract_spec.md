# Model Contract Specification

> Tests covering Spec-to-SPipe Phase-0 manifest contract.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Model Contract Specification

## Scenarios

### Spec-to-SPipe Phase-0 manifest contract

#### pins immutable source bytes and accepts the supported schema

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-S2S-004
```

</details>

#### rejects unknown schema versions without coercion

- rejects unknown schema versions without coercion
   - Expected: manifest_error_code(manifest) equals `unsupported-version`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("rejects unknown schema versions without coercion")
var manifest = sample_manifest()
manifest.schema_version = 99
expect(manifest_error_code(manifest)).to_equal("unsupported-version")
```

</details>

#### rejects stale source hashes

- rejects stale source hashes
   - Expected: manifest_error_code(manifest) equals `stale-hash`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("rejects stale source hashes")
var manifest = sample_manifest()
manifest.source.source_sha256 = "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"
expect(manifest_error_code(manifest)).to_equal("stale-hash")
```

</details>

#### preserves namespaced adapter extensions in deterministic serialization

- preserves namespaced adapter extensions in deterministic serialization
   - Expected: first equals `second`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("preserves namespaced adapter extensions in deterministic serialization")
val manifest = sample_manifest()
val first = canonical_text(manifest)
val second = canonical_text(manifest)
expect(first).to_equal(second)
expect(first).to_contain("org.example.adapter")
expect(first).to_contain("dialect")
expect(first).to_contain("example-v1")
```

</details>

#### rejects adapter data without a namespaced extension

- rejects adapter data without a namespaced extension
   - Expected: manifest_error_code(manifest) equals `invalid-extension-namespace`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("rejects adapter data without a namespaced extension")
var manifest = sample_manifest()
manifest.extensions = [SpecExtensionField(namespace: "markdown", key: "dialect", value: "x")]
expect(manifest_error_code(manifest)).to_equal("invalid-extension-namespace")
```

</details>

#### selects semantic identity by the frozen priority order

- selects semantic identity by the frozen priority order
   - Expected: identity equals `upstream:clause-7`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("selects semantic identity by the frozen priority order")
val identity = choose_spec_semantic_identity(SpecSemanticIdentityInput(
    upstream_id: "clause-7",
    registry_id: "registry-2",
    structural_path: "section/7",
    adapter_semantic_key: "adapter-7",
    content_fingerprint: "body",
    neighborhood_fingerprint: "neighbors"
))
expect(identity).to_equal("upstream:clause-7")
```

</details>

#### accepts only manifest-approved tolerant recovery

- accepts only manifest-approved tolerant recovery
   - Expected: manifest_valid(manifest) is true
   - Expected: manifest_error_code(manifest) equals `unapproved-recovery`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("accepts only manifest-approved tolerant recovery")
var manifest = sample_manifest()
manifest.approved_recovery_rule_ids = ["MD-RECOVERY-001"]
manifest.diagnostics = [SpecImportDiagnostic(
    diagnostic_id: "diag-1",
    severity: "warning",
    adapter_rule_id: "MD-RECOVERY-001",
    message: "recovered malformed table",
    source_span: SourceSpan(byte_start: 1, byte_end: 2),
    recovered: true,
    extensions: []
)]
expect(manifest_valid(manifest)).to_equal(true)
manifest.approved_recovery_rule_ids = []
expect(manifest_error_code(manifest)).to_equal("unapproved-recovery")
```

</details>

#### rejects all parser recovery in strict mode

- rejects all parser recovery in strict mode
   - Expected: manifest_error_code(manifest) equals `strict-recovery`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("rejects all parser recovery in strict mode")
var manifest = sample_manifest()
manifest.strict_mode = true
manifest.approved_recovery_rule_ids = ["MD-RECOVERY-001"]
manifest.diagnostics = [SpecImportDiagnostic(
    diagnostic_id: "diag-1",
    severity: "error",
    adapter_rule_id: "MD-RECOVERY-001",
    message: "malformed table",
    source_span: SourceSpan(byte_start: 1, byte_end: 2),
    recovered: true,
    extensions: []
)]
expect(manifest_error_code(manifest)).to_equal("strict-recovery")
```

</details>

#### retains nested malformed nodes inside their parent source span

- retains nested malformed nodes inside their parent source span
   - Expected: manifest_valid(manifest) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("retains nested malformed nodes inside their parent source span")
var manifest = sample_manifest()
manifest.approved_recovery_rule_ids = ["MD-TABLE-001"]
val child = SpecErrorNode(node_kind: "table-cell",
    source_span: SourceSpan(byte_start: 1, byte_end: 2),
    raw_source: "b", adapter_rule_id: "MD-TABLE-001",
    diagnostic_id: "diag-child", recovered: true, children: [],
    extensions: [])
manifest.error_nodes = [SpecErrorNode(node_kind: "table",
    source_span: SourceSpan(byte_start: 0, byte_end: 3),
    raw_source: "abc", adapter_rule_id: "MD-TABLE-001",
    diagnostic_id: "diag-parent", recovered: true, children: [child],
    extensions: [])]
expect(manifest_valid(manifest)).to_equal(true)
expect(canonical_text(manifest)).to_contain("diag-child")
```

</details>

#### rejects a nested malformed node outside its parent span

- rejects a nested malformed node outside its parent span
   - Expected: manifest_error_code(manifest) equals `invalid-span`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("rejects a nested malformed node outside its parent span")
var manifest = sample_manifest()
manifest.approved_recovery_rule_ids = ["MD-TABLE-001"]
val child = SpecErrorNode(node_kind: "table-cell",
    source_span: SourceSpan(byte_start: 2, byte_end: 3),
    raw_source: "c", adapter_rule_id: "MD-TABLE-001",
    diagnostic_id: "diag-child", recovered: true, children: [],
    extensions: [])
manifest.error_nodes = [SpecErrorNode(node_kind: "table",
    source_span: SourceSpan(byte_start: 0, byte_end: 2),
    raw_source: "ab", adapter_rule_id: "MD-TABLE-001",
    diagnostic_id: "diag-parent", recovered: true, children: [child],
    extensions: [])]
expect(manifest_error_code(manifest)).to_equal("invalid-span")
```

</details>

#### reports exact byte coverage from non-overlapping ledger spans

- reports exact byte coverage from non-overlapping ledger spans
   - Expected: report.exact_coverage is true
   - Expected: report.accounted_source_bytes equals `3`
   - Expected: report.total_source_bytes equals `3`
   - Expected: report.passed is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("reports exact byte coverage from non-overlapping ledger spans")
val report = verify_spec_import_manifest(sample_manifest())
expect(report.exact_coverage).to_equal(true)
expect(report.accounted_source_bytes).to_equal(3)
expect(report.total_source_bytes).to_equal(3)
expect(report.passed).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/spec_to_spipe/model_contract_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Spec-to-SPipe Phase-0 manifest contract.
- Spec-to-SPipe Phase-0 manifest contract

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 11 |
| Active scenarios | 11 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-APP`
- `REQ-S2S-004`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `38342a33b48d567f158a7c45415278fda5c2c5b1de8c3c577b12b57999e6d7b1`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `38342a33b48d567f158a7c45415278fda5c2c5b1de8c3c577b12b57999e6d7b1`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `38342a33b48d567f158a7c45415278fda5c2c5b1de8c3c577b12b57999e6d7b1`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **87/100**; effective score: **87/100**; blockers: **0**.

SSpec documentization score: 87/100
source: test/01_unit/app/spec_to_spipe/model_contract_spec.spl
mirror: doc/06_spec/01_unit/app/spec_to_spipe/model_contract_spec.md (current)
findings: 7 blockers: 0
  narrative=100 structure=90 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/app/spec_to_spipe/model_contract_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/spec_to_spipe/model_contract_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/spec_to_spipe/model_contract_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/app/spec_to_spipe/model_contract_spec.spl:95:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'pins immutable source bytes and accepts the supported schema' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/01_unit/app/spec_to_spipe/model_contract_spec.spl:104:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects unknown schema versions without coercion' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/spec_to_spipe/model_contract_spec.spl:111:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects stale source hashes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/spec_to_spipe/model_contract_spec.spl:118:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'preserves namespaced adapter extensions in deterministic serialization' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

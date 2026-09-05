# Explain Contract Specification

> Tests covering closed BM25 explanation.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Explain Contract Specification

## Scenarios

### closed BM25 explanation

#### binds score, root, scope, and deterministic tie key

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- binds score, root, scope, and deterministic tie key
- Construct the closed explanation record
   - Expected: explanation.fields.len() equals `1`
   - Expected: explanation.tie_key_utf8_hex equals `61`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("binds score, root, scope, and deterministic tie key")
step("Construct the closed explanation record")
val field = FieldExplanationV1(field: "body", document_count: 1, total_length: 2, average_length_scaled: "2000000", document_length: 2, weight_milli: 1000, field_total: "10")
val explanation = SearchExplanationV1(contract: "bm25-explain-v1", analyzer: "spipe-unicode-lex-v1", score_contract: "bm25-fixed-v1", logical_index: "spipe-lexical-snapshot-v1", scope_digest: "sha256:s", logical_root: "sha256:r", document_id: "a", fields: [field], internal_total: "10", public_score_milli: 0, tie_key_utf8_hex: "61")
expect(explanation.fields.len()).to_equal(1)
expect(explanation.tie_key_utf8_hex).to_equal("61")
```

</details>

#### emits exact normative BM25 term intermediates

- emits exact normative BM25 term intermediates
- Check the fixed evaluation sequence against golden integers
   - Expected: trace.average_length_scaled equals `6000000`
   - Expected: trace.ratio_scaled equals `1000000`
   - Expected: trace.norm_scaled equals `1000000`
   - Expected: trace.denominator_scaled equals `2200000`
   - Expected: trace.tf_scaled equals `1000000`
   - Expected: trace.idf_argument_scaled equals `1600000`
   - Expected: trace.idf_scaled equals `469998`
   - Expected: trace.unweighted equals `469998`
   - Expected: trace.weighted equals `469998`
   - Expected: trace.weighted_decimal() equals `469998`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("emits exact normative BM25 term intermediates")
step("Check the fixed evaluation sequence against golden integers")
val trace = bm25_term_checked_trace(1, 6, 18, 3, 2, 1000).unwrap()
expect(trace.average_length_scaled).to_equal(6000000)
expect(trace.ratio_scaled).to_equal(1000000)
expect(trace.norm_scaled).to_equal(1000000)
expect(trace.denominator_scaled).to_equal(2200000)
expect(trace.tf_scaled).to_equal(1000000)
expect(trace.idf_argument_scaled).to_equal(1600000)
expect(trace.idf_scaled).to_equal(469998)
expect(trace.unweighted).to_equal(469998)
expect(trace.weighted).to_equal(469998)
expect(trace.weighted_decimal()).to_equal("469998")
```

</details>

#### rejects an intermediate that cannot be represented identically in i64

- rejects an intermediate that cannot be represented identically in i64
- Fail closed instead of wrapping conceptual i128 arithmetic
   - Expected: bm25_term_checked_trace(10000000000000, 6, 18, 3, 2, 4000).is_ok() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects an intermediate that cannot be represented identically in i64")
step("Fail closed instead of wrapping conceptual i128 arithmetic")
expect(bm25_term_checked_trace(10000000000000, 6, 18, 3, 2, 4000).is_ok()).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/search/explain_contract_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering closed BM25 explanation.
- closed BM25 explanation

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

- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `cd68d085d54192ba27c724d64f5090aa16e2186db94e6ab8d1aadf082fe7586c`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `cd68d085d54192ba27c724d64f5090aa16e2186db94e6ab8d1aadf082fe7586c`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `cd68d085d54192ba27c724d64f5090aa16e2186db94e6ab8d1aadf082fe7586c`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/lib/common/search/explain_contract_spec.spl
mirror: doc/06_spec/01_unit/lib/common/search/explain_contract_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/common/search/explain_contract_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/search/explain_contract_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/search/explain_contract_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 10 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/common/search/explain_contract_spec.spl:17:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'binds score, root, scope, and deterministic tie key' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/search/explain_contract_spec.spl:26:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'emits exact normative BM25 term intermediates' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/search/explain_contract_spec.spl:42:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects an intermediate that cannot be represented identically in i64' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

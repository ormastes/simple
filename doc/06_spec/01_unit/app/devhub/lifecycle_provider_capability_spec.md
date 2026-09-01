# lifecycle_provider_capability_spec

> Provider capability records preserve strict review semantics.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# lifecycle_provider_capability_spec

Provider capability records preserve strict review semantics.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/devhub/lifecycle_provider_capability_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Provider capability records preserve strict review semantics.

## Scenarios

### DevHub provider capabilities

#### refuses to flatten request-changes under strict synchronization

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- refuses to flatten request-changes under strict synchronization
- Discover provider review semantics
   - Expected: provider_review_operation(comment_only_provider(), "approve", true).status equals `provider_operation_supported`
   - Expected: provider_review_operation(comment_only_provider(), "request_changes", true).code equals `PROVIDER_SEMANTIC_GAP`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("refuses to flatten request-changes under strict synchronization")
step("Discover provider review semantics")
expect(provider_review_operation(comment_only_provider(), "approve", true).status).to_equal("provider_operation_supported")
expect(provider_review_operation(comment_only_provider(), "request_changes", true).code).to_equal("PROVIDER_SEMANTIC_GAP")
```

</details>

#### labels a non-strict comment projection as non-equivalent

- labels a non-strict comment projection as non-equivalent
   - Expected: provider_review_operation(comment_only_provider(), "request_changes", false).status equals `local_blocking_remote_comment_non_equivalent`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("labels a non-strict comment projection as non-equivalent")
expect(provider_review_operation(comment_only_provider(), "request_changes", false).status).to_equal("local_blocking_remote_comment_non_equivalent")
```

</details>

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
- `REQ-004`
- `REQ-SSPEC-APP`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `3b8ead195dd86935d75e64bd44332c7d8670983f5bcdaa50a2c74352ee8d9511`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `3b8ead195dd86935d75e64bd44332c7d8670983f5bcdaa50a2c74352ee8d9511`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `3b8ead195dd86935d75e64bd44332c7d8670983f5bcdaa50a2c74352ee8d9511`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/app/devhub/lifecycle_provider_capability_spec.spl
mirror: doc/06_spec/01_unit/app/devhub/lifecycle_provider_capability_spec.md (current)
findings: 5 blockers: 1
  narrative=100 structure=100 oracle=100
  traceability=60 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=88; blocker cap makes effective=49
doc/06_spec/01_unit/app/devhub/lifecycle_provider_capability_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/devhub/lifecycle_provider_capability_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/devhub/lifecycle_provider_capability_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 2 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/app/devhub/lifecycle_provider_capability_spec.spl:27:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'refuses to flatten request-changes under strict synchronization' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/devhub/lifecycle_provider_capability_spec.spl:34:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'labels a non-strict comment projection as non-equivalent' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

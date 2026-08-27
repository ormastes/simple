# SMF note.sdn Instantiation Tracking

> Tests the note.sdn section in SMF (Simple Module Format) for tracking generic instantiation metadata. The feature enables tracking which generic types and functions have been instantiated during compilation.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# SMF note.sdn Instantiation Tracking

Tests the note.sdn section in SMF (Simple Module Format) for tracking generic instantiation metadata. The feature enables tracking which generic types and functions have been instantiated during compilation.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #GENERIC-002 |
| Category | Compiler |
| Status | In Progress |
| Source | `test/feature/usage/note_sdn_feature_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests the note.sdn section in SMF (Simple Module Format) for tracking generic
instantiation metadata. The feature enables tracking which generic
types and functions have been instantiated during compilation.

## Syntax

```simple
# note.sdn records generic instantiations
# e.g., List<Int> instantiated at line 42
```

## Scenarios

### SMF note.sdn Instantiation Tracking

#### tracks generic instantiation metadata

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- tracks generic instantiation metadata
   - Expected: true is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("tracks generic instantiation metadata")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
# Placeholder — real SMF note.sdn tracking tests go here
expect(true).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-FEATURE`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `f32481d0f337ec30f3ae2a3f4cdc39e4bb10dc9366d4296628f8dccc25daf509`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `f32481d0f337ec30f3ae2a3f4cdc39e4bb10dc9366d4296628f8dccc25daf509`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `f32481d0f337ec30f3ae2a3f4cdc39e4bb10dc9366d4296628f8dccc25daf509`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **87/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/feature/usage/note_sdn_feature_spec.spl
mirror: doc/06_spec/feature/usage/note_sdn_feature_spec.md (current)
findings: 3 blockers: 1
  narrative=100 structure=100 oracle=50
  traceability=100 evidence=100 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=87; blocker cap makes effective=49
doc/06_spec/feature/usage/note_sdn_feature_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/feature/usage/note_sdn_feature_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/feature/usage/note_sdn_feature_spec.spl:1:1: blocker SSDOC-ORA-001 [oracle] (-50): no real executed assertion or compiler oracle
  why: A passing-looking document without an oracle is not conformance evidence.
  improve: Replace placeholders with an observable production assertion.
<!-- sspec-maintain:scorecard:end -->

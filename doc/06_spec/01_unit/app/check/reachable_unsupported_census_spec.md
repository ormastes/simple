# Reachable Unsupported Census Specification

> Tests covering reachable-unsupported census classifier.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Reachable Unsupported Census Specification

## Scenarios

### reachable-unsupported census classifier

#### strips surrounding quotes and leaves bare tokens alone

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- strips surrounding quotes and leaves bare tokens alone
   - Expected: strip_quotes("\"Unsupported(no arm)\"") equals `Unsupported(no arm)`
   - Expected: strip_quotes("unsupported") equals `unsupported`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("strips surrounding quotes and leaves bare tokens alone")
expect(strip_quotes("\"Unsupported(no arm)\"")).to_equal("Unsupported(no arm)")
expect(strip_quotes("unsupported")).to_equal("unsupported")
```

</details>

#### reads a field value and ignores lines that are a different key

- reads a field value and ignores lines that are a different key
   - Expected: field_value("  state: unsupported", "state") equals `unsupported`
   - Expected: field_value("  reason: \"no arm\"", "reason") equals `no arm`
   - Expected: field_value("  state: unsupported", "from") equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reads a field value and ignores lines that are a different key")
expect(field_value("  state: unsupported", "state")).to_equal("unsupported")
expect(field_value("  reason: \"no arm\"", "reason")).to_equal("no arm")
expect(field_value("  state: unsupported", "from")).to_equal("")
```

</details>

#### takes the variant name after the last dot, mirroring variant_name_of

- takes the variant name after the last dot, mirroring variant_name_of
   - Expected: last_segment("MirInstKind.AcquireSnapshot") equals `AcquireSnapshot`
   - Expected: last_segment("Alpha") equals `Alpha`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("takes the variant name after the last dot, mirroring variant_name_of")
expect(last_segment("MirInstKind.AcquireSnapshot")).to_equal("AcquireSnapshot")
expect(last_segment("Alpha")).to_equal("Alpha")
```

</details>

#### recognises both the bare and the parameterised unsupported spelling

- recognises both the bare and the parameterised unsupported spelling
   - Expected: state_is_unsupported("unsupported") is true
   - Expected: state_is_unsupported("\"Unsupported(no arm)\"") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("recognises both the bare and the parameterised unsupported spelling")
expect(state_is_unsupported("unsupported")).to_equal(true)
expect(state_is_unsupported("\"Unsupported(no arm)\"")).to_equal(true)
```

</details>

#### does not treat implemented, normalized or notapplicable as unsupported

- does not treat implemented, normalized or notapplicable as unsupported
   - Expected: state_is_unsupported("implemented") is false
   - Expected: state_is_unsupported("\"Normalized(target)\"") is false
   - Expected: state_is_unsupported("\"NotApplicable(never allocated)\"") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does not treat implemented, normalized or notapplicable as unsupported")
expect(state_is_unsupported("implemented")).to_equal(false)
expect(state_is_unsupported("\"Normalized(target)\"")).to_equal(false)
expect(state_is_unsupported("\"NotApplicable(never allocated)\"")).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/check/reachable_unsupported_census_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering reachable-unsupported census classifier.
- reachable-unsupported census classifier

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

- Canonical SPipe generation for source `f517ae75bf1342ea4b176ae7c84bfe9726e67bc10bd59e4763fa75bb9ea448c9`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `f517ae75bf1342ea4b176ae7c84bfe9726e67bc10bd59e4763fa75bb9ea448c9`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `f517ae75bf1342ea4b176ae7c84bfe9726e67bc10bd59e4763fa75bb9ea448c9`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/app/check/reachable_unsupported_census_spec.spl
mirror: doc/06_spec/01_unit/app/check/reachable_unsupported_census_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/app/check/reachable_unsupported_census_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/check/reachable_unsupported_census_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/check/reachable_unsupported_census_spec.spl:23:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'strips surrounding quotes and leaves bare tokens alone' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/check/reachable_unsupported_census_spec.spl:29:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reads a field value and ignores lines that are a different key' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/check/reachable_unsupported_census_spec.spl:36:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'takes the variant name after the last dot, mirroring variant_name_of' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

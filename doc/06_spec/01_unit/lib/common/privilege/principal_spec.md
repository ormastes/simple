# Principal Specification

> Principal kind validation — local principal default; non-local rejected.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Principal Specification

Principal kind validation — local principal default; non-local rejected.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Red (no impl yet) |
| Source | `test/01_unit/lib/common/privilege/principal_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Principal kind validation — local principal default; non-local rejected.

## Scenarios

### Principal

### kinds

#### AC-1: default principal is Local

- AC-1: default principal is Local


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-1: default principal is Local")
val p = Principal.default_local("alice")
expect principal_is_local(p) to_equal true
```

</details>

#### AC-1: local principal passes validation

- AC-1: local principal passes validation


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-1: local principal passes validation")
val p = Principal(kind: PrincipalKind.Local, id: "alice")
val result = principal_validate(p)
expect result.ok to_equal true
```

</details>

#### AC-1: non-local principal is rejected in this release

- AC-1: non-local principal is rejected in this release


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-1: non-local principal is rejected in this release")
val p = Principal(kind: PrincipalKind.Remote, id: "host:alice")
val result = principal_validate(p)
expect result.ok to_equal false
```

</details>

#### AC-1: non-local principal_is_local returns false

- AC-1: non-local principal_is_local returns false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-1: non-local principal_is_local returns false")
val p = Principal(kind: PrincipalKind.Remote, id: "host:alice")
expect principal_is_local(p) to_equal false
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
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

- Canonical SPipe generation for source `3316b21d819519dd9525911a16db874597ace7abdc690eab7dd54334349fe1c3`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `3316b21d819519dd9525911a16db874597ace7abdc690eab7dd54334349fe1c3`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `3316b21d819519dd9525911a16db874597ace7abdc690eab7dd54334349fe1c3`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/common/privilege/principal_spec.spl
mirror: doc/06_spec/01_unit/lib/common/privilege/principal_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/common/privilege/principal_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/privilege/principal_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/privilege/principal_spec.spl:23:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AC-1: default principal is Local' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/privilege/principal_spec.spl:29:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AC-1: local principal passes validation' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/privilege/principal_spec.spl:36:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AC-1: non-local principal is rejected in this release' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

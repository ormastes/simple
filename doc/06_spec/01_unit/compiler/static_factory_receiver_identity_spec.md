# Static factory receiver identity

> Pins the small language contract behind the Stage 3 `BackendError.runtime_error`

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Static factory receiver identity

Pins the small language contract behind the Stage 3 `BackendError.runtime_error`

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/static_factory_receiver_identity_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Pins the small language contract behind the Stage 3 `BackendError.runtime_error`
failure: two adjacent static factories on one owner must resolve without
lowering the type name as a runtime value.

## Scenarios

### static factory receiver identity

#### keeps the owner for the runtime_error-shaped factory

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
```

</details>

#### keeps the owner for an adjacent static factory

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val error = UnitFactoryError.type_error("typed")
expect(error.message).to_equal("typed")
expect(error.code).to_equal(23)
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
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `362cd23abfa5d3ce9dc5cd41e26f8404bf22539d588fea042adc916c86951493`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `362cd23abfa5d3ce9dc5cd41e26f8404bf22539d588fea042adc916c86951493`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `362cd23abfa5d3ce9dc5cd41e26f8404bf22539d588fea042adc916c86951493`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/01_unit/compiler/static_factory_receiver_identity_spec.spl
mirror: doc/06_spec/01_unit/compiler/static_factory_receiver_identity_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=80 oracle=90
  traceability=100 evidence=100 coverage=100 maintainability=55
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/static_factory_receiver_identity_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/static_factory_receiver_identity_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/static_factory_receiver_identity_spec.spl:1:1: advice SSDOC-MNT-001 [maintainability] (-15): multiple scenarios form a flat, unfolded presentation
  why: Long flat dumps obscure the primary workflow.
  improve: Group secondary detail and keep the primary workflow visible.
test/01_unit/compiler/static_factory_receiver_identity_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/static_factory_receiver_identity_spec.spl:31:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'keeps the owner for the runtime_error-shaped factory' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/01_unit/compiler/static_factory_receiver_identity_spec.spl:38:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'keeps the owner for an adjacent static factory' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
<!-- sspec-maintain:scorecard:end -->

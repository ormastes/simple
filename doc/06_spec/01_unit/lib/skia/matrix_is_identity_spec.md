# Matrix3x3.is_identity

> Regression + detection specs for

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Matrix3x3.is_identity

Regression + detection specs for

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/skia/matrix_is_identity_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Regression + detection specs for
`doc/08_tracking/bug/skia_matrix3x3_missing_is_identity_2026-07-20.md`.

(a) reproducing spec: `Matrix3x3` (re-exported by `std.skia.entity.matrix`
    from `std.common.drawing.vector`) had no `is_identity()` at all, so the
    5 examples in `matrix_spec.spl` that call it could not run.
(b) detection spec: generalises the class — a predicate over a 9-element
    matrix must be sensitive to EVERY element, not just the ones the happy
    path happens to touch.

## Scenarios

### Matrix3x3.is_identity

#### returns true for the identity and for identity-equivalent factories

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
```

</details>

#### returns false for a translation

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(Matrix3x3.translate(tx: 10.0, ty: 20.0).is_identity()).to_equal(false)
```

</details>

### Matrix3x3.is_identity element sensitivity (detection)

<details>
<summary>Advanced: rejects a matrix perturbed in any single one of the nine slots</summary>

#### rejects a matrix perturbed in any single one of the nine slots

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var missed = 0
var slot = 0
while slot < 9:
    if _perturbed(slot).is_identity():
        missed = missed + 1
    slot = slot + 1
expect(missed).to_equal(0)
```

</details>


</details>

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

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `8791a4bbd733554a196424b2a34673997deb44e8062eaad9c46abee9fe2ae084`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `8791a4bbd733554a196424b2a34673997deb44e8062eaad9c46abee9fe2ae084`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `8791a4bbd733554a196424b2a34673997deb44e8062eaad9c46abee9fe2ae084`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **89/100**; effective score: **89/100**; blockers: **0**.

SSpec documentization score: 89/100
source: test/01_unit/lib/skia/matrix_is_identity_spec.spl
mirror: doc/06_spec/01_unit/lib/skia/matrix_is_identity_spec.md (current)
findings: 7 blockers: 0
  narrative=100 structure=70 oracle=90
  traceability=100 evidence=100 coverage=100 maintainability=55
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/skia/matrix_is_identity_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/skia/matrix_is_identity_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/skia/matrix_is_identity_spec.spl:1:1: advice SSDOC-MNT-001 [maintainability] (-15): multiple scenarios form a flat, unfolded presentation
  why: Long flat dumps obscure the primary workflow.
  improve: Group secondary detail and keep the primary workflow visible.
test/01_unit/lib/skia/matrix_is_identity_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/skia/matrix_is_identity_spec.spl:57:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'returns true for the identity and for identity-equivalent factories' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/01_unit/lib/skia/matrix_is_identity_spec.spl:65:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'returns false for a translation' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/01_unit/lib/skia/matrix_is_identity_spec.spl:70:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'rejects a matrix perturbed in any single one of the nine slots' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
<!-- sspec-maintain:scorecard:end -->

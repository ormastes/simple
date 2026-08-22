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
| Updated | 2026-08-22 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
## Operator workflow
## Compatibility and limitations

# Matrix3x3.is_identity

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

- Verify: returns true for the identity and for identity-equivalent factories
   - Expected: Matrix3x3.identity().is_identity() is true
   - Expected: Matrix3x3.scale(sx: 1.0, sy: 1.0).is_identity() is true
   - Expected: Matrix3x3.rotate_degrees(deg: 0.0).is_identity() is true
   - Expected: Matrix3x3.identity().mul(Matrix3x3.identity()).is_identity() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-SKIA_MATRIX_IS_IDENTITY-001
step("Verify: returns true for the identity and for identity-equivalent factories")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
expect(Matrix3x3.identity().is_identity()).to_equal(true)
expect(Matrix3x3.scale(sx: 1.0, sy: 1.0).is_identity()).to_equal(true)
expect(Matrix3x3.rotate_degrees(deg: 0.0).is_identity()).to_equal(true)
expect(Matrix3x3.identity().mul(Matrix3x3.identity()).is_identity()).to_equal(true)
```

</details>

#### returns false for a translation

- Verify: returns false for a translation
   - Expected: Matrix3x3.translate(tx: 10.0, ty: 20.0).is_identity() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-SKIA_MATRIX_IS_IDENTITY-001
step("Verify: returns false for a translation")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
expect(Matrix3x3.translate(tx: 10.0, ty: 20.0).is_identity()).to_equal(false)
```

</details>

### Matrix3x3.is_identity element sensitivity (detection)

<details>
<summary>Advanced: rejects a matrix perturbed in any single one of the nine slots</summary>

#### rejects a matrix perturbed in any single one of the nine slots

- Verify: rejects a matrix perturbed in any single one of the nine slots
   - Expected: missed equals `0)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-SKIA_MATRIX_IS_IDENTITY-001
step("Verify: rejects a matrix perturbed in any single one of the nine slots")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
var missed = 0
var slot = 0
while slot < 9:
    if _perturbed(slot).is_identity():
        missed = missed + 1
    slot = slot + 1
expect(missed).to_equal(0)  # oracle: pinned constant asserted by this scenario
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

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `3fdc62c79ac2f1dcbc4736a83c7f916545a4b291f6affc37a434be9ceb6e6af2`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `3fdc62c79ac2f1dcbc4736a83c7f916545a4b291f6affc37a434be9ceb6e6af2`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `3fdc62c79ac2f1dcbc4736a83c7f916545a4b291f6affc37a434be9ceb6e6af2`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **94/100**; effective score: **94/100**; blockers: **0**.

SSpec documentization score: 94/100
source: test/01_unit/lib/skia/matrix_is_identity_spec.spl
mirror: doc/06_spec/01_unit/lib/skia/matrix_is_identity_spec.md (current)
findings: 3 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=85 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/skia/matrix_is_identity_spec.md:1:1: warning SSDOC-EVD-002 [evidence] (-15): source steps are not visible in the generated manual
  why: Source tokens alone do not prove reader-visible workflow structure.
  improve: Use supported literal step calls and regenerate the manual.
doc/06_spec/01_unit/lib/skia/matrix_is_identity_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/skia/matrix_is_identity_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, traceability, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
<!-- sspec-maintain:scorecard:end -->

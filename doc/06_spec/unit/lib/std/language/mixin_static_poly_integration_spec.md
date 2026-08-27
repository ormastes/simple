# Mixin and Static Polymorphism Integration

> Mixins provide horizontal composition (adding capabilities to a class) while

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Mixin and Static Polymorphism Integration

Mixins provide horizontal composition (adding capabilities to a class) while

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/unit/lib/std/language/mixin_static_poly_integration_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Mixins provide horizontal composition (adding capabilities to a class) while
static polymorphism provides zero-cost abstraction. Together they allow
type-safe, performant code composition. This spec exercises the two features
in combination through executed assertions rather than source inspection.

## Scenarios

### Integration - Mixin Method Calls Through Class

#### calls one mixin method and sees state shared with the other

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
val c = Counter()
c.label = "hits"
expect(c.increment()).to_equal(1)
expect(c.increment()).to_equal(2)
expect(c.describe()).to_equal("hits(2)")
```

</details>

### Integration - Generic Mixin Specialization

#### specializes a generic mixin to i64 and returns the payload

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
val h = IntHolder()
h.payload = 21
expect(h.cloned() * 2).to_equal(42)
```

</details>

### Integration - Independent Instances

#### keeps mixin state per instance

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
val a = Counter()
val b = Counter()
a.increment()
a.increment()
a.increment()
b.increment()
expect(a.count).to_equal(3)
expect(b.count).to_equal(1)
```

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

- Canonical SPipe generation for source `83fe3109415ac6f0cce2ac85ce4780b333a68133f6912d9f5d56fd0ba5dcd1f4`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `83fe3109415ac6f0cce2ac85ce4780b333a68133f6912d9f5d56fd0ba5dcd1f4`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `83fe3109415ac6f0cce2ac85ce4780b333a68133f6912d9f5d56fd0ba5dcd1f4`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **85/100**; effective score: **85/100**; blockers: **0**.

SSpec documentization score: 85/100
source: test/unit/lib/std/language/mixin_static_poly_integration_spec.spl
mirror: doc/06_spec/unit/lib/std/language/mixin_static_poly_integration_spec.md (current)
findings: 7 blockers: 0
  narrative=100 structure=70 oracle=70
  traceability=100 evidence=100 coverage=100 maintainability=55
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/lib/std/language/mixin_static_poly_integration_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/lib/std/language/mixin_static_poly_integration_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/lib/std/language/mixin_static_poly_integration_spec.spl:1:1: advice SSDOC-MNT-001 [maintainability] (-15): multiple scenarios form a flat, unfolded presentation
  why: Long flat dumps obscure the primary workflow.
  improve: Group secondary detail and keep the primary workflow visible.
test/unit/lib/std/language/mixin_static_poly_integration_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 5 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/lib/std/language/mixin_static_poly_integration_spec.spl:43:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'calls one mixin method and sees state shared with the other' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/unit/lib/std/language/mixin_static_poly_integration_spec.spl:52:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'specializes a generic mixin to i64 and returns the payload' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/unit/lib/std/language/mixin_static_poly_integration_spec.spl:59:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'keeps mixin state per instance' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
<!-- sspec-maintain:scorecard:end -->

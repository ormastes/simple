# Imported Optional-Argument Projection Across a Re-export Hop — Regression Spec

> Purpose: the behavior asserted in this spec  Audience: engineers reading this spec to confirm the behavior still holds.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Imported Optional-Argument Projection Across a Re-export Hop — Regression Spec

Purpose: the behavior asserted in this spec  Audience: engineers reading this spec to confirm the behavior still holds.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/hir/imported_optional_argument_reexport_hop_regression_spec.spl` |
| Updated | 2026-08-22 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience

Purpose: the behavior asserted in this spec  Audience: engineers reading this spec to confirm the behavior still holds.

## Operator workflow

1. Run `bin/simple test test/01_unit/compiler/hir/imported_optional_argument_reexport_hop_regression_spec.spl`.
2. Every scenario must pass; a failure is a regression in the behavior under test.

## Compatibility and limitations

Covers the behavior asserted here; platform-specific behavior is out of scope.

## Scenarios

### optional generic argument projected across a re-export hop

#### does not blame the importer for a type only the OWNER imports

- Verify: does not blame the importer for a type only the OWNER imports
   - Expected: hop_unresolved_span_errors(lowering) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-SSPEC-LOCAL-001
step("Verify: does not blame the importer for a type only the OWNER imports")
# RED at run15's tree: the projected `Option<Span>` argument is looked
# up in the facade `mir`, misses, falls to the importer's scope, and
# reports `unresolved type: Span` against mir.hwir.bvc -- a module that
# never names Span. This is the shape of all 3716 run15 fatals.
val lowering = hop_lower("s: Span?")
for error in lowering.errors:
    eprint("[hop-optional-error] {error.message}")
expect(hop_unresolved_span_errors(lowering)).to_equal(0)
```

</details>

#### does not blame the importer for a Dict VALUE the owner imports

- Verify: does not blame the importer for a Dict VALUE the owner imports
   - Expected: hop_unresolved_span_errors(lowering) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-SSPEC-LOCAL-001
step("Verify: does not blame the importer for a Dict VALUE the owner imports")
# Same miss, different generic constructor -- the argument recursion is
# shared, so both branches must clear together.
val lowering = hop_lower("d: Dict<text, Span>")
for error in lowering.errors:
    eprint("[hop-dict-error] {error.message}")
expect(hop_unresolved_span_errors(lowering)).to_equal(0)
```

</details>

#### guards the guard: a NON-generic use of the same type is unaffected

- Verify: guards the guard: a NON-generic use of the same type is unaffected
   - Expected: hop_unresolved_span_errors(lowering) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-SSPEC-LOCAL-001
step("Verify: guards the guard: a NON-generic use of the same type is unaffected")
# The bare `s: Span` shape never went through the argument recursion,
# so it must be green on BOTH sides of the regression. If this ever
# goes red the fixture has stopped isolating the argument path.
val lowering = hop_lower("s: Span")
expect(hop_unresolved_span_errors(lowering)).to_equal(0)
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

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `0a8f863a38e0c462836a4270a56781e453520d33988cbaaeb6e0a8f9226affec`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `0a8f863a38e0c462836a4270a56781e453520d33988cbaaeb6e0a8f9226affec`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `0a8f863a38e0c462836a4270a56781e453520d33988cbaaeb6e0a8f9226affec`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/compiler/hir/imported_optional_argument_reexport_hop_regression_spec.spl
mirror: doc/06_spec/01_unit/compiler/hir/imported_optional_argument_reexport_hop_regression_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/hir/imported_optional_argument_reexport_hop_regression_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/hir/imported_optional_argument_reexport_hop_regression_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: assumptions/preconditions, traceability, evidence, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/hir/imported_optional_argument_reexport_hop_regression_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 3 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/hir/imported_optional_argument_reexport_hop_regression_spec.spl:130:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'does not blame the importer for a type only the OWNER imports' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/hir/imported_optional_argument_reexport_hop_regression_spec.spl:142:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'does not blame the importer for a Dict VALUE the owner imports' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/hir/imported_optional_argument_reexport_hop_regression_spec.spl:152:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'guards the guard: a NON-generic use of the same type is unaffected' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

<!-- doc06-layout-migration: Historical generated/manual evidence retained; authoritative executable source remains at test/01_unit/compiler/hir/imported_optional_argument_reexport_hop_regression_spec.spl. -->

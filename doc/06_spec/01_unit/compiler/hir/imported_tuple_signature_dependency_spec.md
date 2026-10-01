# Imported Tuple Signature Dependency — Unit Spec

> Regression guard for the Stage-1 HIR fatal

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Imported Tuple Signature Dependency — Unit Spec

Regression guard for the Stage-1 HIR fatal

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/hir/imported_tuple_signature_dependency_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Regression guard for the Stage-1 HIR fatal

    HIR lowering error in src/compiler/driver/driver.spl:
    unresolved type: ResolveError

`src/compiler/80.driver/driver.spl` never names `ResolveError` (0 hits in all
156 lines). `struct ResolveError` is declared in
`src/compiler/35.semantics/resolve.spl:762`, and `resolve_methods` there returns
the TUPLE `(HirModule, [ResolveError])`.

Cross-module signature dependencies are materialized under the QUALIFIED local
name `{module}::{name}` (`materialize_imported_callable_declared_dependency`),
never the bare one. `imported_surface_type_projected` projects an imported
signature back through that qualified scope, but only for two SCALAR shapes:
a top-level named type (`return_type_name`) and an array-of-named
(`return_array_element_name`). A tuple populates NEITHER, so it fell through to
`imported_surface_type`, which also only projected a top-level Named kind, and
finally to `lower_type` — which resolves names in the IMPORTER's scope, where
`ResolveError` is bound only as `sem.resolve::ResolveError`. Result: the hard,
non-recovered `unresolved type: ResolveError` blamed on the importer.

The defect is SHAPE-specific, not type-specific: the identical signature written
as a bare `[ResolveError]` always worked, which is what made it look arbitrary.

## Scenarios

### imported callable whose signature dependency sits inside a tuple

#### resolves a tuple-return element type through the declaring module

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- resolves a tuple-return element type through the declaring module
   - Expected: lowering.errors.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("resolves a tuple-return element type through the declaring module")
# Pre-fix: `unresolved type: ResolveError`, attributed to drv.driver.
val lowering = tuple_dep_spec_lower("(i64, [ResolveError])")
for error in lowering.errors:
    eprint("[tuple-dep-error] {error.message}")
expect(lowering.errors.len()).to_equal(0)
```

</details>

#### still resolves the array-only shape that always worked

- still resolves the array-only shape that always worked
   - Expected: lowering.errors.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("still resolves the array-only shape that always worked")
# Control: proves the defect was the SHAPE, not the type name.
val lowering = tuple_dep_spec_lower("[ResolveError]")
expect(lowering.errors.len()).to_equal(0)
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

- `REQ-SSPEC-COMPILER`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `d5edcf6a5ac8050a524d9ea147014f1d2be80c141d2e301e738ab8a51979d6b4`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `d5edcf6a5ac8050a524d9ea147014f1d2be80c141d2e301e738ab8a51979d6b4`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `d5edcf6a5ac8050a524d9ea147014f1d2be80c141d2e301e738ab8a51979d6b4`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/01_unit/compiler/hir/imported_tuple_signature_dependency_spec.spl
mirror: doc/06_spec/01_unit/compiler/hir/imported_tuple_signature_dependency_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/hir/imported_tuple_signature_dependency_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/hir/imported_tuple_signature_dependency_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/hir/imported_tuple_signature_dependency_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/hir/imported_tuple_signature_dependency_spec.spl:79:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'resolves a tuple-return element type through the declaring module' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/hir/imported_tuple_signature_dependency_spec.spl:88:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'still resolves the array-only shape that always worked' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

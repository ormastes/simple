# Imported Array-of-Tuple Signature Dependency — Unit Spec

> Purpose: the behavior asserted in this spec  Audience: engineers reading this spec to confirm the behavior still holds.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Imported Array-of-Tuple Signature Dependency — Unit Spec

Purpose: the behavior asserted in this spec  Audience: engineers reading this spec to confirm the behavior still holds.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/hir/imported_array_of_tuple_signature_dependency_spec.spl` |
| Updated | 2026-08-22 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience

Purpose: the behavior asserted in this spec  Audience: engineers reading this spec to confirm the behavior still holds.

## Operator workflow

1. Run `bin/simple test test/01_unit/compiler/hir/imported_array_of_tuple_signature_dependency_spec.spl`.
2. Every scenario must pass; a failure is a regression in the behavior under test.

## Compatibility and limitations

Covers the behavior asserted here; platform-specific behavior is out of scope.

## Scenarios

### imported callable signature dependency under a constructor the projection did not recurse

#### resolves an array-of-tuple element type through the declaring module

- Verify: resolves an array-of-tuple element type through the declaring module
   - Expected: lowering.errors.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Verify: resolves an array-of-tuple element type through the declaring module")
# @req: REQ-SSPEC-LOCAL-001
# Pre-fix: `unresolved type: MirType`, attributed to be.backend_port.
val lowering = array_tuple_dep_lower("fields: [(text, MirType)]")
for error in lowering.errors:
    eprint("[array-tuple-dep-error] {error.message}")
expect(lowering.errors.len()).to_equal(0)
```

</details>

#### resolves a pointee type through the declaring module

- Verify: resolves a pointee type through the declaring module
   - Expected: lowering.errors.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Verify: resolves a pointee type through the declaring module")
# @req: REQ-SSPEC-LOCAL-001
# Same asymmetry, different constructor: `*T` is recursed by the
# materialization walk and was not recursed by the projection.
# Pre-fix: `unresolved type: MirType`. 22 pointer params in owned code.
val lowering = array_tuple_dep_lower("p: *MirType")
for error in lowering.errors:
    eprint("[pointer-dep-error] {error.message}")
expect(lowering.errors.len()).to_equal(0)
```

</details>

#### resolves a union member type through the declaring module

- Verify: resolves a union member type through the declaring module
   - Expected: lowering.errors.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Verify: resolves a union member type through the declaring module")
# @req: REQ-SSPEC-LOCAL-001
# Pre-fix: `unresolved type: MirType`. 13 union positions in owned code.
val lowering = array_tuple_dep_lower("u: MirType | text")
for error in lowering.errors:
    eprint("[union-dep-error] {error.message}")
expect(lowering.errors.len()).to_equal(0)
```

</details>

#### still resolves the bare-array shape that always worked

- Verify: still resolves the bare-array shape that always worked
   - Expected: lowering.errors.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Verify: still resolves the bare-array shape that always worked")
# @req: REQ-SSPEC-LOCAL-001
# Control: proves the defect was the SHAPE, not the type name.
val lowering = array_tuple_dep_lower("fields: [MirType]")
expect(lowering.errors.len()).to_equal(0)
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

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `f48b4c03969fe25a4fcc721e6a2891f89206566e8632971424de66bcfa5d4ee6`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `f48b4c03969fe25a4fcc721e6a2891f89206566e8632971424de66bcfa5d4ee6`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `f48b4c03969fe25a4fcc721e6a2891f89206566e8632971424de66bcfa5d4ee6`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/compiler/hir/imported_array_of_tuple_signature_dependency_spec.spl
mirror: doc/06_spec/01_unit/compiler/hir/imported_array_of_tuple_signature_dependency_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/hir/imported_array_of_tuple_signature_dependency_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/hir/imported_array_of_tuple_signature_dependency_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: assumptions/preconditions, traceability, evidence, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/hir/imported_array_of_tuple_signature_dependency_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 4 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/hir/imported_array_of_tuple_signature_dependency_spec.spl:102:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'resolves an array-of-tuple element type through the declaring module' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/hir/imported_array_of_tuple_signature_dependency_spec.spl:111:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'resolves a pointee type through the declaring module' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/hir/imported_array_of_tuple_signature_dependency_spec.spl:122:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'resolves a union member type through the declaring module' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

<!-- doc06-layout-migration: Historical generated/manual evidence retained; authoritative executable source remains at test/01_unit/compiler/hir/imported_array_of_tuple_signature_dependency_spec.spl. -->

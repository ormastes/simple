# Hir Package Dependency Scan Memo Specification

> Tests covering HIR package-dependency scan memo.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Hir Package Dependency Scan Memo Specification

## Scenarios

### HIR package-dependency scan memo

#### scans the frozen registry once per (module, dependency) pair

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
```

</details>

#### still scans for a different dependency name

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val registry = package_registry()
var lowering = hirlowering_for_module("pkg/a.spl", registry)
val span = Span.empty()
lowering.materialize_imported_field_package_dependency(
    0, "One", span, false)
lowering.materialize_imported_field_package_dependency(
    0, "Two", span, false)
expect(lowering.field_package_dep_scan_count).to_equal(2)
```

</details>

#### memoizes each surface's package name

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val registry = package_registry()
var lowering = hirlowering_for_module("pkg/a.spl", registry)
expect(lowering.cached_surface_package_name("pkg.a")).to_equal("pkg")
expect(lowering.cached_surface_package_name("pkg.a")).to_equal("pkg")
expect(lowering.surface_package_name_memo.len()).to_equal(1)
```

</details>

#### builds the declaration-owner index once, then answers from it

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val registry = package_registry()
var lowering = hirlowering_for_module("pkg/a.spl", registry)
expect(lowering.surface_decl_index_build_count).to_equal(0)
val first = lowering.surface_decl_owner_indices("Missing")
expect(first.len()).to_equal(0)
expect(lowering.surface_decl_index_build_count).to_equal(1)
val second = lowering.surface_decl_owner_indices("Other")
expect(second.len()).to_equal(0)
# The point of the index: a SECOND name costs a dict probe, not a
# second sweep of the registry.
expect(lowering.surface_decl_index_build_count).to_equal(1)
```

</details>

#### builds the package-sibling index once and lists direct members

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val registry = package_registry()
var lowering = hirlowering_for_module("pkg/a.spl", registry)
expect(lowering.package_sibling_index_build_count).to_equal(0)
val members = lowering.package_sibling_registry_names("pkg")
expect(members.len()).to_equal(3)
expect(lowering.package_sibling_canonical_names("pkg").len()).to_equal(3)
expect(lowering.package_sibling_registry_names("other").len()).to_equal(0)
expect(lowering.package_sibling_index_build_count).to_equal(1)
```

</details>

#### resolves registry keys from retained scalar authority

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val registry = package_registry()
var lowering = hirlowering_for_module("pkg/a.spl", registry)
expect(lowering.surface_index_by_name_build_count).to_equal(0)
expect(lowering.surface_index_for_name("pkg.b")).to_equal(1)
expect(lowering.surface_index_for_name("pkg.c")).to_equal(2)
expect(lowering.surface_index_for_name("pkg.absent")).to_equal(-1)
expect(lowering.surface_index_by_name_build_count).to_equal(0)
```

</details>

#### falls back to retained scalar registry keys after a cache miss

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val registry = package_registry()
var lowering = hirlowering_for_module("pkg/a.spl", registry)
lowering.surface_index_by_name = {}
lowering.surface_index_by_name_built = true
expect(lowering.surface_index_for_name("pkg.c")).to_equal(2)
expect(lowering.surface_index_for_name("pkg.absent")).to_equal(-1)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/hir/hir_package_dependency_scan_memo_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering HIR package-dependency scan memo.
- HIR package-dependency scan memo

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
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

- Canonical SPipe generation for source `3eeec83e163425e57f8e5032cb4fb1e29eeb9012531816bdba2c2fbd7878d788`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `3eeec83e163425e57f8e5032cb4fb1e29eeb9012531816bdba2c2fbd7878d788`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `3eeec83e163425e57f8e5032cb4fb1e29eeb9012531816bdba2c2fbd7878d788`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **83/100**; effective score: **83/100**; blockers: **0**.

SSpec documentization score: 83/100
source: test/01_unit/compiler/hir/hir_package_dependency_scan_memo_spec.spl
mirror: doc/06_spec/01_unit/compiler/hir/hir_package_dependency_scan_memo_spec.md (current)
findings: 8 blockers: 0
  narrative=100 structure=60 oracle=70
  traceability=100 evidence=100 coverage=100 maintainability=55
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/hir/hir_package_dependency_scan_memo_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/hir/hir_package_dependency_scan_memo_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/hir/hir_package_dependency_scan_memo_spec.spl:1:1: advice SSDOC-MNT-001 [maintainability] (-15): multiple scenarios form a flat, unfolded presentation
  why: Long flat dumps obscure the primary workflow.
  improve: Group secondary detail and keep the primary workflow visible.
test/01_unit/compiler/hir/hir_package_dependency_scan_memo_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 19 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/hir/hir_package_dependency_scan_memo_spec.spl:43:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'scans the frozen registry once per (module, dependency) pair' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/01_unit/compiler/hir/hir_package_dependency_scan_memo_spec.spl:59:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'still scans for a different dependency name' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/01_unit/compiler/hir/hir_package_dependency_scan_memo_spec.spl:70:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'memoizes each surface's package name' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/01_unit/compiler/hir/hir_package_dependency_scan_memo_spec.spl:78:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'builds the declaration-owner index once, then answers from it' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
<!-- sspec-maintain:scorecard:end -->

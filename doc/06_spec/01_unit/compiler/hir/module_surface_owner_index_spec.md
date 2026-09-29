# Module Surface Owner Index Specification

> Tests covering module surface owner indexing.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Module Surface Owner Index Specification

## Scenarios

### module surface owner indexing

#### rejects an out-of-range owner index before a surface dereference

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- rejects an out-of-range owner index before a surface dereference
   - Expected: result.is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects an out-of-range owner index before a surface dereference")
val result = module_surface_validate_owner_index(2, 2)

expect(result.is_err()).to_equal(true)
expect(result.unwrap_err()).to_contain("index=2 len=2")
```

</details>

#### accepts a nonzero owner index within the surface bounds

- accepts a nonzero owner index within the surface bounds
   - Expected: result.is_ok() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("accepts a nonzero owner index within the surface bounds")
val result = module_surface_validate_owner_index(1, 2)

expect(result.is_ok()).to_equal(true)
```

</details>

#### keeps same-source cross-category duplicates attributable to that source

- keeps same-source cross-category duplicates attributable to that source
   - Expected: result.is_ok() is true
   - Expected: facade_surface.export_origins["shared"].owner_module equals `pkg.provider`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps same-source cross-category duplicates attributable to that source")
val provider_body = "pub fn shared() -> i64:\n    1\npub const shared: i64 = 2\n"
val facade_body = "export shared\n"
val provider = parse_and_build_module(provider_body, "pkg/provider.spl")
val facade = parse_and_build_module(facade_body, "pkg/__init__.spl")
val result = module_surfaces_from_modules(
    {"pkg.provider": provider, "pkg.__init__": facade},
    [
        surface_source("pkg/provider.spl", provider_body, "pkg.provider"),
        surface_source("pkg/__init__.spl", facade_body, "pkg.__init__")
    ])

expect(result.is_ok()).to_equal(true)
val surfaces = result.unwrap()
val facade_surface = surfaces.surfaces[surfaces.index_by_name["pkg.__init__"]]
expect(facade_surface.export_origins["shared"].owner_module).to_equal("pkg.provider")
```

</details>

#### indexes a constant when every earlier declaration category is empty

- indexes a constant when every earlier declaration category is empty
   - Expected: result.is_ok() is true
   - Expected: facade_surface.export_origins["tail_only"].owner_module equals `pkg.constants`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("indexes a constant when every earlier declaration category is empty")
val provider_body = "pub const tail_only: i64 = 7\n"
val facade_body = "export tail_only\n"
val provider = parse_and_build_module(provider_body, "pkg/constants.spl")
val facade = parse_and_build_module(facade_body, "pkg/__init__.spl")
val result = module_surfaces_from_modules(
    {"pkg.constants": provider, "pkg.__init__": facade},
    [
        surface_source("pkg/constants.spl", provider_body, "pkg.constants"),
        surface_source("pkg/__init__.spl", facade_body, "pkg.__init__")
    ])

expect(result.is_ok()).to_equal(true)
val surfaces = result.unwrap()
val facade_surface = surfaces.surfaces[surfaces.index_by_name["pkg.__init__"]]
expect(facade_surface.export_origins["tail_only"].owner_module).to_equal("pkg.constants")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/hir/module_surface_owner_index_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering module surface owner indexing.
- module surface owner indexing

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

- Canonical SPipe generation for source `2f106157f840a66b710d6d3fa721cd596d5da314a58e6ae27d7672bf1597b2c1`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `2f106157f840a66b710d6d3fa721cd596d5da314a58e6ae27d7672bf1597b2c1`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `2f106157f840a66b710d6d3fa721cd596d5da314a58e6ae27d7672bf1597b2c1`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/compiler/hir/module_surface_owner_index_spec.spl
mirror: doc/06_spec/01_unit/compiler/hir/module_surface_owner_index_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/hir/module_surface_owner_index_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/hir/module_surface_owner_index_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/hir/module_surface_owner_index_spec.spl:19:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects an out-of-range owner index before a surface dereference' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/hir/module_surface_owner_index_spec.spl:27:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'accepts a nonzero owner index within the surface bounds' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/hir/module_surface_owner_index_spec.spl:34:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps same-source cross-category duplicates attributable to that source' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

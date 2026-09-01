# GC-Mode Module Resolution

> Verifies that the module loader resolves modules from the correct variant directories. Tests that common/ modules are accessible and that the fallback chain works after migration.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# GC-Mode Module Resolution

Verifies that the module loader resolves modules from the correct variant directories. Tests that common/ modules are accessible and that the fallback chain works after migration.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | N/A |
| Category | Infrastructure |
| Difficulty | 4/5 |
| Status | Implemented |
| Requirements | N/A |
| Plan | N/A |
| Design | N/A |
| Research | N/A |
| Source | `test/feature/lib/gc_parity/gc_module_loader_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Verifies that the module loader resolves modules from the correct
variant directories. Tests that common/ modules are accessible
and that the fallback chain works after migration.

## Scenarios

### Module Resolution Fallback

#### when importing array utilities from common

#### accesses array utilities after migration

- accesses array utilities after migration
   - Expected: items[0] equals `3`
   - Expected: items.len() equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("accesses array utilities after migration")
"""
Basic array operations should work after migration.
"""
val items = [3, 1, 2]
expect(items[0]).to_equal(3)
expect(items.len()).to_equal(3)
```

</details>

#### when verifying omitted sync GC family

#### does not expose an unimplemented gc_sync_mut family

- does not expose an unimplemented gc_sync_mut family
   - Expected: _has_gc_sync_mut_source_dir() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("does not expose an unimplemented gc_sync_mut family")
"""
The runtime-family matrix marks gc_sync_mut as not implemented.
The source tree should not contain a stub family that reverses
the no-GC-first direction.
"""
expect(_has_gc_sync_mut_source_dir()).to_equal(false)
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

- `REQ-SSPEC-FEATURE`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `ab56d0dc17ddc7cc77aabb1a44548cf18cc80a8cd562471c5894ae284e577a80`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `ab56d0dc17ddc7cc77aabb1a44548cf18cc80a8cd562471c5894ae284e577a80`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `ab56d0dc17ddc7cc77aabb1a44548cf18cc80a8cd562471c5894ae284e577a80`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/feature/lib/gc_parity/gc_module_loader_spec.spl
mirror: doc/06_spec/feature/lib/gc_parity/gc_module_loader_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/feature/lib/gc_parity/gc_module_loader_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/feature/lib/gc_parity/gc_module_loader_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/feature/lib/gc_parity/gc_module_loader_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/feature/lib/gc_parity/gc_module_loader_spec.spl:55:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'accesses array utilities after migration' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/lib/gc_parity/gc_module_loader_spec.spl:74:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'does not expose an unimplemented gc_sync_mut family' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

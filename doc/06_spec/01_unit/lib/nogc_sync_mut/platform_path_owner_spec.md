# Platform Path Owner Specification

> Tests covering nogc_sync_mut platform path ownership.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Platform Path Owner Specification

## Scenarios

### nogc_sync_mut platform path ownership

#### retains canonical path implementations through native entry closure

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- retains canonical path implementations through native entry closure
   - Expected: normalize_path("alpha\\beta\\gamma") equals `canon_normalize("alpha\\beta\\gamma")`
   - Expected: join_path("a", "b") equals `canon_join("a", "b")`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("retains canonical path implementations through native entry closure")
# oracle: the platform module re-exports the canonical path module's
# behavior directly — calling through it must match the semantics of
# std.path itself, proving a plain re-export rather than a divergent copy.
use std.path.{normalize_path as canon_normalize, join_path as canon_join}
expect(normalize_path("alpha\\beta\\gamma")).to_equal(canon_normalize("alpha\\beta\\gamma"))
expect(join_path("a", "b")).to_equal(canon_join("a", "b"))
```

</details>

#### forwards path behavior without a runtime module object

- forwards path behavior without a runtime module object
   - Expected: normalize_path("alpha\\beta") equals `alpha/beta`
   - Expected: is_absolute_path("/tmp/simple") is true
   - Expected: join_path("alpha", "beta") equals `alpha/beta`
   - Expected: join_path("/tmp/", "out.txt") equals `/tmp/out.txt`
   - Expected: is_absolute_path("relative/x") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("forwards path behavior without a runtime module object")
expect(normalize_path("alpha\\beta")).to_equal("alpha/beta")
expect(is_absolute_path("/tmp/simple")).to_equal(true)
expect(join_path("alpha", "beta")).to_equal("alpha/beta")
# oracle: redundant separators collapse and trailing pieces join exactly
expect(join_path("/tmp/", "out.txt")).to_equal("/tmp/out.txt")
expect(is_absolute_path("relative/x")).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_sync_mut/platform_path_owner_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering nogc_sync_mut platform path ownership.
- nogc_sync_mut platform path ownership

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

- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `7d4a1f8e709bf1e90ceee5ef4e599f2d1123eaa21a1bcdcff761fc6ed5916e72`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `7d4a1f8e709bf1e90ceee5ef4e599f2d1123eaa21a1bcdcff761fc6ed5916e72`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `7d4a1f8e709bf1e90ceee5ef4e599f2d1123eaa21a1bcdcff761fc6ed5916e72`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **94/100**; effective score: **94/100**; blockers: **0**.

SSpec documentization score: 94/100
source: test/01_unit/lib/nogc_sync_mut/platform_path_owner_spec.spl
mirror: doc/06_spec/01_unit/lib/nogc_sync_mut/platform_path_owner_spec.md (current)
findings: 4 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/nogc_sync_mut/platform_path_owner_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/nogc_sync_mut/platform_path_owner_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/nogc_sync_mut/platform_path_owner_spec.spl:12:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'retains canonical path implementations through native entry closure' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/nogc_sync_mut/platform_path_owner_spec.spl:22:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'forwards path behavior without a runtime module object' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

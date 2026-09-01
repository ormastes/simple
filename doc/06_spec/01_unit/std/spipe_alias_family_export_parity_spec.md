# Spipe Alias Family Export Parity Specification

> Tests covering spipe alias modules re-export lifecycle hooks.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Spipe Alias Family Export Parity Specification

## Scenarios

### spipe alias modules re-export lifecycle hooks

#### nogc_sync_mut alias re-exports

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- nogc_sync_mut alias re-exports
   - Expected: _alias_reexports("src/lib/nogc_sync_mut/spipe.spl") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("nogc_sync_mut alias re-exports")
expect(_alias_reexports("src/lib/nogc_sync_mut/spipe.spl")).to_equal(true)
```

</details>

#### nogc_async_mut alias re-exports

- nogc_async_mut alias re-exports
   - Expected: _alias_reexports("src/lib/nogc_async_mut/spipe.spl") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("nogc_async_mut alias re-exports")
expect(_alias_reexports("src/lib/nogc_async_mut/spipe.spl")).to_equal(true)
```

</details>

#### gc_async_mut alias re-exports

- gc_async_mut alias re-exports
   - Expected: _alias_reexports("src/lib/gc_async_mut/spipe.spl") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("gc_async_mut alias re-exports")
expect(_alias_reexports("src/lib/gc_async_mut/spipe.spl")).to_equal(true)
```

</details>

#### gc_sync_mut alias re-exports

- gc_sync_mut alias re-exports
   - Expected: _alias_reexports("src/lib/gc_sync_mut/spipe.spl") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("gc_sync_mut alias re-exports")
expect(_alias_reexports("src/lib/gc_sync_mut/spipe.spl")).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/std/spipe_alias_family_export_parity_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering spipe alias modules re-export lifecycle hooks.
- spipe alias modules re-export lifecycle hooks

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

- Canonical SPipe generation for source `de7836a87f547b2f93c63da14615d05f70d17385d5834051a2e0573590dda77b`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `de7836a87f547b2f93c63da14615d05f70d17385d5834051a2e0573590dda77b`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `de7836a87f547b2f93c63da14615d05f70d17385d5834051a2e0573590dda77b`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/std/spipe_alias_family_export_parity_spec.spl
mirror: doc/06_spec/01_unit/std/spipe_alias_family_export_parity_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/std/spipe_alias_family_export_parity_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/std/spipe_alias_family_export_parity_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/std/spipe_alias_family_export_parity_spec.spl:25:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'nogc_sync_mut alias re-exports' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/std/spipe_alias_family_export_parity_spec.spl:30:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'nogc_async_mut alias re-exports' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/std/spipe_alias_family_export_parity_spec.spl:35:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'gc_async_mut alias re-exports' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

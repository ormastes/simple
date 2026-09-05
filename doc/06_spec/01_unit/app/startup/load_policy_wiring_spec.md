# Load Policy Wiring Specification

> Tests covering legacy metadata parity, explicit load_policy overrides mmap_hint, invalid policy fails closed, preload mode mapping.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Load Policy Wiring Specification

## Scenarios

### legacy metadata parity

#### mmap_hint=true maps to map_selected_segments with mmap cache

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- mmap_hint=true maps to map_selected_segments with mmap cache


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("mmap_hint=true maps to map_selected_segments with mmap cache")
val d = startup_load_decision(legacy_metadata("smf", true), true, false)
assert_eq(d.load_policy, LOAD_POLICY_MAP_SELECTED_SEGMENTS)
assert_eq(d.cache_strategy, "mmap")
assert_true(d.include_mmap_cache)
assert_eq(d.preload_mode, "map_read_only")
assert_true(d.supported)
```

</details>

#### mmap_hint=false maps to normal with plain reads

- mmap_hint=false maps to normal with plain reads


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("mmap_hint=false maps to normal with plain reads")
val d = startup_load_decision(legacy_metadata("native", false), true, false)
assert_eq(d.load_policy, LOAD_POLICY_NORMAL)
assert_eq(d.cache_strategy, "normal_read")
assert_false(d.include_mmap_cache)
assert_eq(d.preload_mode, "")
assert_true(d.supported)
```

</details>

#### mmap_hint=true without host mmap falls back to simpleos prewarm

- mmap_hint=true without host mmap falls back to simpleos prewarm


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("mmap_hint=true without host mmap falls back to simpleos prewarm")
val d = startup_load_decision(legacy_metadata("smf", true), false, true)
assert_eq(d.cache_strategy, "simpleos_vfs_prewarm")
assert_true(d.include_mmap_cache)
assert_true(d.supported)
```

</details>

#### decision agrees with startup_plan_from_metadata for legacy metadata

- decision agrees with startup_plan_from_metadata for legacy metadata


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("decision agrees with startup_plan_from_metadata for legacy metadata")
val m = legacy_metadata("script", true)
val plan = startup_plan_from_metadata("a.spl", [], m, true, false)
val d = startup_load_decision(m, true, false)
assert_eq(d.load_policy, plan.load_policy)
assert_eq(d.cache_strategy, plan.cache_strategy)
assert_eq(d.include_mmap_cache, plan.include_mmap_cache)
assert_eq(d.supported, plan.supported)
```

</details>

### explicit load_policy overrides mmap_hint

#### normal overrides mmap_hint=true

- normal overrides mmap_hint=true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("normal overrides mmap_hint=true")
val m = declared_metadata("smf", true, LOAD_POLICY_NORMAL)
val d = startup_load_decision(m, true, false)
assert_eq(d.load_policy, LOAD_POLICY_NORMAL)
assert_eq(d.cache_strategy, "normal_read")
assert_false(d.include_mmap_cache)
assert_eq(d.preload_mode, "")
```

</details>

#### read_ahead_selected overrides mmap_hint=false

- read_ahead_selected overrides mmap_hint=false


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("read_ahead_selected overrides mmap_hint=false")
val m = declared_metadata("native", false, LOAD_POLICY_READ_AHEAD_SELECTED)
val d = startup_load_decision(m, true, false)
assert_eq(d.load_policy, LOAD_POLICY_READ_AHEAD_SELECTED)
assert_eq(d.cache_strategy, "mmap")
assert_true(d.include_mmap_cache)
assert_eq(d.preload_mode, "read_ahead")
```

</details>

### invalid policy fails closed

#### unknown declared policy yields unsupported normal-path decision

- unknown declared policy yields unsupported normal-path decision


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("unknown declared policy yields unsupported normal-path decision")
val m = declared_metadata("smf", true, "turbo")
val d = startup_load_decision(m, true, true)
assert_eq(d.load_policy, LOAD_POLICY_INVALID)
assert_eq(d.cache_strategy, "normal_read")
assert_false(d.include_mmap_cache)
assert_eq(d.preload_mode, "")
assert_false(d.supported)
assert_true(d.error.len() > 0)
```

</details>

### preload mode mapping

#### maps only mapping and read-ahead policies

- maps only mapping and read-ahead policies


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("maps only mapping and read-ahead policies")
assert_eq(load_policy_preload_mode(LOAD_POLICY_MAP_SELECTED_SEGMENTS), "map_read_only")
assert_eq(load_policy_preload_mode(LOAD_POLICY_READ_AHEAD_SELECTED), "read_ahead")
assert_eq(load_policy_preload_mode(LOAD_POLICY_NORMAL), "")
assert_eq(load_policy_preload_mode(LOAD_POLICY_INVALID), "")
```

</details>

#### derives the same decision from an existing plan

- derives the same decision from an existing plan


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("derives the same decision from an existing plan")
val m = legacy_metadata("smf", true)
val plan = startup_plan_from_metadata("b.smf", [], m, true, false)
val d = load_decision_from_plan(plan)
assert_eq(d.load_policy, plan.load_policy)
assert_eq(d.preload_mode, "map_read_only")
assert_true(d.supported)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/startup/load_policy_wiring_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering legacy metadata parity, explicit load_policy overrides mmap_hint, invalid policy fails closed, preload mode mapping.
- legacy metadata parity
- explicit load_policy overrides mmap_hint
- invalid policy fails closed
- preload mode mapping

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
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

- Canonical SPipe generation for source `589288ffabfc74d2d71cc4db64d6c445b1ba27b2f9a88f42a141ebfb18fde0c0`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `589288ffabfc74d2d71cc4db64d6c445b1ba27b2f9a88f42a141ebfb18fde0c0`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `589288ffabfc74d2d71cc4db64d6c445b1ba27b2f9a88f42a141ebfb18fde0c0`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/app/startup/load_policy_wiring_spec.spl
mirror: doc/06_spec/01_unit/app/startup/load_policy_wiring_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/app/startup/load_policy_wiring_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/startup/load_policy_wiring_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/startup/load_policy_wiring_spec.spl:41:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'mmap_hint=true maps to map_selected_segments with mmap cache' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/startup/load_policy_wiring_spec.spl:51:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'mmap_hint=false maps to normal with plain reads' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/startup/load_policy_wiring_spec.spl:61:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'mmap_hint=true without host mmap falls back to simpleos prewarm' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

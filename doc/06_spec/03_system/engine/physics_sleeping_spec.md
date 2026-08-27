# Physics Sleeping Specification

> Tests covering Physics2 IslandManager sleeping.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Physics Sleeping Specification

## Scenarios

### Physics2 IslandManager sleeping

#### bodies start awake

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- bodies start awake
   - Expected: m.is_island_sleeping(0) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("bodies start awake")
val m = make_manager()
expect(m.is_island_sleeping(0)).to_equal(false)
```

</details>

#### low KE puts island to sleep

- low KE puts island to sleep
   - Expected: m.is_island_sleeping(0) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("low KE puts island to sleep")
var m = make_manager()
m.update_sleep(0, 0.001, 0.6)
expect(m.is_island_sleeping(0)).to_equal(true)
```

</details>

#### high KE wakes island

- high KE wakes island
   - Expected: m.is_island_sleeping(0) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("high KE wakes island")
var m = make_manager()
m.update_sleep(0, 0.001, 0.6)
m.update_sleep(0, 1.0, 0.1)
expect(m.is_island_sleeping(0)).to_equal(false)
```

</details>

#### union merges islands

- union merges islands
   - Expected: r0 equals `r1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("union merges islands")
var m = make_manager()
m.union(0, 1)
val r0 = m.find(0)
val r1 = m.find(1)
expect(r0).to_equal(r1)
```

</details>

#### wake propagates to merged island

- wake propagates to merged island
   - Expected: m.is_island_sleeping(0) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("wake propagates to merged island")
var m = make_manager()
m.union(0, 1)
m.update_sleep(0, 0.001, 0.6)
m.update_sleep(1, 0.001, 0.6)
m.wake_island(1)
expect(m.is_island_sleeping(0)).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/engine/physics_sleeping_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Physics2 IslandManager sleeping.
- Physics2 IslandManager sleeping

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `497fd37d6f1881465c2bf6d2932dd6e669ecf5dbfb9f948f92113b7f002bba40`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `497fd37d6f1881465c2bf6d2932dd6e669ecf5dbfb9f948f92113b7f002bba40`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `497fd37d6f1881465c2bf6d2932dd6e669ecf5dbfb9f948f92113b7f002bba40`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/engine/physics_sleeping_spec.spl
mirror: doc/06_spec/03_system/engine/physics_sleeping_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/engine/physics_sleeping_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/engine/physics_sleeping_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/engine/physics_sleeping_spec.spl:40:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'bodies start awake' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/engine/physics_sleeping_spec.spl:46:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'low KE puts island to sleep' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/engine/physics_sleeping_spec.spl:53:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'high KE wakes island' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

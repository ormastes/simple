# Ui Scene Column Arena V2 Specification

> Tests covering UiSceneColumnArenaV2 (F3) direct writes.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Ui Scene Column Arena V2 Specification

## Scenarios

### UiSceneColumnArenaV2 (F3) direct writes

#### leases stable partitions and refuses over-capacity leases

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- leases stable partitions and refuses over-capacity leases


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("leases stable partitions and refuses over-capacity leases")
val a = make_arena()
val p0 = a.lease_partition(1, 0, 5)
val p1 = a.lease_partition(2, 0, 3)
assert_true(p0 == 0)
assert_true(p1 == 1)
# table 0 is now full: 5+3 == 8
assert_true(a.lease_partition(3, 0, 1) == -1)
```

</details>

#### writes rows directly and reads them back after swap

- writes rows directly and reads them back after swap


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("writes rows directly and reads them back after swap")
val a = make_arena()
val p = a.lease_partition(1, 0, 2)
assert_true(ui_scene_v2_write_row(a, p, 0, [10, 11, 12, 13]) == UI_SCENE_V2_OK)
assert_true(ui_scene_v2_write_row(a, p, 1, [20, 21, 22, 23]) == UI_SCENE_V2_OK)
assert_true(ui_scene_v2_commit(a) == UI_SCENE_V2_OK)
assert_true(a.front_word(0, 0, 0) == 10)
assert_true(a.front_word(0, 1, 3) == 23)
```

</details>

#### refuses writes past the leased partition (typed refusal, no grow)

- refuses writes past the leased partition (typed refusal, no grow)


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("refuses writes past the leased partition (typed refusal, no grow)")
val a = make_arena()
val p = a.lease_partition(1, 0, 2)
assert_true(ui_scene_v2_write_row(a, p, 2, [1, 2, 3, 4]) == UI_SCENE_V2_PARTITION_OVERFLOW)
assert_true(a.write_word_value(p, 0, 9, 1) == UI_SCENE_V2_BAD_COLUMN)
assert_true(a.write_word_value(99, 0, 0, 1) == UI_SCENE_V2_BAD_PARTITION)
```

</details>

#### records coalesced dirty row ranges on the back generation

- records coalesced dirty row ranges on the back generation


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("records coalesced dirty row ranges on the back generation")
val a = make_arena()
val p = a.lease_partition(1, 0, 4)
ui_scene_v2_write_row(a, p, 0, [1, 1, 1, 1])
ui_scene_v2_write_row(a, p, 1, [2, 2, 2, 2])
# rows 0 and 1 are contiguous -> one coalesced range of 2
assert_true(a.dirty_len == 1)
assert_true(a.dirty_start[0] == 0)
assert_true(a.dirty_count[0] == 2)
ui_scene_v2_write_row(a, p, 3, [3, 3, 3, 3])
assert_true(a.dirty_len == 2)
```

</details>

#### blocks swap until the back generation is sealed

- blocks swap until the back generation is sealed


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("blocks swap until the back generation is sealed")
val a = make_arena()
assert_true(a.try_swap() == UI_SCENE_V2_SWAP_BLOCKED)
```

</details>

#### GATE: two warm generations, zero commit-copy bytes, one allocation

- GATE: two warm generations, zero commit-copy bytes, one allocation


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("GATE: two warm generations, zero commit-copy bytes, one allocation")
val a = make_arena()
val p = a.lease_partition(1, 0, 4)
val q = a.lease_partition(2, 1, 2)
# generation 1
assert_true(ui_scene_v2_write_row(a, p, 0, [1, 2, 3, 4]) == UI_SCENE_V2_OK)
assert_true(ui_scene_v2_write_row(a, q, 0, [7, 8]) == UI_SCENE_V2_OK)
assert_true(ui_scene_v2_commit(a) == UI_SCENE_V2_OK)
# generation 2 — retained update of one stable word only
assert_true(ui_scene_v2_update_word(a, p, 0, 2, 33) == UI_SCENE_V2_OK)
assert_true(ui_scene_v2_commit(a) == UI_SCENE_V2_OK)
# the gate from plan §12.2 F3: no commit copy, no reallocation
assert_true(a.commit_copy_bytes == 0)
assert_true(a.alloc_count == 1)
assert_true(a.front_word(0, 0, 2) == 33)
```

</details>

#### incremental update marks exactly one dirty range

- incremental update marks exactly one dirty range


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("incremental update marks exactly one dirty range")
val a = make_arena()
val p = a.lease_partition(1, 0, 4)
ui_scene_v2_write_row(a, p, 0, [1, 2, 3, 4])
ui_scene_v2_commit(a)
assert_true(a.dirty_len == 0)
ui_scene_v2_update_word(a, p, 0, 1, 99)
assert_true(a.dirty_len == 1)
assert_true(a.dirty_count[0] == 1)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_sync_mut/ui/ui_scene_column_arena_v2_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering UiSceneColumnArenaV2 (F3) direct writes.
- UiSceneColumnArenaV2 (F3) direct writes

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

- Canonical SPipe generation for source `062695fca50506248b19d58594a012f7a83f2d650809551606fcecc6ee04552b`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `062695fca50506248b19d58594a012f7a83f2d650809551606fcecc6ee04552b`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `062695fca50506248b19d58594a012f7a83f2d650809551606fcecc6ee04552b`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/nogc_sync_mut/ui/ui_scene_column_arena_v2_spec.spl
mirror: doc/06_spec/01_unit/lib/nogc_sync_mut/ui/ui_scene_column_arena_v2_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/nogc_sync_mut/ui/ui_scene_column_arena_v2_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/nogc_sync_mut/ui/ui_scene_column_arena_v2_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/nogc_sync_mut/ui/ui_scene_column_arena_v2_spec.spl:31:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'leases stable partitions and refuses over-capacity leases' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/nogc_sync_mut/ui/ui_scene_column_arena_v2_spec.spl:42:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'writes rows directly and reads them back after swap' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/nogc_sync_mut/ui/ui_scene_column_arena_v2_spec.spl:53:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'refuses writes past the leased partition (typed refusal, no grow)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

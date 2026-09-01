# Segment Load Plan Specification

> Tests covering segment table parsing, segment plan per preload_mode, segment plan fail-closed paths.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 15 | 15 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Segment Load Plan Specification

## Scenarios

### segment table parsing

#### parses a well-formed table with all four kinds

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- parses a well-formed table with all four kinds


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses a well-formed table with all four kinds")
val t = parse_segment_table(sample_table_text())
assert_true(t.valid)
assert_eq(t.error, "")
assert_eq(t.rows.len(), 4)
assert_eq(t.rows[0].kind, "rx")
assert_eq(t.rows[0].offset, 0)
assert_eq(t.rows[0].len, 4096)
assert_eq(t.rows[3].kind, "bss")
```

</details>

#### ignores blank lines and comments

- ignores blank lines and comments


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("ignores blank lines and comments")
val t = parse_segment_table("# header\nsegments:\n\n  kind: r offset: 0 len: 8\n")
assert_true(t.valid)
assert_eq(t.rows.len(), 1)
```

</details>

#### fails closed on a missing segments: header

- fails closed on a missing segments: header


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("fails closed on a missing segments: header")
val t = parse_segment_table("kind: rx offset: 0 len: 16\n")
assert_false(t.valid)
assert_true(t.error != "")
assert_eq(t.rows.len(), 0)
```

</details>

#### fails closed on an unknown segment kind

- fails closed on an unknown segment kind


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("fails closed on an unknown segment kind")
val t = parse_segment_table("segments:\n  kind: wx offset: 0 len: 16\n")
assert_false(t.valid)
assert_true(t.error != "")
```

</details>

#### fails closed on a non-numeric offset

- fails closed on a non-numeric offset


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("fails closed on a non-numeric offset")
val t = parse_segment_table("segments:\n  kind: rx offset: abc len: 16\n")
assert_false(t.valid)
assert_true(t.error != "")
```

</details>

#### fails closed on a row missing a field

- fails closed on a row missing a field


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("fails closed on a row missing a field")
val t = parse_segment_table("segments:\n  kind: rx offset: 0\n")
assert_false(t.valid)
assert_true(t.error != "")
```

</details>

#### rejects zero-length segments

- rejects zero-length segments


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects zero-length segments")
val t = parse_segment_table("segments:\n  kind: rx offset: 0 len: 0\n")
assert_false(t.valid)
assert_true(t.error != "")
```

</details>

#### rejects overlapping file-backed segments

- rejects overlapping file-backed segments


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects overlapping file-backed segments")
val t = parse_segment_table(
    "segments:\n  kind: rx offset: 0 len: 4096\n  kind: r offset: 100 len: 64\n")
assert_false(t.valid)
assert_true(t.error != "")
```

</details>

#### allows bss to share offsets with file-backed segments

- allows bss to share offsets with file-backed segments


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("allows bss to share offsets with file-backed segments")
val t = parse_segment_table(
    "segments:\n  kind: rx offset: 0 len: 4096\n  kind: bss offset: 0 len: 64\n")
assert_true(t.valid)
```

</details>

### segment plan per preload_mode

#### map_selected_segments maps rx and r, skips rw and bss

- map_selected_segments maps rx and r, skips rw and bss


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("map_selected_segments maps rx and r, skips rw and bss")
val plan = segment_load_plan(
    decision_for(LOAD_POLICY_MAP_SELECTED_SEGMENTS),
    parse_segment_table(sample_table_text()))
assert_true(plan.planned)
assert_eq(plan.rows.len(), 4)
assert_eq(plan.rows[0].action, segment_action_map_read_only())
assert_eq(plan.rows[1].action, segment_action_map_read_only())
assert_eq(plan.rows[2].action, segment_action_skip())
assert_eq(plan.rows[3].action, segment_action_skip())
assert_eq(plan.rows[0].offset, 0)
assert_eq(plan.rows[0].len, 4096)
```

</details>

#### read_ahead_selected schedules reads for all file-backed segments

- read_ahead_selected schedules reads for all file-backed segments


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("read_ahead_selected schedules reads for all file-backed segments")
val plan = segment_load_plan(
    decision_for(LOAD_POLICY_READ_AHEAD_SELECTED),
    parse_segment_table(sample_table_text()))
assert_true(plan.planned)
assert_eq(plan.rows[0].action, segment_action_read_ahead())
assert_eq(plan.rows[1].action, segment_action_read_ahead())
assert_eq(plan.rows[2].action, segment_action_read_ahead())
assert_eq(plan.rows[3].action, segment_action_skip())
```

</details>

#### normal policy loads nothing eagerly but still plans

- normal policy loads nothing eagerly but still plans


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("normal policy loads nothing eagerly but still plans")
val plan = segment_load_plan(
    decision_for(LOAD_POLICY_NORMAL),
    parse_segment_table(sample_table_text()))
assert_true(plan.planned)
assert_true(plan.reason != "")
assert_eq(plan.rows[0].action, segment_action_skip())
assert_eq(plan.rows[1].action, segment_action_skip())
assert_eq(plan.rows[2].action, segment_action_skip())
```

</details>

### segment plan fail-closed paths

#### invalid decision produces an empty plan with an explicit reason

- invalid decision produces an empty plan with an explicit reason


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("invalid decision produces an empty plan with an explicit reason")
val plan = segment_load_plan(
    decision_for("bogus_policy"),
    parse_segment_table(sample_table_text()))
assert_false(plan.planned)
assert_eq(plan.rows.len(), 0)
assert_true(plan.reason != "")
```

</details>

#### invalid table produces an empty plan with an explicit reason

- invalid table produces an empty plan with an explicit reason


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("invalid table produces an empty plan with an explicit reason")
val plan = segment_load_plan(
    decision_for(LOAD_POLICY_MAP_SELECTED_SEGMENTS),
    parse_segment_table("segments:\n  kind: rx offset: 0 len: 0\n"))
assert_false(plan.planned)
assert_eq(plan.rows.len(), 0)
assert_true(plan.reason != "")
```

</details>

#### empty table yields an empty but planned plan

- empty table yields an empty but planned plan


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("empty table yields an empty but planned plan")
val plan = segment_load_plan(
    decision_for(LOAD_POLICY_MAP_SELECTED_SEGMENTS),
    parse_segment_table("segments:\n"))
assert_true(plan.planned)
assert_eq(plan.rows.len(), 0)
assert_true(plan.reason != "")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/startup/segment_load_plan_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering segment table parsing, segment plan per preload_mode, segment plan fail-closed paths.
- segment table parsing
- segment plan per preload_mode
- segment plan fail-closed paths

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 15 |
| Active scenarios | 15 |
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

- Canonical SPipe generation for source `0a8cb4274019c9762d1edc8f671515208ee4d41ab75147922d9c9a262b440a7b`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `0a8cb4274019c9762d1edc8f671515208ee4d41ab75147922d9c9a262b440a7b`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `0a8cb4274019c9762d1edc8f671515208ee4d41ab75147922d9c9a262b440a7b`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/app/startup/segment_load_plan_spec.spl
mirror: doc/06_spec/01_unit/app/startup/segment_load_plan_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/app/startup/segment_load_plan_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/startup/segment_load_plan_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/startup/segment_load_plan_spec.spl:47:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses a well-formed table with all four kinds' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/startup/segment_load_plan_spec.spl:59:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'ignores blank lines and comments' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/startup/segment_load_plan_spec.spl:66:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'fails closed on a missing segments: header' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

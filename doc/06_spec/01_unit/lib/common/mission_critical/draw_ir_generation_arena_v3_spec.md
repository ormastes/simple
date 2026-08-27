# Draw Ir Generation Arena V3 Specification

> Tests covering bounded Draw IR generation arena v3.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Draw Ir Generation Arena V3 Specification

## Scenarios

### bounded Draw IR generation arena v3

#### admits and seals an exact-capacity generation

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- admits and seals an exact-capacity generation
   - Expected: admitted is true
   - Expected: arena.retire() is true
   - Expected: arena.next_generation equals `2u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("admits and seals an exact-capacity generation")
val counts = draw_ir_generation_count_v3(2u32, 1u32, 1u32, 1u32, 1u32, 2u32)
val planned = draw_ir_generation_plan_v3(7u64, 1u64, counts, 8u64, 64u64, 8u64)
var arena = DrawIrGenerationArenaV3.bounded(7u64, 64u64, 8u64)
var admitted = false
match planned:
    DrawIrPlanOutcomeV3.Planned(plan):
        match arena.admit(plan):
            DrawIrAdmissionOutcomeV3.Admitted(accepted):
                admitted = accepted.total_bytes == 64u64
            DrawIrAdmissionOutcomeV3.Refused(receipt):
                admitted = false
    DrawIrPlanOutcomeV3.Refused(receipt):
        admitted = false
expect(admitted).to_equal(true)
expect(arena.seal(64u64, 8u64)).to_be_nil()
expect(arena.retire()).to_equal(true)
expect(arena.next_generation).to_equal(2u64)
```

</details>

#### rejects one row over capacity before arena mutation

- rejects one row over capacity before arena mutation
   - Expected: reason equals `DRAW_IR_OVERFLOW_COUNT`
   - Expected: arena.active is false
   - Expected: arena.admitted_bytes equals `0u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects one row over capacity before arena mutation")
val counts = draw_ir_generation_count_v3(9u32, 0u32, 0u32, 0u32, 0u32, 0u32)
val planned = draw_ir_generation_plan_v3(8u64, 1u64, counts, 8u64, 64u64, 8u64)
var arena = DrawIrGenerationArenaV3.bounded(8u64, 64u64, 8u64)
var reason = 0u16
match planned:
    DrawIrPlanOutcomeV3.Refused(receipt):
        reason = receipt.reason
    DrawIrPlanOutcomeV3.Planned(plan):
        reason = 99u16
expect(reason).to_equal(DRAW_IR_OVERFLOW_COUNT)
expect(arena.active).to_equal(false)
expect(arena.admitted_bytes).to_equal(0u64)
```

</details>

#### does not grow an active generation

- does not grow an active generation
   - Expected: reason equals `DRAW_IR_OVERFLOW_ACTIVE_GENERATION`
   - Expected: arena.admitted_bytes equals `8u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does not grow an active generation")
val counts = draw_ir_generation_count_v3(1u32, 0u32, 0u32, 0u32, 0u32, 0u32)
val planned = draw_ir_generation_plan_v3(9u64, 1u64, counts, 8u64, 64u64, 8u64)
var arena = DrawIrGenerationArenaV3.bounded(9u64, 64u64, 8u64)
var reason = 0u16
match planned:
    DrawIrPlanOutcomeV3.Planned(plan):
        arena.admit(plan)
        match arena.admit(plan):
            DrawIrAdmissionOutcomeV3.Refused(receipt):
                reason = receipt.reason
            DrawIrAdmissionOutcomeV3.Admitted(accepted):
                reason = 99u16
    DrawIrPlanOutcomeV3.Refused(receipt):
        reason = receipt.reason
expect(reason).to_equal(DRAW_IR_OVERFLOW_ACTIVE_GENERATION)
expect(arena.admitted_bytes).to_equal(8u64)
```

</details>

#### rejects a plan created for another arena before mutation

- rejects a plan created for another arena before mutation
   - Expected: reason equals `DRAW_IR_OVERFLOW_PLAN_MISMATCH`
   - Expected: arena.active is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects a plan created for another arena before mutation")
val counts = draw_ir_generation_count_v3(1u32, 0u32, 0u32, 0u32, 0u32, 0u32)
val planned = draw_ir_generation_plan_v3(99u64, 1u64, counts, 8u64, 64u64, 8u64)
var arena = DrawIrGenerationArenaV3.bounded(10u64, 64u64, 8u64)
var reason = 0u16
match planned:
    DrawIrPlanOutcomeV3.Planned(plan):
        match arena.admit(plan):
            DrawIrAdmissionOutcomeV3.Refused(receipt):
                reason = receipt.reason
            DrawIrAdmissionOutcomeV3.Admitted(accepted):
                reason = 99u16
    DrawIrPlanOutcomeV3.Refused(receipt):
        reason = receipt.reason
expect(reason).to_equal(DRAW_IR_OVERFLOW_PLAN_MISMATCH)
expect(arena.active).to_equal(false)
```

</details>

#### recomputes forged row and byte totals before admission

- recomputes forged row and byte totals before admission
   - Expected: row_reason equals `DRAW_IR_OVERFLOW_PLAN_MISMATCH`
   - Expected: arena.active is false
   - Expected: byte_reason equals `DRAW_IR_OVERFLOW_PLAN_MISMATCH`
   - Expected: arena.admitted_bytes equals `0u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 29 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("recomputes forged row and byte totals before admission")
val counts = draw_ir_generation_count_v3(2u32, 0u32, 0u32, 0u32, 0u32, 0u32)
var arena = DrawIrGenerationArenaV3.bounded(11u64, 64u64, 8u64)
val forged_rows = DrawIrGenerationPlanV3(
    arena_id: 11u64, generation: 1u64, counts: counts,
    total_rows: 1u64, total_bytes: 8u64,
    layout_id: DRAW_IR_LAYOUT_PACKED_V3,
    bytes_per_row: DRAW_IR_PACKED_BYTES_PER_ROW_V3
)
var row_reason = 0u16
match arena.admit(forged_rows):
    DrawIrAdmissionOutcomeV3.Refused(receipt): row_reason = receipt.reason
    DrawIrAdmissionOutcomeV3.Admitted(accepted): row_reason = 99u16
expect(row_reason).to_equal(DRAW_IR_OVERFLOW_PLAN_MISMATCH)
expect(arena.active).to_equal(false)

val forged_bytes = DrawIrGenerationPlanV3(
    arena_id: 11u64, generation: 1u64, counts: counts,
    total_rows: 2u64, total_bytes: 8u64,
    layout_id: DRAW_IR_LAYOUT_PACKED_V3,
    bytes_per_row: DRAW_IR_PACKED_BYTES_PER_ROW_V3
)
var byte_reason = 0u16
match arena.admit(forged_bytes):
    DrawIrAdmissionOutcomeV3.Refused(receipt): byte_reason = receipt.reason
    DrawIrAdmissionOutcomeV3.Admitted(accepted): byte_reason = 99u16
expect(byte_reason).to_equal(DRAW_IR_OVERFLOW_PLAN_MISMATCH)
expect(arena.admitted_bytes).to_equal(0u64)
```

</details>

#### binds admission to packed layout identity and row width

- binds admission to packed layout identity and row width
   - Expected: layout_reason equals `DRAW_IR_OVERFLOW_PLAN_MISMATCH`
   - Expected: width_reason equals `DRAW_IR_OVERFLOW_PLAN_MISMATCH`
   - Expected: arena.active is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("binds admission to packed layout identity and row width")
val counts = draw_ir_generation_count_v3(1u32, 0u32, 0u32, 0u32, 0u32, 0u32)
var arena = DrawIrGenerationArenaV3.bounded(12u64, 64u64, 8u64)
val forged_layout = DrawIrGenerationPlanV3(
    arena_id: 12u64, generation: 1u64, counts: counts,
    total_rows: 1u64, total_bytes: 8u64,
    layout_id: 99u64, bytes_per_row: DRAW_IR_PACKED_BYTES_PER_ROW_V3
)
val forged_width = DrawIrGenerationPlanV3(
    arena_id: 12u64, generation: 1u64, counts: counts,
    total_rows: 1u64, total_bytes: 16u64,
    layout_id: DRAW_IR_LAYOUT_PACKED_V3, bytes_per_row: 16u64
)
var layout_reason = 0u16
var width_reason = 0u16
match arena.admit(forged_layout):
    DrawIrAdmissionOutcomeV3.Refused(receipt): layout_reason = receipt.reason
    DrawIrAdmissionOutcomeV3.Admitted(accepted): layout_reason = 99u16
match arena.admit(forged_width):
    DrawIrAdmissionOutcomeV3.Refused(receipt): width_reason = receipt.reason
    DrawIrAdmissionOutcomeV3.Admitted(accepted): width_reason = 99u16
expect(layout_reason).to_equal(DRAW_IR_OVERFLOW_PLAN_MISMATCH)
expect(width_reason).to_equal(DRAW_IR_OVERFLOW_PLAN_MISMATCH)
expect(arena.active).to_equal(false)
```

</details>

#### aborts a failed seal without publication and admits the next generation

- aborts a failed seal without publication and admits the next generation
   - Expected: mismatch_seen is true
   - Expected: arena.sealed is false
   - Expected: arena.retire() is false
   - Expected: advanced is true
   - Expected: arena.active is false
   - Expected: arena.admitted_bytes equals `0u64`
   - Expected: next_admitted is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 32 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("aborts a failed seal without publication and admits the next generation")
val counts = draw_ir_generation_count_v3(1u32, 0u32, 0u32, 0u32, 0u32, 0u32)
var arena = DrawIrGenerationArenaV3.bounded(13u64, 64u64, 8u64)
val first = draw_ir_generation_plan_v3(13u64, 1u64, counts, 8u64, 64u64, 8u64)
match first:
    DrawIrPlanOutcomeV3.Planned(plan): arena.admit(plan)
    DrawIrPlanOutcomeV3.Refused(receipt): expect(false).to_equal(true)
val mismatch = arena.seal(7u64, 1u64)
var mismatch_seen = false
if val receipt = mismatch:
    mismatch_seen = receipt.reason == DRAW_IR_OVERFLOW_PLAN_MISMATCH
expect(mismatch_seen).to_equal(true)
expect(arena.sealed).to_equal(false)
expect(arena.retire()).to_equal(false)
var advanced = false
match arena.abort():
    DrawIrTerminalOutcomeV3.Advanced(generation): advanced = generation == 2u64
    DrawIrTerminalOutcomeV3.Refused(receipt): advanced = false
expect(advanced).to_equal(true)
expect(arena.active).to_equal(false)
expect(arena.admitted_bytes).to_equal(0u64)

val second = draw_ir_generation_plan_v3(13u64, 2u64, counts, 8u64, 64u64, 8u64)
var next_admitted = false
match second:
    DrawIrPlanOutcomeV3.Planned(plan):
        match arena.admit(plan):
            DrawIrAdmissionOutcomeV3.Admitted(accepted): next_admitted = true
            DrawIrAdmissionOutcomeV3.Refused(receipt): next_admitted = false
    DrawIrPlanOutcomeV3.Refused(receipt): next_admitted = false
expect(next_admitted).to_equal(true)
```

</details>

#### rejects terminal generation advance without wrapping

- rejects terminal generation advance without wrapping
   - Expected: reason equals `DRAW_IR_OVERFLOW_GENERATION_EXHAUSTED`
   - Expected: arena.next_generation equals `0xFFFFFFFFFFFFFFFFu64`
   - Expected: arena.terminal is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects terminal generation advance without wrapping")
val counts = draw_ir_generation_count_v3(1u32, 0u32, 0u32, 0u32, 0u32, 0u32)
var arena = DrawIrGenerationArenaV3.bounded(14u64, 64u64, 8u64)
arena.next_generation = 0xFFFFFFFFFFFFFFFFu64
val planned = draw_ir_generation_plan_v3(
    14u64, 0xFFFFFFFFFFFFFFFFu64, counts, 8u64, 64u64, 8u64
)
match planned:
    DrawIrPlanOutcomeV3.Planned(plan): arena.admit(plan)
    DrawIrPlanOutcomeV3.Refused(receipt): expect(false).to_equal(true)
expect(arena.seal(8u64, 1u64)).to_be_nil()
var reason = 0u16
match arena.retire_checked():
    DrawIrTerminalOutcomeV3.Refused(receipt): reason = receipt.reason
    DrawIrTerminalOutcomeV3.Advanced(generation): reason = 99u16
expect(reason).to_equal(DRAW_IR_OVERFLOW_GENERATION_EXHAUSTED)
expect(arena.next_generation).to_equal(0xFFFFFFFFFFFFFFFFu64)
expect(arena.terminal).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/mission_critical/draw_ir_generation_arena_v3_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering bounded Draw IR generation arena v3.
- bounded Draw IR generation arena v3

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
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

- Canonical SPipe generation for source `8d9ca68d2c9bc50c25bf64436caaeb71dc7816505762f7ca20b291e23baab24f`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `8d9ca68d2c9bc50c25bf64436caaeb71dc7816505762f7ca20b291e23baab24f`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `8d9ca68d2c9bc50c25bf64436caaeb71dc7816505762f7ca20b291e23baab24f`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/common/mission_critical/draw_ir_generation_arena_v3_spec.spl
mirror: doc/06_spec/01_unit/lib/common/mission_critical/draw_ir_generation_arena_v3_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/common/mission_critical/draw_ir_generation_arena_v3_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/mission_critical/draw_ir_generation_arena_v3_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/mission_critical/draw_ir_generation_arena_v3_spec.spl:16:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'admits and seals an exact-capacity generation' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/mission_critical/draw_ir_generation_arena_v3_spec.spl:37:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects one row over capacity before arena mutation' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/mission_critical/draw_ir_generation_arena_v3_spec.spl:53:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'does not grow an active generation' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

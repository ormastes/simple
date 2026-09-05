# Dbg1 Block Specification

> Tests covering DBG-1 block placement — non-overlap with every other arena region, DBG-1 block placement — internal field layout, DBG-1 block encode/decode, DBG-1 writes do not disturb any other arena region.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 16 | 16 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Dbg1 Block Specification

## Scenarios

### DBG-1 block placement — non-overlap with every other arena region

#### starts above the DATA region, so no program STORE can reach it

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- starts above the DATA region, so no program STORE can reach it


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("starts above the DATA region, so no program STORE can reach it")
# bounds_ok() in ref_vm limits LOAD/STORE to offset+width <=
# ARENA_DATA_SIZE, so this inequality is what makes the debug block
# unreachable from bytecode — a program cannot forge its own
# breakpoints or corrupt its saved state.
assert_true(DBG_BASE_OFFSET >= ARENA_DATA_SIZE)
```

</details>

#### starts above the REG mailbox command block

- starts above the REG mailbox command block


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("starts above the REG mailbox command block")
assert_true(DBG_BASE_OFFSET >= REG_BASE_OFFSET + REG_BLOCK_SIZE)
```

</details>

#### starts above the LOG ring's last byte at the default capacity

- starts above the LOG ring's last byte at the default capacity


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("starts above the LOG ring's last byte at the default capacity")
assert_true(DBG_BASE_OFFSET >= LOG_DATA_OFFSET + DEFAULT_LOG_CAP)
```

</details>

#### starts above the RECORD ring's base at the default capacity

- starts above the RECORD ring's base at the default capacity


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("starts above the RECORD ring's base at the default capacity")
assert_true(DBG_BASE_OFFSET >= record_ring_base_offset(DEFAULT_LOG_CAP))
```

</details>

#### ends exactly at the top of the arena, never past it

- ends exactly at the top of the arena, never past it


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("ends exactly at the top of the arena, never past it")
assert_equal(DBG_BASE_OFFSET + DBG_BLOCK_SIZE, ARENA_TOTAL_SIZE)
```

</details>

#### uses no more than the space it reserves

- uses no more than the space it reserves


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("uses no more than the space it reserves")
assert_true(DBG_USED_SIZE <= DBG_BLOCK_SIZE)
```

</details>

#### leaves the RECORD ring a positive, stated capacity before it would collide

- leaves the RECORD ring a positive, stated capacity before it would collide


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("leaves the RECORD ring a positive, stated capacity before it would collide")
val cap = max_record_count(DEFAULT_LOG_CAP)
assert_true(cap > 0)
# The bound must be tight in the right direction: the last record
# that fits must END at or below the DBG block, and one more must not.
val base = record_ring_base_offset(DEFAULT_LOG_CAP)
assert_true(base + cap * RECORD_SIZE <= DBG_BASE_OFFSET)
assert_true(base + (cap + 1) * RECORD_SIZE > DBG_BASE_OFFSET)
```

</details>

### DBG-1 block placement — internal field layout

#### lays the fields out in ascending order with no field overlapping the next

- lays the fields out in ascending order with no field overlapping the next


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("lays the fields out in ascending order with no field overlapping the next")
assert_equal(DBG_FLAGS_OFFSET + 4, DBG_BREAK_COUNT_OFFSET)
assert_equal(DBG_BREAK_COUNT_OFFSET + 4, DBG_BREAK_PCS_OFFSET)
assert_equal(DBG_BREAK_PCS_OFFSET + DBG_MAX_BREAKPOINTS * 4, DBG_SAVED_PC_OFFSET)
assert_equal(DBG_SAVED_PC_OFFSET + 4, DBG_SAVED_SP_OFFSET)
assert_equal(DBG_SAVED_SP_OFFSET + 4, DBG_SAVED_CSP_OFFSET)
assert_equal(DBG_SAVED_CSP_OFFSET + 4, DBG_STEP_COUNT_OFFSET)
assert_equal(DBG_STEP_COUNT_OFFSET + 4, DBG_SAVED_STACK_OFFSET)
assert_equal(DBG_SAVED_STACK_OFFSET + 256 * 4, DBG_SAVED_CALLS_OFFSET)
assert_equal(DBG_SAVED_CALLS_OFFSET + 32 * 4, DBG_SAVED_SEQ_OFFSET)
assert_equal(DBG_SAVED_SEQ_OFFSET + 4, DBG_SAVED_RECORD_COUNT_OFFSET)
assert_equal(DBG_SAVED_RECORD_COUNT_OFFSET + 4, DBG_BASE_OFFSET + DBG_USED_SIZE)
```

</details>

#### sizes the saved stacks to match the VM's actual stack capacities

- sizes the saved stacks to match the VM's actual stack capacities


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("sizes the saved stacks to match the VM's actual stack capacities")
# If OPERAND_STACK_SIZE or CALL_STACK_SIZE ever grows, the saved
# region must grow with it or save_debug_state would write past its
# own field. Asserted against the VM's own constants, not literals.
assert_equal(DBG_SAVED_CALLS_OFFSET - DBG_SAVED_STACK_OFFSET, OPERAND_STACK_SIZE * 4)
assert_equal(DBG_SAVED_SEQ_OFFSET - DBG_SAVED_CALLS_OFFSET, CALL_STACK_SIZE * 4)
```

</details>

#### gives the debug-break sentinel a value distinct from the timeout sentinel

- gives the debug-break sentinel a value distinct from the timeout sentinel


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("gives the debug-break sentinel a value distinct from the timeout sentinel")
assert_true(SENTINEL_DEBUG_BREAK != SENTINEL_TIMEOUT)
# It is in the 0xCAFE00Dx family the design pins it to, which means
# it aliases exit code 0xDB — documented and reserved, and asserted
# here so the aliasing can never be forgotten.
assert_equal(SENTINEL_DEBUG_BREAK, SENTINEL_EXIT_MASK | DEBUG_BREAK_EXIT_CODE)
```

</details>

### DBG-1 block encode/decode

#### round-trips DBG_FLAGS

- round-trips DBG_FLAGS


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("round-trips DBG_FLAGS")
val arena = dbg_set_flags(_fresh_arena(), DBG_FLAG_ENABLED | DBG_FLAG_SINGLE_STEP)
assert_equal(dbg_read_flags(arena), DBG_FLAG_ENABLED | DBG_FLAG_SINGLE_STEP)
```

</details>

#### reads DBG_FLAGS as zero on an arena that was never debugged

- reads DBG_FLAGS as zero on an arena that was never debugged


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reads DBG_FLAGS as zero on an arena that was never debugged")
assert_equal(dbg_read_flags(_fresh_arena()), 0)
```

</details>

#### round-trips a full breakpoint table without dropping the last entry

- round-trips a full breakpoint table without dropping the last entry


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("round-trips a full breakpoint table without dropping the last entry")
var pcs: [i64] = []
var i = 0
while i < DBG_MAX_BREAKPOINTS:
    pcs.push(1000 + i * 7)
    i = i + 1
val arena = dbg_set_breakpoints(_fresh_arena(), pcs)
assert_equal(dbg_read_break_count(arena), DBG_MAX_BREAKPOINTS)
i = 0
while i < DBG_MAX_BREAKPOINTS:
    assert_equal(dbg_read_breakpoint(arena, i), 1000 + i * 7)
    i = i + 1
```

</details>

#### round-trips an empty breakpoint table as a count of zero

- round-trips an empty breakpoint table as a count of zero


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("round-trips an empty breakpoint table as a count of zero")
val arena = dbg_set_breakpoints(_fresh_arena(), [])
assert_equal(dbg_read_break_count(arena), 0)
```

</details>

### DBG-1 writes do not disturb any other arena region

#### leaves the REG block, LOG ring and RECORD ring byte-identical

- leaves the REG block, LOG ring and RECORD ring byte-identical


<details>
<summary>Executable SSpec</summary>

Runnable source: 30 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("leaves the REG block, LOG ring and RECORD ring byte-identical")
val before = _fresh_arena()
var pcs: [i64] = []
var i = 0
while i < DBG_MAX_BREAKPOINTS:
    pcs.push(0xFFFFFF)
    i = i + 1
var after = dbg_set_breakpoints(before, pcs)
after = dbg_set_flags(after, 0xFFFFFFFF)

# Every byte from the start of the REG block through the end of the
# RECORD ring's reserved span must be untouched. This is the check
# that arithmetic non-overlap cannot give you.
var idx = REG_BASE_OFFSET
var differing = 0
while idx < DBG_BASE_OFFSET:
    if before[idx] != after[idx]:
        differing = differing + 1
    idx = idx + 1
assert_equal(differing, 0)

# And the DATA region (the SGP blob) is likewise untouched.
idx = 0
differing = 0
while idx < ARENA_DATA_SIZE:
    if before[idx] != after[idx]:
        differing = differing + 1
    idx = idx + 1
assert_equal(differing, 0)
```

</details>

#### actually wrote something, so the previous check is not vacuous

- actually wrote something, so the previous check is not vacuous


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("actually wrote something, so the previous check is not vacuous")
# A non-overlap test that passes because nothing was written at all
# is worthless; prove the DBG region really did change.
val before = _fresh_arena()
val after = dbg_set_flags(before, DBG_FLAG_ENABLED)
assert_equal(_u32_at(before, DBG_FLAGS_OFFSET), 0)
assert_equal(_u32_at(after, DBG_FLAGS_OFFSET), DBG_FLAG_ENABLED)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/svmg/dbg1_block_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering DBG-1 block placement — non-overlap with every other arena region, DBG-1 block placement — internal field layout, DBG-1 block encode/decode, DBG-1 writes do not disturb any other arena region.
- DBG-1 block placement — non-overlap with every other arena region
- DBG-1 block placement — internal field layout
- DBG-1 block encode/decode
- DBG-1 writes do not disturb any other arena region

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 16 |
| Active scenarios | 16 |
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

- Canonical SPipe generation for source `2685c367eda5c45995eedac804c9b7bdb8938e988042c553caa25b990302edb8`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `2685c367eda5c45995eedac804c9b7bdb8938e988042c553caa25b990302edb8`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `2685c367eda5c45995eedac804c9b7bdb8938e988042c553caa25b990302edb8`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/svmg/dbg1_block_spec.spl
mirror: doc/06_spec/01_unit/lib/svmg/dbg1_block_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/svmg/dbg1_block_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/svmg/dbg1_block_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/svmg/dbg1_block_spec.spl:41:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'starts above the DATA region, so no program STORE can reach it' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/svmg/dbg1_block_spec.spl:50:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'starts above the REG mailbox command block' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/svmg/dbg1_block_spec.spl:55:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'starts above the LOG ring's last byte at the default capacity' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

# Ssa Alloca Value Return Slotting Specification

> Tests covering SSA alloca slotting for value-returning functions.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Ssa Alloca Value Return Slotting Specification

## Scenarios

### SSA alloca slotting for value-returning functions

#### admits a value-returning function instead of rejecting it outright

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- admits a value-returning function instead of rejecting it outright


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("admits a value-returning function instead of rejecting it outright")
val result = transform_cross_block_return(MirConstValue.Bool(true), MirType.bool())
# Before the fix this was `false` with reason
# "unsupported value return terminator".
assert_true(result.applied)
assert_not_equal(result.reason, "unsupported value return terminator")
```

</details>

#### counts a returned local as a use so it is slotted

- counts a returned local as a use so it is slotted


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("counts a returned local as a use so it is slotted")
val result = transform_cross_block_return(MirConstValue.Bool(true), MirType.bool())
# Second gate: with admission fixed but the liveness scan still blind to
# Ret, this rejected with "no slotted locals".
assert_not_equal(result.reason, "no slotted locals")
assert_true(result.applied)
```

</details>

#### keeps the defining constant and its slot store in the entry block

- keeps the defining constant and its slot store in the entry block


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps the defining constant and its slot store in the entry block")
val result = transform_cross_block_return(MirConstValue.Bool(true), MirType.bool())
# The whole point of the original bug: the def and its store survive.
assert_equal(entry_shape(result), "Alloc Const Store")
```

</details>

#### loads the slot back out in the returning block

- loads the slot back out in the returning block


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("loads the slot back out in the returning block")
val result = transform_cross_block_return(MirConstValue.Bool(true), MirType.bool())
val ret_block = result.blocks[1]
assert_equal(ret_block.instructions.len(), 1)
assert_equal(inst_kind_name(ret_block.instructions[0].kind), "Load")
```

</details>

#### returns the loaded temporary, not the now-undefined original local

- returns the loaded temporary, not the now-undefined original local


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns the loaded temporary, not the now-undefined original local")
val result = transform_cross_block_return(MirConstValue.Bool(true), MirType.bool())
val ret_block = result.blocks[1]
var loaded_id = -1
match ret_block.instructions[0].kind:
    case Load(dest, _): loaded_id = dest.id
    case _: loaded_id = -1
assert_true(loaded_id >= 0)
var returned_id = -1
match ret_block.terminator:
    case Ret(returned):
        match returned.unwrap().kind:
            case Copy(l): returned_id = l.id
            case _: returned_id = -1
    case _: returned_id = -1
# Returning local 5 here is exactly the `ret` of a value with no def.
assert_not_equal(returned_id, 5)
assert_equal(returned_id, loaded_id)
```

</details>

#### applies the same rewrite to a text-pointer return

- applies the same rewrite to a text-pointer return


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("applies the same rewrite to a text-pointer return")
# The adjacent case from the original report: a pointer-typed constant.
val result = transform_cross_block_return(
    MirConstValue.Str("linux"),
    MirType.ptr(MirType.i64(), false)
)
assert_true(result.applied)
assert_equal(entry_shape(result), "Alloc Const Store")
assert_equal(result.blocks[1].instructions.len(), 1)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/mir_opt/ssa_alloca_value_return_slotting_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering SSA alloca slotting for value-returning functions.
- SSA alloca slotting for value-returning functions

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
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

- Canonical SPipe generation for source `93bfa65db7d21f77e1aa511b1fc0dbd05e26f7d765c810f0632a7230ce40bbe2`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `93bfa65db7d21f77e1aa511b1fc0dbd05e26f7d765c810f0632a7230ce40bbe2`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `93bfa65db7d21f77e1aa511b1fc0dbd05e26f7d765c810f0632a7230ce40bbe2`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/compiler/mir_opt/ssa_alloca_value_return_slotting_spec.spl
mirror: doc/06_spec/01_unit/compiler/mir_opt/ssa_alloca_value_return_slotting_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/mir_opt/ssa_alloca_value_return_slotting_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/mir_opt/ssa_alloca_value_return_slotting_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/mir_opt/ssa_alloca_value_return_slotting_spec.spl:79:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'admits a value-returning function instead of rejecting it outright' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/mir_opt/ssa_alloca_value_return_slotting_spec.spl:88:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'counts a returned local as a use so it is slotted' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/mir_opt/ssa_alloca_value_return_slotting_spec.spl:97:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps the defining constant and its slot store in the entry block' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

# LoopInvariantMotion Specification

> Validates the LoopInvariantMotion pass which hoists loop-invariant loads and binary operations above the loop header. The pass delegates ReadAheadHoist for Load/Call hoisting and adds BinOp/Copy hoisting. Side-effecting instructions and instructions with loop-dependent operands must not be hoisted.

<!-- sdn-diagram:id=loop_invariant_motion_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=loop_invariant_motion_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

loop_invariant_motion_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=loop_invariant_motion_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# LoopInvariantMotion Specification

Validates the LoopInvariantMotion pass which hoists loop-invariant loads and binary operations above the loop header. The pass delegates ReadAheadHoist for Load/Call hoisting and adds BinOp/Copy hoisting. Side-effecting instructions and instructions with loop-dependent operands must not be hoisted.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #web-server-optimizer-complete |
| Category | Compiler / MIR Optimization |
| Difficulty | 3/5 |
| Status | Draft |
| Source | `test/01_unit/compiler/mir_opt/loop_invariant_motion_spec.spl` |
| Updated | 2026-07-06 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Validates the LoopInvariantMotion pass which hoists loop-invariant loads
and binary operations above the loop header. The pass delegates
ReadAheadHoist for Load/Call hoisting and adds BinOp/Copy hoisting.
Side-effecting instructions and instructions with loop-dependent operands
must not be hoisted.

## Behavior

- Loop-invariant Load above loop header → hoisted
- Loop-invariant BinOp above loop header → hoisted
- Instruction with loop-dependent operand → not hoisted
- Instruction with side effects → not hoisted
- Pass statistics count every hoisted instruction

## Scenarios

### LoopInvariantMotion

### Load hoisting

<details>
<summary>Advanced: hoists loop-invariant load above loop header</summary>

#### hoists loop-invariant load above loop header

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# load_base is not a loop variable — it is invariant.
val loop_vars = ["%i", "%sum"]
val operands = ["%base_ptr"]
val is_inv = is_loop_inv(operands, loop_vars)
expect(is_inv).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: does not hoist load whose address depends on loop induction variable</summary>

#### does not hoist load whose address depends on loop induction variable

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val loop_vars = ["%i", "%sum"]
val operands = ["%i"]
val is_inv = is_loop_inv(operands, loop_vars)
expect(is_inv).to_equal(false)
```

</details>


</details>

### BinOp hoisting

<details>
<summary>Advanced: hoists loop-invariant binop above loop header</summary>

#### hoists loop-invariant binop above loop header

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val loop_vars = ["%i"]
val operands = ["%width", "%height"]
val is_inv = is_loop_inv(operands, loop_vars)
expect(is_inv).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: does not hoist instruction with loop-dependent operand</summary>

#### does not hoist instruction with loop-dependent operand

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val loop_vars = ["%i"]
val operands = ["%i", "%stride"]
val is_inv = is_loop_inv(operands, loop_vars)
expect(is_inv).to_equal(false)
```

</details>


</details>

### side-effect guard

#### does not hoist instruction with side effects

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val kind = "Store"
val is_se = has_side_effects(kind)
expect(is_se).to_equal(true)
```

</details>

#### treats pure Load as free of side effects

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val kind = "Load"
val is_se = has_side_effects(kind)
expect(is_se).to_equal(false)
```

</details>

### combined LICM simulation

<details>
<summary>Advanced: hoists only invariant non-side-effecting instructions from loop body</summary>

#### hoists only invariant non-side-effecting instructions from loop body

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Instructions: "%base_ptr" (invariant), "%i" (loop var), "%store" (side effect)
val loop_vars = ["%i"]
val side_effects = ["%store"]
val instructions = ["%base_ptr", "%i", "%store"]
val hoisted = simulate_licm(instructions, loop_vars, side_effects)
expect(hoisted.len()).to_equal(1)
expect(hoisted[0]).to_equal("%base_ptr")
```

</details>


</details>

### pass statistics

#### counts hoisted instructions in pass statistics

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val loop_vars = ["%i"]
val side_effects: List<text> = []
val instructions = ["%base", "%scale", "%i"]
val hoisted = simulate_licm(instructions, loop_vars, side_effects)
val count = simulate_hoist_stats(hoisted)
expect(count).to_equal(2)
expect(count).to_be_greater_than(0)
```

</details>

<details>
<summary>Advanced: reports zero hoisted when all instructions are loop-dependent</summary>

#### reports zero hoisted when all instructions are loop-dependent

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val loop_vars = ["%i", "%j"]
val side_effects: List<text> = []
val instructions = ["%i", "%j"]
val hoisted = simulate_licm(instructions, loop_vars, side_effects)
val count = simulate_hoist_stats(hoisted)
expect(count).to_equal(0)
```

</details>


</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

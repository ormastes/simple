# Mir Ssa Phi Intrinsic Specification

> 1. var interp = MirInterpreter create

<!-- sdn-diagram:id=mir_ssa_phi_intrinsic_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=mir_ssa_phi_intrinsic_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

mir_ssa_phi_intrinsic_spec -> std
mir_ssa_phi_intrinsic_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=mir_ssa_phi_intrinsic_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Mir Ssa Phi Intrinsic Specification

## Scenarios

### MIR interpreter pseudo SSA phi intrinsic

#### uses the first incoming value as linear fallback

1. var interp = MirInterpreter create
2. interp set local
3. interp set local
4. Some
5. [phi copy
   - Expected: err.? is false
   - Expected: interp.get_local(phi_local(12)) equals `41`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var interp = MirInterpreter.create()
interp.set_local(phi_local(10), 41)
interp.set_local(phi_local(11), 99)
val inst = MirInst(
    kind: MirInstKind.Intrinsic(
        Some(phi_local(12)),
        "__simple_ssa_phi",
        [phi_copy(10), phi_copy(11)]
    ),
    span: nil
)
val err = interp.execute_instruction(inst)
expect(err.?).to_equal(false)
expect(interp.get_local(phi_local(12))).to_equal(41)
```

</details>

#### skips predecessor metadata when encoded for native lowering

1. var interp = MirInterpreter create
2. interp set local
3. interp set local
4. Some
5. [mir operand const int
   - Expected: err.? is false
   - Expected: interp.get_local(phi_local(12)) equals `41`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var interp = MirInterpreter.create()
interp.set_local(phi_local(10), 41)
interp.set_local(phi_local(11), 99)
val inst = MirInst(
    kind: MirInstKind.Intrinsic(
        Some(phi_local(12)),
        "__simple_ssa_phi",
        [mir_operand_const_int(1), phi_copy(10), mir_operand_const_int(2), phi_copy(11)]
    ),
    span: nil
)
val err = interp.execute_instruction(inst)
expect(err.?).to_equal(false)
expect(interp.get_local(phi_local(12))).to_equal(41)
```

</details>

#### selects the incoming value for the recorded predecessor block

1. var interp = MirInterpreter create
2. interp set local
3. interp set local
4. interp set previous block for phi
5. Some
6. [mir operand const int
   - Expected: err.? is false
   - Expected: interp.get_local(phi_local(12)) equals `99`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var interp = MirInterpreter.create()
interp.set_local(phi_local(10), 41)
interp.set_local(phi_local(11), 99)
interp.set_previous_block_for_phi(2)
val inst = MirInst(
    kind: MirInstKind.Intrinsic(
        Some(phi_local(12)),
        "__simple_ssa_phi",
        [mir_operand_const_int(1), phi_copy(10), mir_operand_const_int(2), phi_copy(11)]
    ),
    span: nil
)
val err = interp.execute_instruction(inst)
expect(err.?).to_equal(false)
expect(interp.get_local(phi_local(12))).to_equal(99)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/interpreter/mir_ssa_phi_intrinsic_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- MIR interpreter pseudo SSA phi intrinsic

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

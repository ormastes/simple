# Mir Ssa Phi Intrinsic Specification

> <details>

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
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Mir Ssa Phi Intrinsic Specification

## Scenarios

### MIR interpreter pseudo SSA phi intrinsic

#### uses the first incoming value as linear fallback

- var interp = MirInterpreter create
- interp set local
- interp set local
- Some
- [phi copy
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
expect(err).to_be_nil()
expect(interp.get_local(phi_local(12))).to_equal(41)
```

</details>

#### skips predecessor metadata when encoded for native lowering

- var interp = MirInterpreter create
- interp set local
- interp set local
- Some
- [mir operand const int
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
expect(err).to_be_nil()
expect(interp.get_local(phi_local(12))).to_equal(41)
```

</details>

#### selects the incoming value for the recorded predecessor block

- var interp = MirInterpreter create
- interp set local
- interp set local
- interp set previous block for phi
- Some
- [mir operand const int
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
expect(err).to_be_nil()
expect(interp.get_local(phi_local(12))).to_equal(99)
```

</details>

#### returns the fail-closed sentinel for a never-written local

- var interp = MirInterpreter create
   - Expected: interp.get_local(phi_local(99)) equals `-1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var interp = MirInterpreter.create()
expect(interp.get_local(phi_local(99))).to_equal(-1)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/interpreter/mir_ssa_phi_intrinsic_spec.spl` |
| Updated | 2026-07-06 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- MIR interpreter pseudo SSA phi intrinsic

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

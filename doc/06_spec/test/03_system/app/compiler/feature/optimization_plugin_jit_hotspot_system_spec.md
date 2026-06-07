# Optimization Plugin Jit Hotspot System Specification

> <details>

<!-- sdn-diagram:id=optimization_plugin_jit_hotspot_system_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=optimization_plugin_jit_hotspot_system_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

optimization_plugin_jit_hotspot_system_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=optimization_plugin_jit_hotspot_system_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Optimization Plugin Jit Hotspot System Specification

## Scenarios

### Optimization Plugin JIT Hotspot System

### REQ-OPJH-001 REQ-OPJH-002 REQ-OPJH-003 REQ-OPJH-005 REQ-OPJH-006 REQ-OPJH-008

#### should expose JIT hotspot as a first-class built-in provider

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val provider = optimization_rule_provider_builtin_jit_hotspot(
    "simple.opt.jit.hotspot.system",
    ["profile.hot_count", "typed_mir", "safe_deopt"],
    ["jit.hotspot_plan"],
    "runtime-guarded"
)
expect(provider.kind).to_equal(OptimizerProviderKind.JitHotspot)
expect(provider.hot_path).to_equal(true)
expect(optimization_rule_provider_is_runtime_hotspot(provider)).to_equal(true)
```

</details>

### REQ-OPJH-004 REQ-OPJH-007 REQ-OPJH-011

#### should apply the provider only after runtime hotspot facts are available

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val provider = optimization_rule_provider_builtin_jit_hotspot(
    "simple.opt.jit.hotspot.system",
    ["profile.hot_count", "typed_mir", "safe_deopt"],
    ["jit.hotspot_plan"],
    "runtime-guarded"
)
val profile = system_hotspot_profile(8)
val plan = jit_hotspot_plan_from_profile(profile, system_hotspot_config(), true, true)
expect(optimization_rule_provider_can_run(provider, plan.facts)).to_equal(true)
expect(plan.eligible).to_equal(true)
expect(plan.facts).to_contain("profile.hot_count")
```

</details>

### REQ-OPJH-009 REQ-OPJH-012 NFR-OPJH-008

#### should replace compile source only when semantic proof exists

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val profile = system_hotspot_profile(64)
val plan = jit_hotspot_plan_from_profile(profile, system_hotspot_config(), true, true)
val provider = jit_hotspot_specialization_provider(
    "simple.opt.jit.hotspot.system.specialized",
    profile.hotspot_specialized_source,
    profile.hotspot_semantic_proof
)
val decision = jit_hotspot_consume_plan_with_provider(plan, profile.source, provider)
expect(decision.provider_used).to_equal(true)
expect(decision.compile_source).to_equal(profile.hotspot_specialized_source)
expect(decision.reason).to_equal("jit.hotspot_specialized_source accepted")
```

</details>

#### should preserve original source when semantic proof is missing

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val profile = system_hotspot_profile(64)
val plan = jit_hotspot_plan_from_profile(profile, system_hotspot_config(), true, true)
val provider = jit_hotspot_specialization_provider(
    "simple.opt.jit.hotspot.system.specialized",
    profile.hotspot_specialized_source,
    false
)
val decision = jit_hotspot_consume_plan_with_provider(plan, profile.source, provider)
expect(decision.provider_used).to_equal(false)
expect(decision.compile_source).to_equal(profile.source)
expect(decision.reason).to_equal("missing semantic proof")
```

</details>

### REQ-OPJH-013 REQ-OPJH-015

#### should derive JIT var safety facts from MIR reassignment analysis

1. system inst
2. system inst
3. MirTerminator Return
   - Expected: analysis.has_var_reassignment is true
   - Expected: analysis.ssa_transform_safe is true
   - Expected: plan.eligible is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val blocks = system_one_block(
    [
        system_inst(MirInstKind.Const(system_local(0), MirConstValue.Int(1), MirType.i64())),
        system_inst(MirInstKind.Const(system_local(0), MirConstValue.Int(2), MirType.i64()))
    ],
    MirTerminator.Return(Some(system_copy(1)))
)
val analysis = analyze_var_reassign_blocks(blocks)
val facts = var_reassign_analysis_to_jit_facts(analysis)
val plan = jit_hotspot_plan_with_var_facts(system_hotspot_profile(64), system_hotspot_config(), true, true, facts)
expect(analysis.has_var_reassignment).to_equal(true)
expect(analysis.ssa_transform_safe).to_equal(true)
expect(plan.eligible).to_equal(true)
expect(plan.facts).to_contain("ssa.var_transform")
expect(plan.facts).to_contain("borrow.reassign_safe")
```

</details>

#### should create a MIR analysis-backed specialization provider with proof facts

1. system inst
2. system inst
3. system inst
4. MirTerminator Return
5. "fn system hot loop
   - Expected: provider.semantic_proof is true
   - Expected: decision.provider_used is true
   - Expected: decision.compile_source equals `fn system_hot_loop(x: i64) -> i64: x + 2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val blocks = system_one_block(
    [
        system_inst(MirInstKind.Const(system_local(0), MirConstValue.Int(1), MirType.i64())),
        system_inst(MirInstKind.Const(system_local(0), MirConstValue.Int(2), MirType.i64())),
        system_inst(MirInstKind.BinOp(system_local(1), MirBinOp.Add, system_copy(0), system_int(1)))
    ],
    MirTerminator.Return(Some(system_copy(1)))
)
val provider = jit_hotspot_specialization_provider_from_var_reassign_analysis(
    "system.mir.var.hotspot",
    "fn system_hot_loop(x: i64) -> i64: x + 2",
    blocks,
    ["typed_mir", "safe_deopt"]
)
val plan = jit_hotspot_plan_from_profile(system_hotspot_profile(64), system_hotspot_config(), true, true)
val decision = jit_hotspot_consume_plan_with_provider(plan, system_hotspot_profile(64).source, provider)
expect(provider.semantic_proof).to_equal(true)
expect(decision.provider_used).to_equal(true)
expect(decision.compile_source).to_equal("fn system_hot_loop(x: i64) -> i64: x + 2")
```

</details>

### REQ-OPJH-014

#### should select Cranelift within medium budget and LLVM only for tier2 high budget

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val medium = jit_hotspot_rebuild_choice(system_hotspot_profile(256), system_hotspot_config(), true, true, "medium")
expect(medium.eligible).to_equal(true)
expect(medium.selected_backend).to_equal("cranelift")
val high = jit_hotspot_rebuild_choice(system_hotspot_profile(256), system_hotspot_config(), true, true, "high")
expect(high.eligible).to_equal(true)
expect(high.selected_backend).to_equal("llvm")
```

</details>

### REQ-OPJH-016 REQ-OPJH-017 REQ-OPJH-018 REQ-OPJH-019

#### should report, plan, and materialize phi nodes for branch reassignment

<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val entry = MirBlock(id: BlockId.new(0), label: "entry", instructions: [], terminator: MirTerminator.If(system_copy(9), BlockId.new(1), BlockId.new(2)))
val then_block = MirBlock(id: BlockId.new(1), label: "then", instructions: [system_inst(MirInstKind.Const(system_local(0), MirConstValue.Int(1), MirType.i64()))], terminator: MirTerminator.Goto(BlockId.new(3)))
val else_block = MirBlock(id: BlockId.new(2), label: "else", instructions: [system_inst(MirInstKind.Const(system_local(0), MirConstValue.Int(2), MirType.i64()))], terminator: MirTerminator.Goto(BlockId.new(3)))
val join = MirBlock(id: BlockId.new(3), label: "join", instructions: [system_inst(MirInstKind.BinOp(system_local(1), MirBinOp.Add, system_copy(0), system_int(1)))], terminator: MirTerminator.Return(Some(system_copy(1))))
val blocks = [entry, then_block, else_block, join]
val transform = ssa_var_transform_blocks(blocks)
expect(transform.applied).to_equal(true)
expect(transform.reason).to_equal("ready")
val plans = ssa_phi_plans_for_blocks(blocks)
expect(plans.len()).to_equal(1)
expect(plans[0].original_local_id).to_equal(0)
expect(plans[0].join_block_id).to_equal(3)
val materialized = ssa_materialize_phi_plans_for_blocks(blocks)
expect(materialized.applied).to_equal(true)
expect(materialized.phi_count).to_equal(1)
```

</details>

### REQ-OPJH-020

#### should interpret pseudo phi by predecessor block

1. var interp = MirInterpreter create
2. interp set local
3. interp set local
4. interp set previous block for phi
5. Some
6. [mir operand const int
   - Expected: err.? is false
   - Expected: interp.get_local(system_local(12)) equals `99`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var interp = MirInterpreter.create()
interp.set_local(system_local(10), 41)
interp.set_local(system_local(11), 99)
interp.set_previous_block_for_phi(2)
val inst = MirInst(
    kind: MirInstKind.Intrinsic(
        Some(system_local(12)),
        "__simple_ssa_phi",
        [mir_operand_const_int(1), system_copy(10), mir_operand_const_int(2), system_copy(11)]
    ),
    span: nil
)
val err = interp.execute_instruction(inst)
expect(err.?).to_equal(false)
expect(interp.get_local(system_local(12))).to_equal(99)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/app/compiler/feature/optimization_plugin_jit_hotspot_system_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Optimization Plugin JIT Hotspot System
- REQ-OPJH-001 REQ-OPJH-002 REQ-OPJH-003 REQ-OPJH-005 REQ-OPJH-006 REQ-OPJH-008
- REQ-OPJH-004 REQ-OPJH-007 REQ-OPJH-011
- REQ-OPJH-009 REQ-OPJH-012 NFR-OPJH-008
- REQ-OPJH-013 REQ-OPJH-015
- REQ-OPJH-014
- REQ-OPJH-016 REQ-OPJH-017 REQ-OPJH-018 REQ-OPJH-019
- REQ-OPJH-020

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

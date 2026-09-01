# Optimization Plugin Jit Hotspot System Specification

> Tests covering Optimization Plugin JIT Hotspot System, REQ-OPJH-001 REQ-OPJH-002 REQ-OPJH-003 REQ-OPJH-005 REQ-OPJH-006 REQ-OPJH-008, REQ-OPJH-004 REQ-OPJH-007 REQ-OPJH-011, REQ-OPJH-009 REQ-OPJH-012 NFR-OPJH-008, REQ-OPJH-013 REQ-OPJH-015, REQ-OPJH-014, REQ-OPJH-016 REQ-OPJH-017 REQ-OPJH-018 REQ-OPJH-019, REQ-OPJH-020.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Optimization Plugin Jit Hotspot System Specification

## Scenarios

### Optimization Plugin JIT Hotspot System

### REQ-OPJH-001 REQ-OPJH-002 REQ-OPJH-003 REQ-OPJH-005 REQ-OPJH-006 REQ-OPJH-008

#### expose JIT hotspot as a first-class built-in provider

- expose JIT hotspot as a first-class built-in provider
   - Expected: provider.kind equals `OptimizerProviderKind.JitHotspot`
   - Expected: provider.hot_path is true
   - Expected: optimization_rule_provider_is_runtime_hotspot(provider) is true


- Verify: should expose JIT hotspot as a first-class built-in provider
   - Expected: provider.kind equals `OptimizerProviderKind.JitHotspot`
   - Expected: provider.hot_path is true
   - Expected: optimization_rule_provider_is_runtime_hotspot(provider) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 31 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-OPJH-001
# @req REQ-OPJH-002
# @req REQ-OPJH-003
# @req REQ-OPJH-005
# @req REQ-OPJH-006
# @req REQ-OPJH-008
# @req REQ-OPJH-004
# @req REQ-OPJH-007
# @req REQ-OPJH-011
# @req REQ-OPJH-009
# @req REQ-OPJH-012
# @req REQ-OPJH-013
# @req REQ-OPJH-015
# @req REQ-OPJH-014
# @req REQ-OPJH-016
# @req REQ-OPJH-017
# @req REQ-OPJH-018
# @req REQ-OPJH-019
# @req REQ-OPJH-020
# @req REQ-SSPEC-SYSTEM
step("expose JIT hotspot as a first-class built-in provider")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
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

#### apply the provider only after runtime hotspot facts are available

- apply the provider only after runtime hotspot facts are available
   - Expected: optimization_rule_provider_can_run(provider, plan.facts) is true
   - Expected: plan.eligible is true


- Verify: should apply the provider only after runtime hotspot facts are available
   - Expected: optimization_rule_provider_can_run(provider, plan.facts) is true
   - Expected: plan.eligible is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("apply the provider only after runtime hotspot facts are available")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
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

#### replace compile source only when semantic proof exists

- replace compile source only when semantic proof exists
   - Expected: decision.provider_used is true
   - Expected: decision.compile_source equals `profile.hotspot_specialized_source`
   - Expected: decision.reason equals `jit.hotspot_specialized_source accepted`


- Verify: should replace compile source only when semantic proof exists
   - Expected: decision.provider_used is true
   - Expected: decision.compile_source equals `profile.hotspot_specialized_source`
   - Expected: decision.reason equals `jit.hotspot_specialized_source accepted`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("replace compile source only when semantic proof exists")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
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

#### preserve original source when semantic proof is missing

- preserve original source when semantic proof is missing
   - Expected: decision.provider_used is false
   - Expected: decision.compile_source equals `profile.source`
   - Expected: decision.reason equals `missing semantic proof`


- Verify: should preserve original source when semantic proof is missing
   - Expected: decision.provider_used is false
   - Expected: decision.compile_source equals `profile.source`
   - Expected: decision.reason equals `missing semantic proof`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("preserve original source when semantic proof is missing")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
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

- derive JIT var safety facts from MIR reassignment analysis
   - Expected: analysis.has_var_reassignment is true
   - Expected: analysis.ssa_transform_safe is true
   - Expected: plan.eligible is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("derive JIT var safety facts from MIR reassignment analysis")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
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

- create a MIR analysis-backed specialization provider with proof facts
   - Expected: provider.semantic_proof is true
   - Expected: decision.provider_used is true
   - Expected: decision.compile_source equals `fn system_hot_loop(x: i64) -> i64: x + 2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("create a MIR analysis-backed specialization provider with proof facts")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
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

#### select Cranelift within medium budget and LLVM only for tier2 high budget

- select Cranelift within medium budget and LLVM only for tier2 high budget
   - Expected: medium.eligible is true
   - Expected: medium.selected_backend equals `cranelift`
   - Expected: high.eligible is true
   - Expected: high.selected_backend equals `llvm`


- Verify: should select Cranelift within medium budget and LLVM only for tier2 high budget
   - Expected: medium.eligible is true
   - Expected: medium.selected_backend equals `cranelift`
   - Expected: high.eligible is true
   - Expected: high.selected_backend equals `llvm`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("select Cranelift within medium budget and LLVM only for tier2 high budget")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
val medium = jit_hotspot_rebuild_choice(system_hotspot_profile(256), system_hotspot_config(), true, true, "medium")
expect(medium.eligible).to_equal(true)
expect(medium.selected_backend).to_equal("cranelift")
val high = jit_hotspot_rebuild_choice(system_hotspot_profile(256), system_hotspot_config(), true, true, "high")
expect(high.eligible).to_equal(true)
expect(high.selected_backend).to_equal("llvm")
```

</details>

### REQ-OPJH-016 REQ-OPJH-017 REQ-OPJH-018 REQ-OPJH-019

#### report, plan, and materialize phi nodes for branch reassignment

- report, plan, and materialize phi nodes for branch reassignment
   - Expected: transform.applied is true
   - Expected: transform.reason equals `ready`
   - Expected: plans.len() equals `1`
   - Expected: plans[0].original_local_id equals `0`
   - Expected: plans[0].join_block_id equals `3`
   - Expected: materialized.applied is true
   - Expected: materialized.phi_count equals `1`


- Verify: should report, plan, and materialize phi nodes for branch reassignment
   - Expected: transform.applied is true
   - Expected: transform.reason equals `ready`
   - Expected: plans.len() equals `1)  # oracle: pinned constant asserted by this scenario`
   - Expected: plans[0].original_local_id equals `0)  # oracle: pinned constant asserted by this scenario`
   - Expected: plans[0].join_block_id equals `3)  # oracle: pinned constant asserted by this scenario`
   - Expected: materialized.applied is true
   - Expected: materialized.phi_count equals `1)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("report, plan, and materialize phi nodes for branch reassignment")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
val entry = MirBlock(id: BlockId.new(0), label: "entry", instructions: [], terminator: MirTerminator.If(system_copy(9), BlockId.new(1), BlockId.new(2)))
val then_block = MirBlock(id: BlockId.new(1), label: "then", instructions: [system_inst(MirInstKind.Const(system_local(0), MirConstValue.Int(1), MirType.i64()))], terminator: MirTerminator.Goto(BlockId.new(3)))
val else_block = MirBlock(id: BlockId.new(2), label: "else", instructions: [system_inst(MirInstKind.Const(system_local(0), MirConstValue.Int(2), MirType.i64()))], terminator: MirTerminator.Goto(BlockId.new(3)))
val join = MirBlock(id: BlockId.new(3), label: "join", instructions: [system_inst(MirInstKind.BinOp(system_local(1), MirBinOp.Add, system_copy(0), system_int(1)))], terminator: MirTerminator.Return(Some(system_copy(1))))
val blocks = [entry, then_block, else_block, join]
val transform = ssa_var_transform_blocks(blocks)
expect(transform.applied).to_equal(true)
expect(transform.reason).to_equal("ready")
val plans = ssa_phi_plans_for_blocks(blocks)
expect(plans.len()).to_equal(1)  # oracle: plans.len() must equal 1 — authoritative contract constant
expect(plans[0].original_local_id).to_equal(0)  # oracle: plans[0].original_local_id must equal 0 — authoritative contract constant
expect(plans[0].join_block_id).to_equal(3)  # oracle: plans[0].join_block_id must equal 3 — authoritative contract constant
val materialized = ssa_materialize_phi_plans_for_blocks(blocks)
expect(materialized.applied).to_equal(true)
expect(materialized.phi_count).to_equal(1)  # oracle: materialized.phi_count must equal 1 — authoritative contract constant
```

</details>

### REQ-OPJH-020

#### should interpret pseudo phi by predecessor block

- interpret pseudo phi by predecessor block
   - Expected: err == nil is true
   - Expected: interp.get_local(system_local(12)) equals `99`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("interpret pseudo phi by predecessor block")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
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
expect(err == nil).to_equal(true)
expect(interp.get_local(system_local(12))).to_equal(99)  # oracle: interp.get_local(system_local(12)) must equal 99 — authoritative contract constant
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/app/compiler/feature/optimization_plugin_jit_hotspot_system_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Optimization Plugin JIT Hotspot System, REQ-OPJH-001 REQ-OPJH-002 REQ-OPJH-003 REQ-OPJH-005 REQ-OPJH-006 REQ-OPJH-008, REQ-OPJH-004 REQ-OPJH-007 REQ-OPJH-011, REQ-OPJH-009 REQ-OPJH-012 NFR-OPJH-008, REQ-OPJH-013 REQ-OPJH-015, REQ-OPJH-014, REQ-OPJH-016 REQ-OPJH-017 REQ-OPJH-018 REQ-OPJH-019, REQ-OPJH-020.
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
- `REQ-OPJH-002`
- `REQ-OPJH-003`
- `REQ-OPJH-005`
- `REQ-OPJH-006`
- `REQ-OPJH-008":`
- `REQ-OPJH-001`
- `REQ-OPJH-008`
- `REQ-OPJH-004`
- `REQ-OPJH-007`
- `REQ-OPJH-011`
- `REQ-OPJH-009`
- `REQ-OPJH-012`
- `REQ-OPJH-013`
- `REQ-OPJH-015`
- `REQ-OPJH-014`
- `REQ-OPJH-016`
- `REQ-OPJH-017`
- `REQ-OPJH-018`
- `REQ-OPJH-019`
- `REQ-OPJH-020`
- `REQ-OPJH-011":`
- `REQ-OPJH-015":`
- `REQ-OPJH-019":`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `b56baf875f1fad4abb7f096db4485ea2fecdbd55a97fe7a7544298e1869e7383`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `b56baf875f1fad4abb7f096db4485ea2fecdbd55a97fe7a7544298e1869e7383`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `b56baf875f1fad4abb7f096db4485ea2fecdbd55a97fe7a7544298e1869e7383`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **97/100**; effective score: **97/100**; blockers: **0**.

SSpec documentization score: 97/100
source: test/03_system/app/compiler/feature/optimization_plugin_jit_hotspot_system_spec.spl
mirror: doc/06_spec/03_system/app/compiler/feature/optimization_plugin_jit_hotspot_system_spec.md (current)
findings: 2 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=100 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/app/compiler/feature/optimization_plugin_jit_hotspot_system_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/app/compiler/feature/optimization_plugin_jit_hotspot_system_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
<!-- sspec-maintain:scorecard:end -->

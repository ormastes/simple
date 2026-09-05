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

#### should expose JIT hotspot as a first-class built-in provider

<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
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
```

</details>

### REQ-OPJH-004 REQ-OPJH-007 REQ-OPJH-011

#### should apply the provider only after runtime hotspot facts are available

- should apply the provider only after runtime hotspot facts are available


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should apply the provider only after runtime hotspot facts are available")
val provider = optimization_rule_provider_builtin_jit_hotspot(
    "simple.opt.jit.hotspot.system",
    ["profile.hot_count", "typed_mir", "safe_deopt"],
    ["jit.hotspot_plan"],
    "runtime-guarded"
)
val profile = system_hotspot_profile(8)
val plan = jit_hotspot_plan_from_profile(profile, system_hotspot_config(), true, true)
assert_equal(optimization_rule_provider_can_run(provider, plan.facts), true)
assert_equal(plan.eligible, true)
assert_contains(plan.facts, "profile.hot_count")
```

</details>

### REQ-OPJH-009 REQ-OPJH-012 NFR-OPJH-008

#### should replace compile source only when semantic proof exists

- should replace compile source only when semantic proof exists


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should replace compile source only when semantic proof exists")
val profile = system_hotspot_profile(64)
val plan = jit_hotspot_plan_from_profile(profile, system_hotspot_config(), true, true)
val provider = jit_hotspot_specialization_provider(
    "simple.opt.jit.hotspot.system.specialized",
    profile.hotspot_specialized_source,
    profile.hotspot_semantic_proof
)
val decision = jit_hotspot_consume_plan_with_provider(plan, profile.source, provider)
assert_equal(decision.provider_used, true)
assert_equal(decision.compile_source, profile.hotspot_specialized_source)
assert_equal(decision.reason, "jit.hotspot_specialized_source accepted")
```

</details>

#### should preserve original source when semantic proof is missing

- should preserve original source when semantic proof is missing


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should preserve original source when semantic proof is missing")
val profile = system_hotspot_profile(64)
val plan = jit_hotspot_plan_from_profile(profile, system_hotspot_config(), true, true)
val provider = jit_hotspot_specialization_provider(
    "simple.opt.jit.hotspot.system.specialized",
    profile.hotspot_specialized_source,
    false
)
val decision = jit_hotspot_consume_plan_with_provider(plan, profile.source, provider)
assert_equal(decision.provider_used, false)
assert_equal(decision.compile_source, profile.source)
assert_equal(decision.reason, "missing semantic proof")
```

</details>

### REQ-OPJH-013 REQ-OPJH-015

#### should derive JIT var safety facts from MIR reassignment analysis

- should derive JIT var safety facts from MIR reassignment analysis


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should derive JIT var safety facts from MIR reassignment analysis")
val blocks = system_one_block(
    [
        system_inst(MirInstKind.Const(system_local(0), MirConstValue.Int(1), MirType.i64())),
        system_inst(MirInstKind.Const(system_local(0), MirConstValue.Int(2), MirType.i64()))
    ],
    MirTerminator.Ret(Some(system_copy(1)))
)
val analysis = analyze_var_reassign_blocks(blocks)
val facts = var_reassign_analysis_to_jit_facts(analysis)
val plan = jit_hotspot_plan_with_var_facts(system_hotspot_profile(64), system_hotspot_config(), true, true, facts)
assert_equal(analysis.has_var_reassignment, true)
assert_equal(analysis.ssa_transform_safe, true)
assert_equal(plan.eligible, true)
assert_contains(plan.facts, "ssa.var_transform")
assert_contains(plan.facts, "borrow.reassign_safe")
```

</details>

#### should create a MIR analysis-backed specialization provider with proof facts

- should create a MIR analysis-backed specialization provider with proof facts


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should create a MIR analysis-backed specialization provider with proof facts")
val blocks = system_one_block(
    [
        system_inst(MirInstKind.Const(system_local(0), MirConstValue.Int(1), MirType.i64())),
        system_inst(MirInstKind.Const(system_local(0), MirConstValue.Int(2), MirType.i64())),
        system_inst(MirInstKind.BinOp(system_local(1), MirBinOp.Add, system_copy(0), system_int(1)))
    ],
    MirTerminator.Ret(Some(system_copy(1)))
)
val provider = jit_hotspot_specialization_provider_from_var_reassign_analysis(
    "system.mir.var.hotspot",
    "fn system_hot_loop(x: i64) -> i64: x + 2",
    blocks,
    ["typed_mir", "safe_deopt"]
)
val plan = jit_hotspot_plan_from_profile(system_hotspot_profile(64), system_hotspot_config(), true, true)
val decision = jit_hotspot_consume_plan_with_provider(plan, system_hotspot_profile(64).source, provider)
assert_equal(provider.semantic_proof, true)
assert_equal(decision.provider_used, true)
assert_equal(decision.compile_source, "fn system_hot_loop(x: i64) -> i64: x + 2")
```

</details>

### REQ-OPJH-014

#### should select Cranelift within medium budget and LLVM only for tier2 high budget

- should select Cranelift within medium budget and LLVM only for tier2 high budget


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should select Cranelift within medium budget and LLVM only for tier2 high budget")
val medium = jit_hotspot_rebuild_choice(system_hotspot_profile(256), system_hotspot_config(), true, true, "medium")
assert_equal(medium.eligible, true)
assert_equal(medium.selected_backend, "cranelift")
val high = jit_hotspot_rebuild_choice(system_hotspot_profile(256), system_hotspot_config(), true, true, "high")
assert_equal(high.eligible, true)
assert_equal(high.selected_backend, "llvm")
```

</details>

### REQ-OPJH-016 REQ-OPJH-017 REQ-OPJH-018 REQ-OPJH-019

#### should report, plan, and materialize phi nodes for branch reassignment

- should report, plan, and materialize phi nodes for branch reassignment


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should report, plan, and materialize phi nodes for branch reassignment")
val entry = MirBlock(id: BlockId.new(0), label: "entry", instructions: [], terminator: MirTerminator.If(system_copy(9), BlockId.new(1), BlockId.new(2)))
val then_block = MirBlock(id: BlockId.new(1), label: "then", instructions: [system_inst(MirInstKind.Const(system_local(0), MirConstValue.Int(1), MirType.i64()))], terminator: MirTerminator.Goto(BlockId.new(3)))
val else_block = MirBlock(id: BlockId.new(2), label: "else", instructions: [system_inst(MirInstKind.Const(system_local(0), MirConstValue.Int(2), MirType.i64()))], terminator: MirTerminator.Goto(BlockId.new(3)))
val join = MirBlock(id: BlockId.new(3), label: "join", instructions: [system_inst(MirInstKind.BinOp(system_local(1), MirBinOp.Add, system_copy(0), system_int(1)))], terminator: MirTerminator.Ret(Some(system_copy(1))))
val blocks = [entry, then_block, else_block, join]
val transform = ssa_var_transform_blocks(blocks)
assert_equal(transform.applied, true)
assert_equal(transform.reason, "ready")
val plans = ssa_phi_plans_for_blocks(blocks)
assert_equal(plans.len(), 1)
assert_equal(plans[0].original_local_id, 0)
assert_equal(plans[0].join_block_id, 3)
val materialized = ssa_materialize_phi_plans_for_blocks(blocks)
assert_equal(materialized.applied, true)
assert_equal(materialized.phi_count, 1)
```

</details>

### REQ-OPJH-020

#### should interpret pseudo phi by predecessor block

- should interpret pseudo phi by predecessor block


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should interpret pseudo phi by predecessor block")
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
assert_equal(err == nil, true)
assert_equal(interp.get_local(system_local(12)), 99)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/system/app/compiler/feature/optimization_plugin_jit_hotspot_system_spec.spl` |
| Updated | 2026-08-27 |
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

- Canonical SPipe generation for source `0823c9546d463f70776fc6490caab2ea85784a3598069ffe482e5811e7673379`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `0823c9546d463f70776fc6490caab2ea85784a3598069ffe482e5811e7673379`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `0823c9546d463f70776fc6490caab2ea85784a3598069ffe482e5811e7673379`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **83/100**; effective score: **83/100**; blockers: **0**.

SSpec documentization score: 83/100
source: test/system/app/compiler/feature/optimization_plugin_jit_hotspot_system_spec.spl
mirror: doc/06_spec/system/app/compiler/feature/optimization_plugin_jit_hotspot_system_spec.md (current)
findings: 13 blockers: 0
  narrative=80 structure=60 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/system/app/compiler/feature/optimization_plugin_jit_hotspot_system_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/system/app/compiler/feature/optimization_plugin_jit_hotspot_system_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/system/app/compiler/feature/optimization_plugin_jit_hotspot_system_spec.spl:1:1: warning SSDOC-NAR-001 [narrative] (-20): missing authored purpose and audience
  why: Readers need scope, audience, and intent before executable detail.
  improve: Add authored purpose, scope, and audience facts.
test/system/app/compiler/feature/optimization_plugin_jit_hotspot_system_spec.spl:84:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'should expose JIT hotspot as a first-class built-in provider' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/system/app/compiler/feature/optimization_plugin_jit_hotspot_system_spec.spl:84:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should expose JIT hotspot as a first-class built-in provider' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/system/app/compiler/feature/optimization_plugin_jit_hotspot_system_spec.spl:123:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should apply the provider only after runtime hotspot facts are available' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/system/app/compiler/feature/optimization_plugin_jit_hotspot_system_spec.spl:123:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should apply the provider only after runtime hotspot facts are available' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/system/app/compiler/feature/optimization_plugin_jit_hotspot_system_spec.spl:139:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should replace compile source only when semantic proof exists' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/system/app/compiler/feature/optimization_plugin_jit_hotspot_system_spec.spl:139:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should replace compile source only when semantic proof exists' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/system/app/compiler/feature/optimization_plugin_jit_hotspot_system_spec.spl:154:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should preserve original source when semantic proof is missing' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/system/app/compiler/feature/optimization_plugin_jit_hotspot_system_spec.spl:154:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should preserve original source when semantic proof is missing' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/system/app/compiler/feature/optimization_plugin_jit_hotspot_system_spec.spl:170:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should derive JIT var safety facts from MIR reassignment analysis' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/system/app/compiler/feature/optimization_plugin_jit_hotspot_system_spec.spl:189:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should create a MIR analysis-backed specialization provider with proof facts' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->

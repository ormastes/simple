# Hwir Opt Specification

> <details>

<!-- sdn-diagram:id=hwir_opt_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=hwir_opt_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

hwir_opt_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=hwir_opt_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Hwir Opt Specification

## Scenarios

### HWIR optimizer pass config

#### allows all passes to be independently enabled

- check
- check
- check
- check
- check
- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = HwirOptPassConfig.all_enabled("speed")
check(config.width_narrowing)
check(config.structural_simplify)
check(config.resource_binding)
check(config.fsm_opt)
check(config.memory_inference)
check(config.dsp_inference)
expect config.profile == "speed"
```

</details>

#### allows all passes to be independently disabled

- check
- check
- check
- check
- check
- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = HwirOptPassConfig.none("area")
check(not config.width_narrowing)
check(not config.structural_simplify)
check(not config.resource_binding)
check(not config.fsm_opt)
check(not config.memory_inference)
check(not config.dsp_inference)
expect config.profile == "area"
```

</details>

### HWIR width narrowing

#### reports narrowed bits from static ranges

- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val range = HwirWidthRange(node_id: "n0", min_value: 0, max_value: 7, original_width: 8, signed_value: false)
val result = hwir_width_narrowing_pass(test_module(), [range])
check(result.changed)
expect result.narrowed_bits == 4
```

</details>

### HWIR structural simplification

#### counts folded and removed nodes

- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val stats = HwirStructuralStats(constant_folds: 2, dead_signals: 3, dead_registers: 1, redundant_muxes: 1, cse_hits: 2)
val result = hwir_structural_simplify_pass(test_module(), stats)
check(result.changed)
expect result.removed_nodes == 7
```

</details>

### HWIR resource binding

#### shares resources for area profile

- check
- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val plan = HwirResourceBindingPlan(profile: "area", multiplier_count: 4, shared_multiplier_count: 2, divider_count: 1, pipeline_stage_count: 0)
val binding = hwir_binding_for_profile("mul0", "multiplier", "area")
val result = hwir_resource_binding_pass(test_module(), plan)
check(binding.is_shared())
check(result.changed)
expect result.shared_resources == 2
```

</details>

### HWIR FSM optimization

#### chooses one hot for speed and removes unreachable states

- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fsm = HwFsm.create("ctrl", "state", 8)
val encoding = hwir_choose_fsm_encoding(8, "speed")
val plan = HwirFsmOptPlan(fsm: fsm, unreachable_states: 3, encoding: encoding)
val result = hwir_fsm_opt_pass(test_module(), plan)
expect encoding == "one_hot"
check(result.changed)
expect result.removed_nodes == 3
```

</details>

### HWIR memory inference

#### recognizes true dual port RAM patterns

- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pattern = HwirMemoryPattern(name: "rf", element_width: 32, depth: 64, read_ports: 2, write_ports: 1, constant_contents: false, fifo_access: false)
val memory = hwir_memory_from_pattern(pattern)
val result = hwir_memory_inference_pass(test_module(), [pattern])
expect memory.template_kind == "true_dual_port_ram"
check(result.changed)
expect result.removed_nodes == 64
```

</details>

### HWIR DSP inference

#### binds wide arithmetic patterns to DSP resources

- check
- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pattern = HwirDspPattern(node_id: "mac0", pattern_kind: "mac", operand_width: 16, term_count: 2, prefer_lut: false)
val result = hwir_dsp_inference_pass(test_module(), [pattern])
check(pattern.uses_dsp())
check(result.changed)
expect result.cost_after.dsp_count == 5
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/60.mir_opt/hwir_opt_spec.spl` |
| Updated | 2026-07-06 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- HWIR optimizer pass config
- HWIR width narrowing
- HWIR structural simplification
- HWIR resource binding
- HWIR FSM optimization
- HWIR memory inference
- HWIR DSP inference

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

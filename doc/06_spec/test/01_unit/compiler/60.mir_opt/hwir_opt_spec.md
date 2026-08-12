# Hwir Opt Specification

> **Requirement:** REQ-G2-001
>
> **Source:** `test/01_unit/compiler/60.mir_opt/hwir_opt_spec.spl`
> **Scope:** Typed HWIR optimizer planning and accounting. This specification
> does not establish generated-VHDL or target-execution evidence.

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

## Operator workflow

Run the focused SSpec with the admitted Simple runtime. Each scenario builds a
small typed HWIR fixture, invokes exactly one optimizer contract, and checks
the returned change and accounting fields with built-in matchers.

## Scenarios

### HWIR optimizer pass config

#### should enable every pass for the speed profile

1. Create an all-enabled speed pass configuration.
2. Confirm that each optimization pass is enabled and the profile is `speed`.

<details>
<summary>Executable SSpec</summary>

```simple
val config = HwirOptPassConfig.all_enabled("speed")
expect(config.width_narrowing).to_be(true)
expect(config.structural_simplify).to_be(true)
expect(config.resource_binding).to_be(true)
expect(config.fsm_opt).to_be(true)
expect(config.memory_inference).to_be(true)
expect(config.dsp_inference).to_be(true)
expect(config.profile).to_equal("speed")
```

</details>

#### should disable every pass for the area profile

1. Create a disabled area pass configuration.
2. Confirm that each optimization pass is disabled and the profile is `area`.

<details>
<summary>Executable SSpec</summary>

```simple
val config = HwirOptPassConfig.none("area")
expect(config.width_narrowing).to_be(false)
expect(config.structural_simplify).to_be(false)
expect(config.resource_binding).to_be(false)
expect(config.fsm_opt).to_be(false)
expect(config.memory_inference).to_be(false)
expect(config.dsp_inference).to_be(false)
expect(config.profile).to_equal("area")
```

</details>

### HWIR width narrowing

#### should report narrowed bits from a static range

1. Narrow an eight-bit unsigned range whose maximum is seven.
2. Confirm that the pass changes the module and removes four bits.

<details>
<summary>Executable SSpec</summary>

```simple
val range = HwirWidthRange(node_id: "n0", min_value: 0, max_value: 7, original_width: 8, signed_value: false)
val result = hwir_width_narrowing_pass(test_module(), [range])
expect(result.changed).to_be(true)
expect(result.narrowed_bits).to_equal(4)
```

</details>

### HWIR structural simplification

#### should count folded and removed nodes

1. Simplify a module with foldable and dead structural nodes.
2. Confirm that the pass changes the module and removes seven nodes.

<details>
<summary>Executable SSpec</summary>

```simple
val stats = HwirStructuralStats(constant_folds: 2, dead_signals: 3, dead_registers: 1, redundant_muxes: 1, cse_hits: 2)
val result = hwir_structural_simplify_pass(test_module(), stats)
expect(result.changed).to_be(true)
expect(result.removed_nodes).to_equal(7)
```

</details>

### HWIR resource binding

#### should share multiplier resources for the area profile

1. Bind an area-profile multiplier plan.
2. Confirm shared binding, estimated latency, and two shared resources.

<details>
<summary>Executable SSpec</summary>

```simple
val plan = HwirResourceBindingPlan(profile: "area", multiplier_count: 4, shared_multiplier_count: 2, divider_count: 1, pipeline_stage_count: 0)
val binding = hwir_binding_for_profile("mul0", "multiplier", "area")
val result = hwir_resource_binding_pass(test_module(), plan)
expect(binding.is_shared()).to_be(true)
expect(binding.latency_contract).to_equal("estimated")
expect(binding.latency_is_committed()).to_equal(false)
expect(result.changed).to_be(true)
expect(result.shared_resources).to_equal(2)
```

</details>

### HWIR FSM optimization

#### should choose one-hot speed encoding and remove unreachable states

1. Optimize an eight-state control FSM for speed.
2. Confirm one-hot encoding and removal of three unreachable states.

<details>
<summary>Executable SSpec</summary>

```simple
val fsm = HwFsm.create("ctrl", "state", 8)
val encoding = hwir_choose_fsm_encoding(8, "speed")
val plan = HwirFsmOptPlan(fsm: fsm, unreachable_states: 3, encoding: encoding)
val result = hwir_fsm_opt_pass(test_module(), plan)
expect(encoding).to_equal("one_hot")
expect(result.changed).to_be(true)
expect(result.removed_nodes).to_equal(3)
```

</details>

### HWIR memory inference

#### should recognize a true dual-port RAM pattern

1. Infer memory from a two-read-port register-file pattern.
2. Confirm the true-dual-port template and changed accounting.

<details>
<summary>Executable SSpec</summary>

```simple
val pattern = HwirMemoryPattern(name: "rf", element_width: 32, depth: 64, read_ports: 2, write_ports: 1, constant_contents: false, fifo_access: false)
val memory = hwir_memory_from_pattern(pattern)
val result = hwir_memory_inference_pass(test_module(), [pattern])
expect(memory.template_kind).to_equal("true_dual_port_ram")
expect(result.changed).to_be(true)
expect(result.removed_nodes).to_equal(64)
```

</details>

### HWIR DSP inference

#### should bind a multiply-accumulate pattern to DSP resources

1. Infer DSP use for a sixteen-bit multiply-accumulate pattern.
2. Confirm DSP eligibility, pass mutation, and post-pass DSP count.

<details>
<summary>Executable SSpec</summary>

```simple
val pattern = HwirDspPattern(node_id: "mac0", pattern_kind: "mac", operand_width: 16, term_count: 2, prefer_lut: false)
val result = hwir_dsp_inference_pass(test_module(), [pattern])
expect(pattern.uses_dsp()).to_be(true)
expect(result.changed).to_be(true)
expect(result.cost_after.dsp_count).to_equal(5)
```

</details>

## Scorecard and limitations

| Field | Value |
|-------|-------|
| Category | Compiler unit specification |
| Status | Active |
| Scenario count | 8 |
| Requirement coverage | REQ-G2-001 typed HWIR optimizer contracts |
| Excluded evidence | VHDL emission, GHDL analysis, synthesis, target execution |
| Updated | 2026-08-12 |

The examples intentionally use a fixed minimal module and deterministic
optimizer inputs. They prove pass-config selection and reported accounting,
not global optimization quality on arbitrary hardware designs.

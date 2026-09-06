# hwir_opt_spec

> HWIR optimizer unit tests.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# hwir_opt_spec

HWIR optimizer unit tests.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/unit/compiler/60.mir_opt/hwir_opt_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

HWIR optimizer unit tests.

Each scenario exercises one optimizer pass contract against the same minimal
typed HWIR module.  The scope is optimizer planning and accounting only; it
does not claim generated VHDL or target execution evidence.

## Scenarios

### HWIR optimizer pass config

#### should enable every pass for the speed profile

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- should enable every pass for the speed profile
- Create an all-enabled speed pass configuration
   - Expected: config.profile equals `speed`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should enable every pass for the speed profile")
step("Create an all-enabled speed pass configuration")
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

- should disable every pass for the area profile
- Create a disabled area pass configuration
   - Expected: config.profile equals `area`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should disable every pass for the area profile")
step("Create a disabled area pass configuration")
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

- should report narrowed bits from a static range
- Narrow an eight-bit unsigned range whose maximum is seven
   - Expected: result.narrowed_bits equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should report narrowed bits from a static range")
step("Narrow an eight-bit unsigned range whose maximum is seven")
val range = HwirWidthRange(node_id: "n0", min_value: 0, max_value: 7, original_width: 8, signed_value: false)
val result = hwir_width_narrowing_pass(test_module(), [range])
expect(result.changed).to_be(true)
expect(result.narrowed_bits).to_equal(4)
```

</details>

### HWIR structural simplification

#### should count folded and removed nodes

- should count folded and removed nodes
- Simplify a module with foldable and dead structural nodes
   - Expected: result.removed_nodes equals `7`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should count folded and removed nodes")
step("Simplify a module with foldable and dead structural nodes")
val stats = HwirStructuralStats(constant_folds: 2, dead_signals: 3, dead_registers: 1, redundant_muxes: 1, cse_hits: 2)
val result = hwir_structural_simplify_pass(test_module(), stats)
expect(result.changed).to_be(true)
expect(result.removed_nodes).to_equal(7)
```

</details>

### HWIR resource binding

#### should share multiplier resources for the area profile

- should share multiplier resources for the area profile
- Bind an area-profile multiplier plan
   - Expected: binding.latency_contract equals `estimated`
   - Expected: binding.latency_is_committed() is false
   - Expected: result.shared_resources equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should share multiplier resources for the area profile")
step("Bind an area-profile multiplier plan")
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

- should choose one-hot speed encoding and remove unreachable states
- Optimize an eight-state control FSM for speed
   - Expected: encoding equals `one_hot`
   - Expected: result.removed_nodes equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should choose one-hot speed encoding and remove unreachable states")
step("Optimize an eight-state control FSM for speed")
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

- should recognize a true dual-port RAM pattern
- Infer memory from a two-read-port register-file pattern
   - Expected: memory.template_kind equals `true_dual_port_ram`
   - Expected: result.removed_nodes equals `64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should recognize a true dual-port RAM pattern")
step("Infer memory from a two-read-port register-file pattern")
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

- should bind a multiply-accumulate pattern to DSP resources
- Infer DSP use for a sixteen-bit multiply-accumulate pattern
   - Expected: result.cost_after.dsp_count equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should bind a multiply-accumulate pattern to DSP resources")
step("Infer DSP use for a sixteen-bit multiply-accumulate pattern")
val pattern = HwirDspPattern(node_id: "mac0", pattern_kind: "mac", operand_width: 16, term_count: 2, prefer_lut: false)
val result = hwir_dsp_inference_pass(test_module(), [pattern])
expect(pattern.uses_dsp()).to_be(true)
expect(result.changed).to_be(true)
expect(result.cost_after.dsp_count).to_equal(5)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
- `REQ-G2-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `ee37376fc81c7712342fcdf22777e37d4611e52bd60187ec150ecd8e172b7890`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `ee37376fc81c7712342fcdf22777e37d4611e52bd60187ec150ecd8e172b7890`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `ee37376fc81c7712342fcdf22777e37d4611e52bd60187ec150ecd8e172b7890`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **76/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/unit/compiler/60.mir_opt/hwir_opt_spec.spl
mirror: doc/06_spec/unit/compiler/60.mir_opt/hwir_opt_spec.md (current)
findings: 13 blockers: 1
  narrative=100 structure=70 oracle=70
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=76; blocker cap makes effective=49
doc/06_spec/unit/compiler/60.mir_opt/hwir_opt_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/compiler/60.mir_opt/hwir_opt_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/compiler/60.mir_opt/hwir_opt_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 6 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/compiler/60.mir_opt/hwir_opt_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 1 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/unit/compiler/60.mir_opt/hwir_opt_spec.spl:47:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should enable every pass for the speed profile' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/unit/compiler/60.mir_opt/hwir_opt_spec.spl:47:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should enable every pass for the speed profile' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/60.mir_opt/hwir_opt_spec.spl:60:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should disable every pass for the area profile' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/unit/compiler/60.mir_opt/hwir_opt_spec.spl:60:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should disable every pass for the area profile' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/60.mir_opt/hwir_opt_spec.spl:74:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should report narrowed bits from a static range' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/unit/compiler/60.mir_opt/hwir_opt_spec.spl:74:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should report narrowed bits from a static range' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/60.mir_opt/hwir_opt_spec.spl:84:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should count folded and removed nodes' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/unit/compiler/60.mir_opt/hwir_opt_spec.spl:94:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should share multiplier resources for the area profile' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/unit/compiler/60.mir_opt/hwir_opt_spec.spl:108:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should choose one-hot speed encoding and remove unreachable states' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->

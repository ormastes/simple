# Hwir Standalone Sequential Specification

> Tests covering standalone typed sequential HWIR.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Hwir Standalone Sequential Specification

## Scenarios

### standalone typed sequential HWIR

#### should admit a register-ready plan without a fabricated child

- should admit a register-ready plan without a fabricated child
- Render a standalone ready-register plan with no child entity or pins
   - Expected: module.diagnostic() equals ``
   - Expected: module.plan.decoder_pins.len() equals `0`
   - Expected: emitted.is_success() is true
   - Expected: emitted.vhdl does not contain `entity work.`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("should admit a register-ready plan without a fabricated child")
step("Render a standalone ready-register plan with no child entity or pins")
val module = standalone_ready_module()
expect(module.diagnostic()).to_equal("")
expect(module.plan.decoder_pins.len()).to_equal(0)
val emitted = render_strict_sequential_hwir(module, "hwir-standalone-sequential-v1")
expect(emitted.is_success()).to_equal(true)
expect(emitted.vhdl).to_contain("entity standalone_ready_register is")
expect(emitted.vhdl).to_contain("in_ready <= '1' when valid_reg='0' else '0';")
expect(emitted.vhdl).to_contain("out_data <= data_reg when valid_reg='1' else (others=>'0');")
expect(emitted.vhdl.contains("entity work.")).to_equal(false)
```

</details>

#### should reject standalone plans that retain child pins

- should reject standalone plans that retain child pins
- Add a child decoder pin to an otherwise standalone sequential plan


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("should reject standalone plans that retain child pins")
step("Add a child decoder pin to an otherwise standalone sequential plan")
val module = standalone_ready_module()
val malformed_plan = HwSequentialPlan(owner_id: module.plan.owner_id,
    registers: module.plan.registers, rules: module.plan.rules,
    outputs: module.plan.outputs, decoder_pins: [
        HwSeqInstancePin(port_name: "data",
            signal_name: "in_data", direction: "in", bit_width: 32)])
val malformed = HwSequentialModuleDef(node_id: module.node_id,
    entity_name: module.entity_name, config: module.config, origins: module.origins,
    ports: module.ports, datapath_signals: [], datapath_constants: [], datapath_bit_vector_constants: [],
    datapath_comb_ops: [], datapath_compare_ops: [], datapath_select_ops: [],
    datapath_bit_extract_ops: [], datapath_fixed_slice_ops: [],
    plan: malformed_plan, child_entity: "",
    child_graph_sha256: "")
expect(malformed.diagnostic()).to_equal(
    "HWIR-E-SEQUENTIAL-MODULE-CHILD: standalone modules cannot retain child identity or pins")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/50.mir/hwir_standalone_sequential_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering standalone typed sequential HWIR.
- standalone typed sequential HWIR

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-COMPILER`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `16c70ea2e9f9c218f0296318cc605227176ded9f2fa01888239f692c4a92576a`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `16c70ea2e9f9c218f0296318cc605227176ded9f2fa01888239f692c4a92576a`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `16c70ea2e9f9c218f0296318cc605227176ded9f2fa01888239f692c4a92576a`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/01_unit/compiler/50.mir/hwir_standalone_sequential_spec.spl
mirror: doc/06_spec/01_unit/compiler/50.mir/hwir_standalone_sequential_spec.md (current)
findings: 7 blockers: 0
  narrative=100 structure=90 oracle=90
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/50.mir/hwir_standalone_sequential_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/50.mir/hwir_standalone_sequential_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/50.mir/hwir_standalone_sequential_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/50.mir/hwir_standalone_sequential_spec.spl:55:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should admit a register-ready plan without a fabricated child' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/compiler/50.mir/hwir_standalone_sequential_spec.spl:55:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should admit a register-ready plan without a fabricated child' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/50.mir/hwir_standalone_sequential_spec.spl:70:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should reject standalone plans that retain child pins' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/compiler/50.mir/hwir_standalone_sequential_spec.spl:70:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should reject standalone plans that retain child pins' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

# Hwir Retirement Composition Specification

> Tests covering strict Gen2 retirement receipt composition.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Hwir Retirement Composition Specification

## Scenarios

### strict Gen2 retirement receipt composition

#### should bind the one-entry frontend and receipt producer to one reset for RV32 and RV64

- should bind the one-entry frontend and receipt producer to one reset for RV32 and RV64
- Construct the closed RV32 and RV64 retirement-receipt contracts
   - Expected: composition32.shape_diagnostic() equals ``
   - Expected: composition64.shape_diagnostic() equals ``
   - Expected: composition32.bindings.len() equals `15`
   - Expected: composition32.bindings[2].source_port equals `rst`
   - Expected: composition32.bindings[2].destination_owner equals `frontend`
   - Expected: composition32.bindings[3].source_port equals `rst`
   - Expected: composition32.bindings[3].destination_owner equals `producer`
   - Expected: composition32.producer.dispatch_lineage.bit_width equals `64`
   - Expected: composition64.producer.dispatch_original_length_bytes.bit_width equals `2`
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("should bind the one-entry frontend and receipt producer to one reset for RV32 and RV64")
step("Construct the closed RV32 and RV64 retirement-receipt contracts")
val rv32 = strict_zca_single_outstanding_retirement_composition(
    "rv32_retirement_composition", CoreConfig.rv32_zca_mission_critical(),
    "riscv_gen2_rv32_architectural_retirement")
val rv64 = strict_zca_single_outstanding_retirement_composition(
    "rv64_retirement_composition", CoreConfig.rv64_zca_mission_critical(),
    "riscv_gen2_rv64_architectural_retirement")
if rv32.is_ok() and rv64.is_ok():
    val composition32 = rv32.ok().unwrap()
    val composition64 = rv64.ok().unwrap()
    expect(composition32.shape_diagnostic()).to_equal("")
    expect(composition64.shape_diagnostic()).to_equal("")
    expect(composition32.bindings.len()).to_equal(15)
    expect(composition32.bindings[2].source_port).to_equal("rst")
    expect(composition32.bindings[2].destination_owner).to_equal("frontend")
    expect(composition32.bindings[3].source_port).to_equal("rst")
    expect(composition32.bindings[3].destination_owner).to_equal("producer")
    expect(composition32.producer.dispatch_lineage.bit_width).to_equal(64)
    expect(composition64.producer.dispatch_original_length_bytes.bit_width).to_equal(2)
else:
    expect(false).to_equal(true)
```

</details>

#### should reject a producer that loses the shared reset or receipt width

- should reject a producer that loses the shared reset or receipt width
- Mutate the typed producer reset and receipt tuple independently
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("should reject a producer that loses the shared reset or receipt width")
step("Mutate the typed producer reset and receipt tuple independently")
val config = CoreConfig.rv32_zca_mission_critical()
val producer = strict_riscv_retire_receipt_producer_interface(config)
if producer.is_ok():
    val bad_reset = producer.ok().unwrap()
    bad_reset.rst = HwPort.input("retire_rst", "Bits", 1)
    expect(bad_reset.shape_diagnostic()).to_equal(
        "HWIR-E-RETIRE-PRODUCER-CLOCK: retirement receipt producer requires shared one-bit clk and synchronous active-high rst inputs")
    val bad_width = strict_riscv_retire_receipt_producer_interface(config).ok().unwrap()
    bad_width.retire_lineage = HwPort.output("retire_lineage", "Bits", 63)
    expect(bad_width.shape_diagnostic()).to_equal(
        "HWIR-E-RETIRE-PRODUCER-RECEIPT-WIDTH: retirement producer must publish the exact receipt identity tuple")
else:
    expect(false).to_equal(true)
```

</details>

#### should reject omitted or rewired receipt bindings before composition

- should reject omitted or rewired receipt bindings before composition
- Rewire one closed receipt binding before the composition boundary
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("should reject omitted or rewired receipt bindings before composition")
step("Rewire one closed receipt binding before the composition boundary")
val built = strict_zca_single_outstanding_retirement_composition(
    "retirement_binding_contract", CoreConfig.rv32_zca_mission_critical(),
    "riscv_gen2_rv32_architectural_retirement")
if built.is_ok():
    val canonical = built.ok().unwrap()
    var rewired = canonical.bindings
    rewired[11] = HwRetireCompositionBinding(kind: "producer_to_frontend", source_owner: "producer",
        source_port: "retire_lineage", destination_owner: "frontend",
        destination_port: "retire_original_parcel", bit_width: 64)
    val malformed = HwParcelRetirementComposition(node_id: canonical.node_id,
        config: canonical.config, frontend: canonical.frontend, producer: canonical.producer,
        producer_entity: canonical.producer_entity, bindings: rewired)
    expect(malformed.shape_diagnostic()).to_equal(
        "HWIR-E-RETIRE-COMPOSITION-BINDINGS: retirement composition requires the closed reset, dispatch, and receipt wiring set")
else:
    expect(false).to_equal(true)
```

</details>

#### should reject a substituted child route before it can be bound

- should reject a substituted child route before it can be bound
- Substitute an otherwise valid frontend route with a legacy route
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("should reject a substituted child route before it can be bound")
step("Substitute an otherwise valid frontend route with a legacy route")
val built = strict_zca_single_outstanding_retirement_composition(
    "retirement_child_schema_contract", CoreConfig.rv64_zca_mission_critical(),
    "riscv_gen2_rv64_architectural_retirement")
if built.is_ok():
    val malformed = built.ok().unwrap()
    malformed.frontend_route = "legacy-vhdl"
    expect(malformed.shape_diagnostic()).to_equal(
        "HWIR-E-RETIRE-COMPOSITION-CHILD-SCHEMA: retirement composition requires the admitted frontend and strict producer child schemas")
else:
    expect(false).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/50.mir/hwir_retirement_composition_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering strict Gen2 retirement receipt composition.
- strict Gen2 retirement receipt composition

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
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

- Canonical SPipe generation for source `9e9c6302fa3555fdb891161daf3a07a78091bded37ceaf14320d7f5d52243eea`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `9e9c6302fa3555fdb891161daf3a07a78091bded37ceaf14320d7f5d52243eea`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `9e9c6302fa3555fdb891161daf3a07a78091bded37ceaf14320d7f5d52243eea`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **83/100**; effective score: **83/100**; blockers: **0**.

SSpec documentization score: 83/100
source: test/01_unit/compiler/50.mir/hwir_retirement_composition_spec.spl
mirror: doc/06_spec/01_unit/compiler/50.mir/hwir_retirement_composition_spec.md (current)
findings: 10 blockers: 0
  narrative=100 structure=80 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/50.mir/hwir_retirement_composition_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/50.mir/hwir_retirement_composition_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/50.mir/hwir_retirement_composition_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 3 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/50.mir/hwir_retirement_composition_spec.spl:21:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should bind the one-entry frontend and receipt producer to one reset for RV32 and RV64' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/compiler/50.mir/hwir_retirement_composition_spec.spl:21:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should bind the one-entry frontend and receipt producer to one reset for RV32 and RV64' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/50.mir/hwir_retirement_composition_spec.spl:47:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should reject a producer that loses the shared reset or receipt width' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/compiler/50.mir/hwir_retirement_composition_spec.spl:47:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should reject a producer that loses the shared reset or receipt width' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/50.mir/hwir_retirement_composition_spec.spl:66:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should reject omitted or rewired receipt bindings before composition' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/compiler/50.mir/hwir_retirement_composition_spec.spl:66:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should reject omitted or rewired receipt bindings before composition' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/50.mir/hwir_retirement_composition_spec.spl:88:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should reject a substituted child route before it can be bound' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->

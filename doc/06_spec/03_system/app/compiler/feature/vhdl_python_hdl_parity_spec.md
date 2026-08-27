# Vhdl Python Hdl Parity Specification

> Tests covering VHDL Python-HDL parity acceptance.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Vhdl Python Hdl Parity Specification

## Scenarios

### VHDL Python-HDL parity acceptance

#### renders deterministic one-DUT testbench assertions and source-map anchors

- renders deterministic one-DUT testbench assertions and source-map anchors


<details>
<summary>Executable SSpec</summary>

Runnable source: 33 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("renders deterministic one-DUT testbench assertions and source-map anchors")
val artifact = render_vhdl_testbench(VhdlTestbenchCase(
    testbench_name: "parity_tb",
    dut_entity: "parity_gate",
    test_name: "parity gate returns high",
    test_source_line: 42,
    ports: [
        VhdlTestbenchPort(name: "a", direction: "in", type_name: "std_logic", source_line: 3),
        VhdlTestbenchPort(name: "y", direction: "out", type_name: "std_logic", source_line: 3)
    ],
    stimuli: [
        VhdlTestbenchAssignment(target: "a", literal: "'1'", source_line: 43)
    ],
    assertions: [
        VhdlTestbenchAssertion(
            actual: "y",
            expected: "'1'",
            test_name: "parity gate returns high",
            expectation_index: 0,
            source_line: 44
        )
    ],
    clock_name: "",
    reset_name: "",
    reset_asserted: ""
))

expect(artifact.testbench_vhdl).to_contain("dut: entity work.parity_gate")
expect(artifact.testbench_vhdl).to_contain("assert y = '1'")
expect(artifact.testbench_vhdl).to_contain("severity failure;")
expect(artifact.source_map_json).to_contain("\"testbench\": \"parity_tb\"")
expect(artifact.source_map_json).to_contain("\"expectationIndex\":0")
```

</details>

#### renders supported ROM templates and rejects ambiguous RAM policy

- renders supported ROM templates and rejects ambiguous RAM policy
   - Expected: rom.is_ok() is true
   - Expected: ram.is_err() is true
   - Expected: ram.unwrap_err().code equals `VHDL-MEM-RDW-AMBIGUOUS`


<details>
<summary>Executable SSpec</summary>

Runnable source: 30 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("renders supported ROM templates and rejects ambiguous RAM policy")
val rom = render_static_rom_template(VhdlStaticRomTemplate(
    name: "parity_rom",
    type_name: "parity_rom_t",
    data_type: "std_logic_vector(1 downto 0)",
    depth: 2,
    values: ["\"00\"", "\"11\""],
    default_value: "\"00\""
))

expect(rom.is_ok()).to_equal(true)
expect(rom.unwrap().vhdl).to_contain("constant parity_rom : parity_rom_t := (")

val ram = render_single_port_sync_ram_template(VhdlSinglePortSyncRamTemplate(
    name: "parity_ram",
    type_name: "parity_ram_t",
    data_type: "std_logic_vector(7 downto 0)",
    depth: 4,
    clock: "clk",
    write_enable: "we",
    address: "addr",
    write_data: "din",
    read_data: "dout",
    initial_value: "x\"00\"",
    read_during_write: VhdlReadDuringWritePolicy.Ambiguous("policy not selected")
))

expect(ram.is_err()).to_equal(true)
expect(ram.unwrap_err().code).to_equal("VHDL-MEM-RDW-AMBIGUOUS")
```

</details>

#### renders ordered multi-DUT multi-phase source-test suites

- renders ordered multi-DUT multi-phase source-test suites
   - Expected: result.is_ok() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 66 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("renders ordered multi-DUT multi-phase source-test suites")
val drive = VhdlTestbenchPhase(
    name: "drive producer",
    source_line: 70,
    stimuli: [
        VhdlTestbenchAssignment(target: "producer_en", literal: "'1'", source_line: 71),
        VhdlTestbenchAssignment(target: "consumer_ready", literal: "'0'", source_line: 72)
    ],
    assertions: [
        VhdlTestbenchAssertion(actual: "shared_valid", expected: "'1'", test_name: "pipeline", expectation_index: 0, source_line: 73)
    ],
    wait_for: "2 ns"
)
val accept = VhdlTestbenchPhase(
    name: "consumer accepts",
    source_line: 74,
    stimuli: [
        VhdlTestbenchAssignment(target: "consumer_ready", literal: "'1'", source_line: 75)
    ],
    assertions: [
        VhdlTestbenchAssertion(actual: "consumer_done", expected: "'1'", test_name: "pipeline", expectation_index: 1, source_line: 76)
    ],
    wait_for: ""
)

val result = render_vhdl_testbench_suite(VhdlTestbenchSuite(
    testbench_name: "pipeline_tb",
    test_name: "pipeline",
    test_source_line: 69,
    duts: [
        VhdlTestbenchDut(
            instance_name: "producer_dut",
            entity: "producer",
            ports: [
                VhdlTestbenchPort(name: "producer_en", direction: "in", type_name: "std_logic", source_line: 60),
                VhdlTestbenchPort(name: "shared_valid", direction: "out", type_name: "std_logic", source_line: 61)
            ],
            source_line: 60
        ),
        VhdlTestbenchDut(
            instance_name: "consumer_dut",
            entity: "consumer",
            ports: [
                VhdlTestbenchPort(name: "shared_valid", direction: "in", type_name: "std_logic", source_line: 62),
                VhdlTestbenchPort(name: "consumer_ready", direction: "in", type_name: "std_logic", source_line: 63),
                VhdlTestbenchPort(name: "consumer_done", direction: "out", type_name: "std_logic", source_line: 64)
            ],
            source_line: 62
        )
    ],
    phases: [drive, accept],
    clock_name: "",
    reset_name: "",
    reset_asserted: ""
))

expect(result.is_ok()).to_equal(true)
val artifact = result.unwrap()
expect(artifact.testbench_vhdl).to_contain("producer_dut: entity work.producer")
expect(artifact.testbench_vhdl).to_contain("consumer_dut: entity work.consumer")
expect(artifact.testbench_vhdl).to_contain("-- phase: drive producer")
expect(artifact.testbench_vhdl).to_contain("assert consumer_done = '1'")
expect(artifact.source_map_json).to_contain("\"duts\": [{\"instance\":\"producer_dut\"")
expect(artifact.source_map_json).to_contain("\"phases\": [{\"name\":\"drive producer\"")
expect(artifact.source_map_json).to_contain("\"phase\":\"consumer accepts\",\"expectationIndex\":1")
```

</details>

#### keeps parity docs aligned with supported and deferred lanes

- keeps parity docs aligned with supported and deferred lanes
   - Expected: requirements does not contain `Anonymous hardware outputs are not a stable VHDL public API`
   - Expected: pending does not contain `skip "`
   - Expected: pending does not contain `pure Simple structured generic and clock-domain coverage replaces remaining c... (full value in folded executable source)`
   - Expected: pending does not contain `implicit heap allocation and pointer-like addressing fail before VHDL emissio... (full value in folded executable source)`
   - Expected: pending does not contain `payload enum matching and payload field projection`
   - Expected: pending does not contain `anonymous same-type hardware outputs`
   - Expected: pending does not contain `reset domain API accepts active-low asynchronous reset syntax`
   - Expected: pending does not contain `interface bundles lower scalar fields to grouped flattened ports`
   - Expected: pending does not contain `testbench conversion emits a standalone no-port VHDL testbench entity`
   - Expected: pending does not contain `vendor synthesis smoke skips with clear reason when disabled`


<details>
<summary>Executable SSpec</summary>

Runnable source: 31 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("keeps parity docs aligned with supported and deferred lanes")
val requirements = rt_file_read_text("doc/02_requirements/feature/vhdl_python_hdl_parity.md") ?? ""
val roadmap = rt_file_read_text("doc/03_plan/vhdl_python_hdl_parity_roadmap.md") ?? ""
val matrix = rt_file_read_text("doc/04_architecture/hardware/vhdl/vhdl_support_matrix.md") ?? ""
val design = rt_file_read_text("doc/05_design/vhdl_python_hdl_parity.md") ?? ""
val pending = rt_file_read_text("test/unit/compiler/vhdl_python_hdl_parity_spec.spl.skip") ?? ""

expect(requirements).to_contain("Payload enum lowering supports tagged-record representation")
expect(requirements).to_contain("unsupported MIR instructions")
expect(requirements.contains("Anonymous hardware outputs are not a stable VHDL public API")).to_equal(false)
expect(roadmap).to_contain("multi-DUT/multi-phase")
expect(roadmap).to_contain("vendor smoke skip/report/log behavior")
expect(matrix).to_contain("unsupported-MIR hard diagnostic")
expect(matrix).to_contain("hard diagnostics for unsupported implicit-width behavior")
expect(matrix).to_contain("deterministic `out_N` output ports")
expect(matrix).to_contain("Implicit heap allocation, pointer wrappers, pointer dereference, and dynamic pointer-like addressing fail before VHDL file emission")
expect(matrix).to_contain("Explicit memory-interface boundary")
expect(design).to_contain("render_vhdl_testbench_suite")
expect(design).to_contain("explicit diagnostics; compatibility parsing must not be documented as pure-Simple ownership")
expect(pending).to_contain("VHDL Python-HDL Parity Closure")
expect(pending).to_contain("No pending `.skip` entries remain")
expect(pending.contains("skip \"")).to_equal(false)
expect(pending.contains("pure Simple structured generic and clock-domain coverage replaces remaining compatibility source-facade fallback")).to_equal(false)
expect(pending.contains("implicit heap allocation and pointer-like addressing fail before VHDL emission; explicit memory interfaces remain accepted")).to_equal(false)
expect(pending.contains("payload enum matching and payload field projection")).to_equal(false)
expect(pending.contains("anonymous same-type hardware outputs")).to_equal(false)
expect(pending.contains("reset domain API accepts active-low asynchronous reset syntax")).to_equal(false)
expect(pending.contains("interface bundles lower scalar fields to grouped flattened ports")).to_equal(false)
expect(pending.contains("testbench conversion emits a standalone no-port VHDL testbench entity")).to_equal(false)
expect(pending.contains("vendor synthesis smoke skips with clear reason when disabled")).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/app/compiler/feature/vhdl_python_hdl_parity_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering VHDL Python-HDL parity acceptance.
- VHDL Python-HDL parity acceptance

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

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `aac96f820d085891f383690380a40b93262f64d4202031fbab44d3a415e9c5e3`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `aac96f820d085891f383690380a40b93262f64d4202031fbab44d3a415e9c5e3`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `aac96f820d085891f383690380a40b93262f64d4202031fbab44d3a415e9c5e3`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/app/compiler/feature/vhdl_python_hdl_parity_spec.spl
mirror: doc/06_spec/03_system/app/compiler/feature/vhdl_python_hdl_parity_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/app/compiler/feature/vhdl_python_hdl_parity_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/app/compiler/feature/vhdl_python_hdl_parity_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/app/compiler/feature/vhdl_python_hdl_parity_spec.spl:17:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'renders deterministic one-DUT testbench assertions and source-map anchors' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/app/compiler/feature/vhdl_python_hdl_parity_spec.spl:52:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'renders supported ROM templates and rejects ambiguous RAM policy' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/app/compiler/feature/vhdl_python_hdl_parity_spec.spl:84:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'renders ordered multi-DUT multi-phase source-test suites' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

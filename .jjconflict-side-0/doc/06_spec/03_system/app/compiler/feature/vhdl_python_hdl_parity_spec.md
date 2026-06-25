# Vhdl Python Hdl Parity Specification

> _Acceptance smoke for the selected VHDL parity milestone._

<!-- sdn-diagram:id=vhdl_python_hdl_parity_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=vhdl_python_hdl_parity_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

vhdl_python_hdl_parity_spec -> std
vhdl_python_hdl_parity_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=vhdl_python_hdl_parity_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Vhdl Python Hdl Parity Specification

## Scenarios

### VHDL Python-HDL parity acceptance
_Acceptance smoke for the selected VHDL parity milestone._

#### renders deterministic one-DUT testbench assertions and source-map anchors

1. VhdlTestbenchPort
2. VhdlTestbenchPort
3. VhdlTestbenchAssignment


<details>
<summary>Executable SSpec</summary>

Runnable source: 31 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. data type: "std logic vector
   - Expected: rom.is_ok() is true
2. data type: "std logic vector
3. read during write: VhdlReadDuringWritePolicy Ambiguous
   - Expected: ram.is_err() is true
   - Expected: ram.unwrap_err().code equals `VHDL-MEM-RDW-AMBIGUOUS`


<details>
<summary>Executable SSpec</summary>

Runnable source: 28 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. VhdlTestbenchAssignment
2. VhdlTestbenchAssignment
3. VhdlTestbenchAssertion
4. VhdlTestbenchAssignment
5. VhdlTestbenchAssertion
6. VhdlTestbenchPort
7. VhdlTestbenchPort
8. VhdlTestbenchPort
9. VhdlTestbenchPort
10. VhdlTestbenchPort
   - Expected: result.is_ok() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 64 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 29 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val requirements = rt_file_read_text("doc/02_requirements/feature/vhdl_python_hdl_parity.md") ?? ""
val roadmap = rt_file_read_text("doc/03_plan/vhdl_python_hdl_parity_roadmap.md") ?? ""
val matrix = rt_file_read_text("doc/04_architecture/vhdl_support_matrix.md") ?? ""
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
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
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

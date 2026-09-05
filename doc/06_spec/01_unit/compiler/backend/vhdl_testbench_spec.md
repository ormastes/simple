# Vhdl Testbench Specification

> Tests covering VHDL testbench renderer.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Vhdl Testbench Specification

## Scenarios

### VHDL testbench renderer

#### renders one DUT with literal stimulus and expect-style equality assertion

- renders one DUT with literal stimulus and expect-style equality assertion
   - Expected: artifact.testbench_entity equals `and_gate_tb`


<details>
<summary>Executable SSpec</summary>

Runnable source: 46 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("renders one DUT with literal stimulus and expect-style equality assertion")
val tb = VhdlTestbenchCase(
    testbench_name: "and_gate_tb",
    dut_entity: "and_gate",
    test_name: "and gate returns high",
    test_source_line: 12,
    ports: [
        VhdlTestbenchPort(name: "a", direction: "in", type_name: "std_logic", source_line: 3),
        VhdlTestbenchPort(name: "b", direction: "in", type_name: "std_logic", source_line: 3),
        VhdlTestbenchPort(name: "y", direction: "out", type_name: "std_logic", source_line: 3)
    ],
    stimuli: [
        VhdlTestbenchAssignment(target: "a", literal: "'1'", source_line: 13),
        VhdlTestbenchAssignment(target: "b", literal: "'1'", source_line: 14)
    ],
    assertions: [
        VhdlTestbenchAssertion(
            actual: "y",
            expected: "'1'",
            test_name: "and gate returns high",
            expectation_index: 0,
            source_line: 15
        )
    ],
    clock_name: "",
    reset_name: "",
    reset_asserted: ""
)

val artifact = render_vhdl_testbench(tb)
val vhdl = artifact.testbench_vhdl

expect(artifact.testbench_entity).to_equal("and_gate_tb")
expect(vhdl).to_contain("entity and_gate_tb is")
expect(vhdl).to_contain("dut: entity work.and_gate")
expect(vhdl).to_contain("stimulus: process\n    begin")
expect(vhdl).to_contain("a <= '1';")
expect(vhdl).to_contain("b <= '1';")
expect(vhdl).to_contain("assert y = '1'")
expect(vhdl).to_contain("report \"and gate returns high expectation 0: expected y to equal '1'\"")
expect(vhdl).to_contain("severity failure;")
expect(artifact.source_map_json).to_contain("\"testName\": {\"name\":\"and gate returns high\"")
expect(artifact.source_map_json).to_contain("\"ports\": [{\"name\":\"a\",\"direction\":\"in\",\"type\":\"std_logic\"")
expect(artifact.source_map_json).to_contain("\"expectations\": [{\"testName\":\"and gate returns high\",\"phase\":\"and gate returns high\",\"expectationIndex\":0")
expect(artifact.source_map_json).to_contain("\"sourceLine\":15")
```

</details>

#### renders clock and reset driven DUT tests

- renders clock and reset driven DUT tests


<details>
<summary>Executable SSpec</summary>

Runnable source: 49 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("renders clock and reset driven DUT tests")
val tb = VhdlTestbenchCase(
    testbench_name: "reg1_tb",
    dut_entity: "reg1",
    test_name: "register captures d after reset",
    test_source_line: 20,
    ports: [
        VhdlTestbenchPort(name: "clk", direction: "in", type_name: "std_logic", source_line: 2),
        VhdlTestbenchPort(name: "reset_n", direction: "in", type_name: "std_logic", source_line: 2),
        VhdlTestbenchPort(name: "d", direction: "in", type_name: "std_logic", source_line: 2),
        VhdlTestbenchPort(name: "q", direction: "out", type_name: "std_logic", source_line: 2)
    ],
    stimuli: [
        VhdlTestbenchAssignment(target: "d", literal: "'1'", source_line: 21)
    ],
    assertions: [
        VhdlTestbenchAssertion(
            actual: "q",
            expected: "'1'",
            test_name: "register captures d after reset",
            expectation_index: 0,
            source_line: 22
        )
    ],
    clock_name: "clk",
    reset_name: "reset_n",
    reset_asserted: "'0'"
)

val artifact = render_vhdl_testbench(tb)
val vhdl = artifact.testbench_vhdl

expect(vhdl).to_contain("signal clk : std_logic := '0';")
expect(vhdl).to_contain("clock_driver: process\n    begin\n        loop")
expect(vhdl).to_contain("clk <= '0';")
expect(vhdl).to_contain("wait for 5 ns;")
expect(vhdl).to_contain("clk <= '1';")
expect(vhdl).to_contain("reset_n <= '0';")
expect(vhdl).to_contain("wait for 10 ns;")
expect(vhdl).to_contain("reset_n <= '1';")
expect(vhdl).to_contain("wait until rising_edge(clk);")
expect(vhdl).to_contain("d <= '1';")
expect(vhdl).to_contain("assert q = '1'")
expect(artifact.source_map_json).to_contain("\"testbench\": \"reg1_tb\"")
expect(artifact.source_map_json).to_contain("\"dutEntity\": \"reg1\"")
expect(artifact.source_map_json).to_contain("\"name\":\"clk\",\"direction\":\"in\",\"type\":\"std_logic\"")
expect(artifact.source_map_json).to_contain("\"portMapLine\":")
expect(artifact.source_map_json).to_contain("\"expectationIndex\":0")
```

</details>

#### renders multiple DUT instances across ordered source-test phases

- renders multiple DUT instances across ordered source-test phases
   - Expected: result.is_ok() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 87 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("renders multiple DUT instances across ordered source-test phases")
val phase0 = VhdlTestbenchPhase(
    name: "drive producer",
    source_line: 40,
    stimuli: [
        VhdlTestbenchAssignment(target: "producer_en", literal: "'1'", source_line: 41),
        VhdlTestbenchAssignment(target: "consumer_ready", literal: "'0'", source_line: 42)
    ],
    assertions: [
        VhdlTestbenchAssertion(
            actual: "shared_valid",
            expected: "'1'",
            test_name: "pipeline handshake",
            expectation_index: 0,
            source_line: 43
        )
    ],
    wait_for: "2 ns"
)
val phase1 = VhdlTestbenchPhase(
    name: "consumer accepts",
    source_line: 44,
    stimuli: [
        VhdlTestbenchAssignment(target: "consumer_ready", literal: "'1'", source_line: 45)
    ],
    assertions: [
        VhdlTestbenchAssertion(
            actual: "consumer_done",
            expected: "'1'",
            test_name: "pipeline handshake",
            expectation_index: 1,
            source_line: 46
        )
    ],
    wait_for: ""
)

val result = render_vhdl_testbench_suite(VhdlTestbenchSuite(
    testbench_name: "pipeline_tb",
    test_name: "pipeline handshake",
    test_source_line: 39,
    duts: [
        VhdlTestbenchDut(
            instance_name: "producer_dut",
            entity: "producer",
            ports: [
                VhdlTestbenchPort(name: "producer_en", direction: "in", type_name: "std_logic", source_line: 30),
                VhdlTestbenchPort(name: "shared_valid", direction: "out", type_name: "std_logic", source_line: 31)
            ],
            source_line: 30
        ),
        VhdlTestbenchDut(
            instance_name: "consumer_dut",
            entity: "consumer",
            ports: [
                VhdlTestbenchPort(name: "shared_valid", direction: "in", type_name: "std_logic", source_line: 32),
                VhdlTestbenchPort(name: "consumer_ready", direction: "in", type_name: "std_logic", source_line: 33),
                VhdlTestbenchPort(name: "consumer_done", direction: "out", type_name: "std_logic", source_line: 34)
            ],
            source_line: 32
        )
    ],
    phases: [phase0, phase1],
    clock_name: "",
    reset_name: "",
    reset_asserted: ""
))

expect(result.is_ok()).to_equal(true)
val artifact = result.unwrap()
val vhdl = artifact.testbench_vhdl

expect(vhdl).to_contain("producer_dut: entity work.producer")
expect(vhdl).to_contain("consumer_dut: entity work.consumer")
expect(vhdl).to_contain("shared_valid => shared_valid")
expect(vhdl).to_contain("-- phase: drive producer")
expect(vhdl).to_contain("wait for 2 ns;")
expect(vhdl).to_contain("-- phase: consumer accepts")
expect(vhdl).to_contain("wait for 1 ns;")
expect(vhdl).to_contain("assert shared_valid = '1'")
expect(vhdl).to_contain("assert consumer_done = '1'")
expect(artifact.source_map_json).to_contain("\"duts\": [{\"instance\":\"producer_dut\",\"entity\":\"producer\"")
expect(artifact.source_map_json).to_contain("{\"instance\":\"consumer_dut\",\"entity\":\"consumer\"")
expect(artifact.source_map_json).to_contain("\"phases\": [{\"name\":\"drive producer\"")
expect(artifact.source_map_json).to_contain("{\"name\":\"consumer accepts\"")
expect(artifact.source_map_json).to_contain("\"phase\":\"consumer accepts\",\"expectationIndex\":1")
```

</details>

#### rejects source-test conversion without DUTs before VHDL output

- rejects source-test conversion without DUTs before VHDL output
   - Expected: result.is_err() is true
   - Expected: diagnostic.code equals `VHDL-TB-NO-DUT`
   - Expected: diagnostic.source_line equals `50`


<details>
<summary>Executable SSpec</summary>

Runnable source: 26 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("rejects source-test conversion without DUTs before VHDL output")
val result = render_vhdl_testbench_suite(VhdlTestbenchSuite(
    testbench_name: "empty_tb",
    test_name: "no dut test",
    test_source_line: 50,
    duts: [],
    phases: [
        VhdlTestbenchPhase(
            name: "phase",
            source_line: 51,
            stimuli: [],
            assertions: [],
            wait_for: ""
        )
    ],
    clock_name: "",
    reset_name: "",
    reset_asserted: ""
))

expect(result.is_err()).to_equal(true)
val diagnostic = result.unwrap_err()
expect(diagnostic.code).to_equal("VHDL-TB-NO-DUT")
expect(diagnostic.message).to_contain("requires at least one DUT")
expect(diagnostic.source_line).to_equal(50)
```

</details>

#### rejects incompatible shared DUT signals before VHDL output

- rejects incompatible shared DUT signals before VHDL output
   - Expected: result.is_err() is true
   - Expected: diagnostic.code equals `VHDL-TB-SIGNAL-COLLISION`
   - Expected: diagnostic.source_line equals `62`


<details>
<summary>Executable SSpec</summary>

Runnable source: 43 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("rejects incompatible shared DUT signals before VHDL output")
val result = render_vhdl_testbench_suite(VhdlTestbenchSuite(
    testbench_name: "collision_tb",
    test_name: "bad shared signal",
    test_source_line: 60,
    duts: [
        VhdlTestbenchDut(
            instance_name: "left_dut",
            entity: "left",
            ports: [
                VhdlTestbenchPort(name: "shared", direction: "out", type_name: "std_logic", source_line: 61)
            ],
            source_line: 61
        ),
        VhdlTestbenchDut(
            instance_name: "right_dut",
            entity: "right",
            ports: [
                VhdlTestbenchPort(name: "shared", direction: "in", type_name: "std_logic_vector(7 downto 0)", source_line: 62)
            ],
            source_line: 62
        )
    ],
    phases: [
        VhdlTestbenchPhase(
            name: "phase",
            source_line: 63,
            stimuli: [],
            assertions: [],
            wait_for: ""
        )
    ],
    clock_name: "",
    reset_name: "",
    reset_asserted: ""
))

expect(result.is_err()).to_equal(true)
val diagnostic = result.unwrap_err()
expect(diagnostic.code).to_equal("VHDL-TB-SIGNAL-COLLISION")
expect(diagnostic.message).to_contain("incompatible DUT port types")
expect(diagnostic.source_line).to_equal(62)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/backend/vhdl_testbench_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering VHDL testbench renderer.
- VHDL testbench renderer

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
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

- Canonical SPipe generation for source `9707af3b87fb686287285b9f505cda0efef65f09a95c0bd9a3c0d84d18f4d5a4`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `9707af3b87fb686287285b9f505cda0efef65f09a95c0bd9a3c0d84d18f4d5a4`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `9707af3b87fb686287285b9f505cda0efef65f09a95c0bd9a3c0d84d18f4d5a4`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/01_unit/compiler/backend/vhdl_testbench_spec.spl
mirror: doc/06_spec/01_unit/compiler/backend/vhdl_testbench_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/backend/vhdl_testbench_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/backend/vhdl_testbench_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/backend/vhdl_testbench_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/backend/vhdl_testbench_spec.spl:17:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'renders one DUT with literal stimulus and expect-style equality assertion' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/backend/vhdl_testbench_spec.spl:65:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'renders clock and reset driven DUT tests' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/backend/vhdl_testbench_spec.spl:116:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'renders multiple DUT instances across ordered source-test phases' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

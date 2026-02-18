# vhdl
*Source:* `test/feature/usage/vhdl_spec.spl`

## Feature: VHDL Toolchain Availability

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | checks GHDL availability | pass |
| 2 | checks Yosys availability | pass |

**Example:** checks GHDL availability
    Given val available = ghdl_available()

**Example:** checks Yosys availability
    Given val available = yosys_available()

## Feature: GHDL Analysis

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | analyzes valid VHDL file | pass |
| 2 | rejects invalid VHDL file | pass |

**Example:** analyzes valid VHDL file
    Given val vhdl_src = "library ieee;{NL}use ieee.std_logic_1164.all;{NL}{NL}entity test_ent is{NL}end entity test_ent;{NL}{NL}architecture rtl of test_ent is{NL}begin{NL}end architecture rtl;{NL}"
    Given val path = "/tmp/simple_test_vhdl_analyze.vhd"
    Given val result = ghdl_analyze(path)
    Then  expect(result.exit_code).to_equal(0)

**Example:** rejects invalid VHDL file
    Given val vhdl_src = "this is not valid VHDL;"
    Given val path = "/tmp/simple_test_vhdl_invalid.vhd"
    Given val result = ghdl_analyze(path)

## Feature: GHDL Elaboration

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | elaborates valid entity | pass |

**Example:** elaborates valid entity
    Given val vhdl_src = "library ieee;{NL}use ieee.std_logic_1164.all;{NL}{NL}entity elab_test is{NL}end entity elab_test;{NL}{NL}architecture rtl of elab_test is{NL}begin{NL}end architecture rtl;{NL}"
    Given val path = "/tmp/simple_test_vhdl_elab.vhd"
    Given val result = ghdl_analyze_and_elaborate(path, "elab_test")

## Feature: GHDL Simulation

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | runs simulation with stop time | pass |

**Example:** runs simulation with stop time
    Given val vhdl_src = "library ieee;{NL}use ieee.std_logic_1164.all;{NL}{NL}entity sim_test is{NL}end entity sim_test;{NL}{NL}architecture rtl of sim_test is{NL}begin{NL}end architecture rtl;{NL}"
    Given val path = "/tmp/simple_test_vhdl_sim.vhd"
    Given val analyze = ghdl_analyze(path)
    Given val elab = ghdl_elaborate("sim_test")
    Given val run_result = ghdl_run("sim_test", Some("100ns"))

## Feature: GHDL Synthesis

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | synthesizes a simple entity | pass |

**Example:** synthesizes a simple entity
    Given val vhdl_src = "library ieee;{NL}use ieee.std_logic_1164.all;{NL}use ieee.numeric_std.all;{NL}{NL}entity synth_test is{NL}    port ({NL}        a : in  unsigned(7 downto 0);{NL}        b : in  unsigned(7 downto 0);{NL}        s : out unsigned(7 downto 0){NL}    );{NL}end entity synth_test;{NL}{NL}architecture rtl of synth_test is{NL}begin{NL}    s <= a + b;{NL}end architecture rtl;{NL}"
    Given val path = "/tmp/simple_test_vhdl_synth.vhd"
    Given val analyze = ghdl_analyze(path)
    Given val synth = ghdl_synth("synth_test")

## Feature: VHDL File Operations

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | writes and reads VHDL file | pass |
| 2 | returns nil for non-existent file | pass |
| 3 | checks file existence | pass |

**Example:** writes and reads VHDL file
    Given val path = "/tmp/simple_test_vhdl_io.vhd"
    Given val content = "-- test file{NL}library ieee;{NL}"
    Given val read_content = vhdl_read_file(path)
    Then  expect(read_content.unwrap()).to_equal(content)

**Example:** returns nil for non-existent file
    Given val result = vhdl_read_file("/tmp/simple_test_nonexistent_vhdl_file_12345.vhd")

**Example:** checks file existence
    Given val path = "/tmp/simple_test_vhdl_exists.vhd"

## Feature: VhdlToolResult structure

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | has correct fields on success | pass |

**Example:** has correct fields on success
    Given val vhdl_src = "library ieee;{NL}use ieee.std_logic_1164.all;{NL}{NL}entity result_test is{NL}end entity result_test;{NL}{NL}architecture rtl of result_test is{NL}begin{NL}end architecture rtl;{NL}"
    Given val path = "/tmp/simple_test_vhdl_result.vhd"
    Given val result = ghdl_analyze(path)
    Then  expect(result.exit_code).to_equal(0)

## Feature: Yosys VHDL Synthesis

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | synthesizes VHDL via Yosys+GHDL plugin | pass |

**Example:** synthesizes VHDL via Yosys+GHDL plugin
    Given val vhdl_src = "library ieee;{NL}use ieee.std_logic_1164.all;{NL}use ieee.numeric_std.all;{NL}{NL}entity yosys_test is{NL}    port ({NL}        a : in  unsigned(7 downto 0);{NL}        b : in  unsigned(7 downto 0);{NL}        s : out unsigned(7 downto 0){NL}    );{NL}end entity yosys_test;{NL}{NL}architecture rtl of yosys_test is{NL}begin{NL}    s <= a + b;{NL}end architecture rtl;{NL}"
    Given val path = "/tmp/simple_test_yosys_vhdl.vhd"
    Given val json_path = "/tmp/simple_test_yosys_vhdl.json"
    Given val result = yosys_synth_ghdl(path, "yosys_test", json_path)



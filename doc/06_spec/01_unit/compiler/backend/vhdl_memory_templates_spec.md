# Vhdl Memory Templates Specification

> Tests covering VHDL memory template renderer.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Vhdl Memory Templates Specification

## Scenarios

### VHDL memory template renderer

#### renders a static ROM constant with explicit initializer values

- renders a static ROM constant with explicit initializer values
   - Expected: result.is_ok() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("renders a static ROM constant with explicit initializer values")
val result = render_static_rom_template(VhdlStaticRomTemplate(
    name: "coeff_rom",
    type_name: "coeff_rom_t",
    data_type: "std_logic_vector(7 downto 0)",
    depth: 4,
    values: ["x\"11\"", "x\"22\""],
    default_value: "x\"00\""
))

expect(result.is_ok()).to_equal(true)
val vhdl = result.unwrap().vhdl
expect(vhdl).to_contain("type coeff_rom_t is array (0 to 3) of std_logic_vector(7 downto 0);")
expect(vhdl).to_contain("constant coeff_rom : coeff_rom_t := (")
expect(vhdl).to_contain("0 => x\"11\",")
expect(vhdl).to_contain("1 => x\"22\",")
expect(vhdl).to_contain("others => x\"00\"")
```

</details>

#### renders a registered ROM read process

- renders a registered ROM read process
   - Expected: result.is_ok() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("renders a registered ROM read process")
val result = render_registered_rom_read_template(VhdlRegisteredRomReadTemplate(
    name: "lookup_rom",
    type_name: "lookup_rom_t",
    data_type: "unsigned(15 downto 0)",
    depth: 8,
    values: ["to_unsigned(3, 16)", "to_unsigned(5, 16)"],
    default_value: "to_unsigned(0, 16)",
    clock: "clk",
    address: "addr",
    data_out: "q"
))

expect(result.is_ok()).to_equal(true)
val artifact = result.unwrap()
expect(artifact.declarations).to_contain("constant lookup_rom : lookup_rom_t := (")
expect(artifact.body).to_contain("lookup_rom_read: process(clk)")
expect(artifact.body).to_contain("if rising_edge(clk) then")
expect(artifact.body).to_contain("q <= lookup_rom(to_integer(unsigned(addr)));")
```

</details>

#### renders read-first single-port synchronous RAM policy

- renders read-first single-port synchronous RAM policy
   - Expected: result.is_ok() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("renders read-first single-port synchronous RAM policy")
val result = render_single_port_sync_ram_template(VhdlSinglePortSyncRamTemplate(
    name: "sample_ram",
    type_name: "sample_ram_t",
    data_type: "std_logic_vector(31 downto 0)",
    depth: 16,
    clock: "clk",
    write_enable: "we",
    address: "addr",
    write_data: "din",
    read_data: "dout",
    initial_value: "x\"00000000\"",
    read_during_write: VhdlReadDuringWritePolicy.ReadFirst
))

expect(result.is_ok()).to_equal(true)
val artifact = result.unwrap()
expect(artifact.declarations).to_contain("signal sample_ram : sample_ram_t := (others => x\"00000000\");")
expect(artifact.body).to_contain("dout <= sample_ram(to_integer(unsigned(addr)));")
expect(artifact.body).to_contain("if we = '1' then")
expect(artifact.body).to_contain("sample_ram(to_integer(unsigned(addr))) <= din;")
```

</details>

#### renders write-first single-port synchronous RAM policy

- renders write-first single-port synchronous RAM policy
   - Expected: result.is_ok() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("renders write-first single-port synchronous RAM policy")
val result = render_single_port_sync_ram_template(VhdlSinglePortSyncRamTemplate(
    name: "sample_ram",
    type_name: "sample_ram_t",
    data_type: "std_logic_vector(31 downto 0)",
    depth: 16,
    clock: "clk",
    write_enable: "we",
    address: "addr",
    write_data: "din",
    read_data: "dout",
    initial_value: "x\"00000000\"",
    read_during_write: VhdlReadDuringWritePolicy.WriteFirst
))

expect(result.is_ok()).to_equal(true)
val body = result.unwrap().body
expect(body).to_contain("sample_ram(to_integer(unsigned(addr))) <= din;")
expect(body).to_contain("dout <= din;")
expect(body).to_contain("else")
expect(body).to_contain("dout <= sample_ram(to_integer(unsigned(addr)));")
```

</details>

#### renders no-change single-port synchronous RAM policy

- renders no-change single-port synchronous RAM policy
   - Expected: result.is_ok() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("renders no-change single-port synchronous RAM policy")
val result = render_single_port_sync_ram_template(VhdlSinglePortSyncRamTemplate(
    name: "sample_ram",
    type_name: "sample_ram_t",
    data_type: "std_logic_vector(31 downto 0)",
    depth: 16,
    clock: "clk",
    write_enable: "we",
    address: "addr",
    write_data: "din",
    read_data: "dout",
    initial_value: "x\"00000000\"",
    read_during_write: VhdlReadDuringWritePolicy.NoChange
))

expect(result.is_ok()).to_equal(true)
val body = result.unwrap().body
expect(body).to_contain("if we = '1' then")
expect(body).to_contain("sample_ram(to_integer(unsigned(addr))) <= din;")
expect(body).to_contain("else")
expect(body).to_contain("dout <= sample_ram(to_integer(unsigned(addr)));")
```

</details>

#### rejects ambiguous read-during-write policies with diagnostics

- rejects ambiguous read-during-write policies with diagnostics
   - Expected: result.is_err() is true
   - Expected: diagnostic.code equals `VHDL-MEM-RDW-AMBIGUOUS`


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects ambiguous read-during-write policies with diagnostics")
val result = render_single_port_sync_ram_template(VhdlSinglePortSyncRamTemplate(
    name: "sample_ram",
    type_name: "sample_ram_t",
    data_type: "std_logic_vector(31 downto 0)",
    depth: 16,
    clock: "clk",
    write_enable: "we",
    address: "addr",
    write_data: "din",
    read_data: "dout",
    initial_value: "x\"00000000\"",
    read_during_write: VhdlReadDuringWritePolicy.Ambiguous("source did not choose old, new, or unchanged read data")
))

expect(result.is_err()).to_equal(true)
val diagnostic = result.unwrap_err()
expect(diagnostic.code).to_equal("VHDL-MEM-RDW-AMBIGUOUS")
expect(diagnostic.message).to_contain("Vendor-safe VHDL memory policy requires explicit read-during-write behavior")
```

</details>

#### renders a constrained signal memory with a named array type

- renders a constrained signal memory with a named array type
   - Expected: result.is_ok() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("renders a constrained signal memory with a named array type")
val result = render_constrained_signal_memory_template(VhdlConstrainedSignalMemoryTemplate(
    name: "line_buffer",
    type_name: "line_buffer_memory_t",
    data_type: "unsigned(7 downto 0)",
    depth: 64,
    initial_value: Some("to_unsigned(0, 8)")
))

expect(result.is_ok()).to_equal(true)
val vhdl = result.unwrap().vhdl
expect(vhdl).to_contain("type line_buffer_memory_t is array (0 to 63) of unsigned(7 downto 0);")
expect(vhdl).to_contain("signal line_buffer : line_buffer_memory_t := (others => to_unsigned(0, 8));")
```

</details>

#### rejects unconstrained signal memory before VHDL emission

- rejects unconstrained signal memory before VHDL emission
   - Expected: result.is_err() is true
   - Expected: diagnostic.code equals `VHDL-MEM-UNCONSTRAINED`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects unconstrained signal memory before VHDL emission")
val result = render_constrained_signal_memory_template(VhdlConstrainedSignalMemoryTemplate(
    name: "dynamic_buffer",
    type_name: "dynamic_buffer_memory_t",
    data_type: "std_logic_vector(7 downto 0)",
    depth: 0,
    initial_value: nil
))

expect(result.is_err()).to_equal(true)
val diagnostic = result.unwrap_err()
expect(diagnostic.code).to_equal("VHDL-MEM-UNCONSTRAINED")
expect(diagnostic.message).to_contain("concrete positive depth before vendor-safe VHDL emission")
```

</details>

#### rejects nested general memory before anonymous array VHDL

- rejects nested general memory before anonymous array VHDL
   - Expected: result.is_err() is true
   - Expected: diagnostic.code equals `VHDL-MEM-GENERAL`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects nested general memory before anonymous array VHDL")
val result = render_constrained_signal_memory_template(VhdlConstrainedSignalMemoryTemplate(
    name: "matrix",
    type_name: "matrix_memory_t",
    data_type: "array (0 to 3) of unsigned(7 downto 0)",
    depth: 4,
    initial_value: nil
))

expect(result.is_err()).to_equal(true)
val diagnostic = result.unwrap_err()
expect(diagnostic.code).to_equal("VHDL-MEM-GENERAL")
expect(diagnostic.message).to_contain("nested or general array element type")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/backend/vhdl_memory_templates_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering VHDL memory template renderer.
- VHDL memory template renderer

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

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `a8557214c8ba712d80cbf0a370508445ab78a220254ad2ec96d512cd866c889c`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `a8557214c8ba712d80cbf0a370508445ab78a220254ad2ec96d512cd866c889c`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `a8557214c8ba712d80cbf0a370508445ab78a220254ad2ec96d512cd866c889c`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/compiler/backend/vhdl_memory_templates_spec.spl
mirror: doc/06_spec/01_unit/compiler/backend/vhdl_memory_templates_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/backend/vhdl_memory_templates_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/backend/vhdl_memory_templates_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/backend/vhdl_memory_templates_spec.spl:15:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'renders a static ROM constant with explicit initializer values' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/backend/vhdl_memory_templates_spec.spl:35:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'renders a registered ROM read process' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/backend/vhdl_memory_templates_spec.spl:57:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'renders read-first single-port synchronous RAM policy' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

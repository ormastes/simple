# Vhdl Builder Specification

> Tests covering Vhdl Builder.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Vhdl Builder Specification

## Scenarios

### Vhdl Builder

#### emits library, package, and entity headers

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- emits library, package, and entity headers


<details>
<summary>Executable SSpec</summary>

Runnable source: 34 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("emits library, package, and entity headers")
var builder = VhdlBuilder.create("demo")
builder.emit_library_header()
builder.emit_use_package("work", "demo_pkg")
builder.emit_package_begin("demo")
builder.emit_type_decl("state_t", "(Idle, Running)")
builder.emit_constant_decl("WIDTH", "integer", "32")
builder.emit_package_end("demo")
builder.emit_entity_begin("demo")
builder.emit_generic_begin()
builder.emit_generic_param("N", "integer", Some("8"), true)
builder.emit_generic_end()
builder.emit_port_begin()
builder.emit_port("clk", "in", "std_logic", false)
builder.emit_port("q", "out", "std_logic_vector(N-1 downto 0)", true)
builder.emit_port_end()
builder.emit_entity_end("demo")

val vhdl = builder.build()

check(vhdl.contains("library ieee;"))
check(vhdl.contains("use ieee.std_logic_1164.all;"))
check(vhdl.contains("use work.demo_pkg.all;"))
check(vhdl.contains("package demo_pkg is"))
check(vhdl.contains("type state_t is (Idle, Running);"))
check(vhdl.contains("constant WIDTH : integer := 32;"))
check(vhdl.contains("entity demo is"))
check(vhdl.contains("generic ("))
check(vhdl.contains("N : integer := 8"))
check(vhdl.contains("port ("))
check(vhdl.contains("clk : in std_logic;"))
check(vhdl.contains("q : out std_logic_vector(N-1 downto 0)"))
check(vhdl.contains("end entity demo;"))
```

</details>

#### emits architecture bodies, processes, and control flow

- emits architecture bodies, processes, and control flow


<details>
<summary>Executable SSpec</summary>

Runnable source: 28 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("emits architecture bodies, processes, and control flow")
var builder = VhdlBuilder.create("alu")
builder.emit_architecture_begin("alu", "rtl")
builder.emit_signal_decl("sum", "signed(31 downto 0)", nil)
builder.emit_architecture_body_begin()
builder.emit_process_begin(Some("comb"), ["a", "b"])
builder.emit_process_body_begin()
builder.emit_signal_assign("sum", "a + b")
builder.emit_if_begin("a = b")
builder.emit_var_assign("sum", "a")
builder.emit_else()
builder.emit_signal_assign_delay("sum", "b", 2)
builder.emit_if_end()
builder.emit_process_end(Some("comb"))
builder.emit_architecture_end("rtl")

val vhdl = builder.build()

check(vhdl.contains("architecture rtl of alu is"))
check(vhdl.contains("signal sum : signed(31 downto 0);"))
check(vhdl.contains("comb: process(a, b)"))
check(vhdl.contains("sum <= a + b;"))
check(vhdl.contains("if a = b then"))
check(vhdl.contains("sum := a;"))
check(vhdl.contains("sum <= b after 2 ns;"))
check(vhdl.contains("end process comb;"))
check(vhdl.contains("end architecture rtl;"))
```

</details>

#### emits instances, port maps, and helper text

- emits instances, port maps, and helper text


<details>
<summary>Executable SSpec</summary>

Runnable source: 33 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("emits instances, port maps, and helper text")
var builder = VhdlBuilder.create("top")
val label0 = builder.alloc_label()
val label1 = builder.alloc_label()
builder.emit_comment("instantiate child")
builder.emit_instance_begin(label0, "child")
builder.emit_port_map_begin()
builder.emit_port_map_entry("clk", "clk_i", false)
builder.emit_port_map_entry("rst", "rst_i", false)
builder.emit_port_map_entry("q", "q_o", true)
builder.emit_port_map_end()
builder.emit_synthesis_translate_off()
builder.emit_assert("width > 0", "width must be positive", "error")
builder.emit_synthesis_translate_on()
builder.emit_resize("wide_sig", "narrow_sig", 32, true)
builder.emit_slice("low", "bus", 7, 0)
builder.emit_concat("joined", ["a", "b", "c"])

val vhdl = builder.build()

check(label0.starts_with("label_"))
check(label1.starts_with("label_"))
check(label0 != label1)
check(vhdl.contains("-- instantiate child"))
check(vhdl.contains("{label0}: entity work.child"))
check(vhdl.contains("clk => clk_i,"))
check(vhdl.contains("q => q_o"))
check(vhdl.contains("report \"width must be positive\""))
check(vhdl.contains("severity error;"))
check(vhdl.contains("wide_sig <= resize(narrow_sig, 32);"))
check(vhdl.contains("low <= bus(7 downto 0);"))
check(vhdl.contains("joined <= a & b & c;"))
```

</details>

#### uses the VHDL type mapper for port types

- uses the VHDL type mapper for port types


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("uses the VHDL type mapper for port types")
val mapper = VhdlTypeMapper.create_resolved()
var builder = VhdlBuilder.create("typed")
builder.emit_entity_begin("typed")
builder.emit_port_begin()
builder.emit_port("flag", "in", mapper.map_primitive(PrimitiveType.Bool), false)
builder.emit_port("data", "in", mapper.map_primitive(PrimitiveType.I16), true)
builder.emit_port_end()
builder.emit_entity_end("typed")

val vhdl = builder.build()

check(vhdl.contains("flag : in std_logic;"))
check(vhdl.contains("data : in signed(15 downto 0)"))
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/unit/compiler/backend/vhdl_builder_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Vhdl Builder.
- Vhdl Builder

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

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `633f171121e3d251f3da51482615cfb8374b6693f0ce577f578b39203779e619`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `633f171121e3d251f3da51482615cfb8374b6693f0ce577f578b39203779e619`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `633f171121e3d251f3da51482615cfb8374b6693f0ce577f578b39203779e619`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/compiler/backend/vhdl_builder_spec.spl
mirror: doc/06_spec/unit/compiler/backend/vhdl_builder_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/compiler/backend/vhdl_builder_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/compiler/backend/vhdl_builder_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/compiler/backend/vhdl_builder_spec.spl:16:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'emits library, package, and entity headers' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/backend/vhdl_builder_spec.spl:52:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'emits architecture bodies, processes, and control flow' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/backend/vhdl_builder_spec.spl:82:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'emits instances, port maps, and helper text' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

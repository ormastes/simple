# Vhdl Builder Specification

> 1. var builder = VhdlBuilder create

<!-- sdn-diagram:id=vhdl_builder_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=vhdl_builder_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

vhdl_builder_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=vhdl_builder_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Vhdl Builder Specification

## Scenarios

### Vhdl Builder

#### emits library, package, and entity headers

1. var builder = VhdlBuilder create
2. builder emit library header
3. builder emit use package
4. builder emit package begin
5. builder emit type decl
6. builder emit constant decl
7. builder emit package end
8. builder emit entity begin
9. builder emit generic begin
10. builder emit generic param
11. builder emit generic end
12. builder emit port begin
13. builder emit port
14. builder emit port
15. builder emit port end
16. builder emit entity end
17. check
18. check
19. check
20. check
21. check
22. check
23. check
24. check
25. check
26. check
27. check
28. check
29. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 32 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. var builder = VhdlBuilder create
2. builder emit architecture begin
3. builder emit signal decl
4. builder emit architecture body begin
5. builder emit process begin
6. builder emit process body begin
7. builder emit signal assign
8. builder emit if begin
9. builder emit var assign
10. builder emit else
11. builder emit signal assign delay
12. builder emit if end
13. builder emit process end
14. builder emit architecture end
15. check
16. check
17. check
18. check
19. check
20. check
21. check
22. check
23. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 26 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. var builder = VhdlBuilder create
2. builder emit comment
3. builder emit instance begin
4. builder emit port map begin
5. builder emit port map entry
6. builder emit port map entry
7. builder emit port map entry
8. builder emit port map end
9. builder emit synthesis translate off
10. builder emit assert
11. builder emit synthesis translate on
12. builder emit resize
13. builder emit slice
14. builder emit concat
15. check
16. check
17. check
18. check
19. check
20. check
21. check
22. check
23. check
24. check
25. check
26. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 31 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. var builder = VhdlBuilder create
2. builder emit entity begin
3. builder emit port begin
4. builder emit port
5. builder emit port
6. builder emit port end
7. builder emit entity end
8. check
9. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
| Source | `test/01_unit/compiler/backend/vhdl_builder_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
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

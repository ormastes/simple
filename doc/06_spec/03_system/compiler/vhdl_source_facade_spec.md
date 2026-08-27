# Vhdl Source Facade Specification

> Tests covering VHDL Source Facade.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 40 | 40 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Vhdl Source Facade Specification

## Scenarios

### VHDL Source Facade

#### aot_vhdl_file writes a typed add design unit from minimal source

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- aot_vhdl_file writes a typed add design unit from minimal source


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("aot_vhdl_file writes a typed add design unit from minimal source")
val src_path = "/tmp/sml_vhdl_source_facade_add.spl"
val out_path = "/tmp/sml_vhdl_source_facade_add.vhd"
delete_file(src_path)
delete_file(out_path)
write_file(src_path, "fn add(a: i32, b: i32) -> i32:\n    a + b")

val result = aot_vhdl_file(src_path, out_path)
check_msg(result.is_success(), result.get_errors().join("\n"))
check_msg(rt_file_exists(out_path), "VHDL output file was not created")
val output = rt_file_read_text(out_path) ?? ""
check_msg(output.len() > 0, "VHDL output file was empty")
check_msg(output.contains("entity add is"), output)
check_msg(output.contains("a : in signed(31 downto 0);"), output)
check_msg(output.contains("b : in signed(31 downto 0);"), output)
check_msg(output.contains("result_out : out signed(31 downto 0)"), output)
check_msg(output.contains("result_out <= a + b;"), output)

delete_file(src_path)
delete_file(out_path)
```

</details>

#### aot_vhdl_file writes arithmetic with integer constants

- aot_vhdl_file writes arithmetic with integer constants


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("aot_vhdl_file writes arithmetic with integer constants")
val src_path = "/tmp/sml_vhdl_source_facade_const.spl"
val out_path = "/tmp/sml_vhdl_source_facade_const.vhd"
delete_file(src_path)
delete_file(out_path)
write_file(src_path, "fn add_five(a: i32) -> i32:\n    a + 5")

val result = aot_vhdl_file(src_path, out_path)
check_msg(result.is_success(), result.get_errors().join("\n"))
val output = rt_file_read_text(out_path) ?? ""
check_msg(output.contains("entity add_five is"), output)
check_msg(output.contains("result_out <= a + to_signed(5, 32);"), output)

delete_file(src_path)
delete_file(out_path)
```

</details>

#### aot_vhdl_file writes a boolean if expression as a result mux

- aot_vhdl_file writes a boolean if expression as a result mux


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("aot_vhdl_file writes a boolean if expression as a result mux")
val src_path = "/tmp/sml_vhdl_source_facade_if.spl"
val out_path = "/tmp/sml_vhdl_source_facade_if.vhd"
delete_file(src_path)
delete_file(out_path)
write_file(src_path, "fn choose(flag: bool, a: i32, b: i32) -> i32:\n    if flag: a else: b")

val result = aot_vhdl_file(src_path, out_path)
check_msg(result.is_success(), result.get_errors().join("\n"))
val output = rt_file_read_text(out_path) ?? ""
check_msg(output.contains("flag : in std_logic;"), output)
check_msg(output.contains("result_out <= a when flag = '1' else b;"), output)

delete_file(src_path)
delete_file(out_path)
```

</details>

#### aot_vhdl_file writes a supported source cast

- aot_vhdl_file writes a supported source cast


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("aot_vhdl_file writes a supported source cast")
val src_path = "/tmp/sml_vhdl_source_facade_cast.spl"
val out_path = "/tmp/sml_vhdl_source_facade_cast.vhd"
delete_file(src_path)
delete_file(out_path)
write_file(src_path, "fn widen(a: i32) -> i64:\n    a as i64")

val result = aot_vhdl_file(src_path, out_path)
check_msg(result.is_success(), result.get_errors().join("\n"))
val output = rt_file_read_text(out_path) ?? ""
check_msg(output.contains("result_out : out signed(63 downto 0)"), output)
check_msg(output.contains("result_out <= resize(signed(a), 64);"), output)

delete_file(src_path)
delete_file(out_path)
```

</details>

#### aot_vhdl_file writes constant arithmetic with fixed-width literals

- aot_vhdl_file writes constant arithmetic with fixed-width literals


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("aot_vhdl_file writes constant arithmetic with fixed-width literals")
val src_path = "/tmp/sml_vhdl_source_facade_consts.spl"
val out_path = "/tmp/sml_vhdl_source_facade_consts.vhd"
delete_file(src_path)
delete_file(out_path)
write_file(src_path, "fn add_consts() -> i32:\n    2 + 3")

val result = aot_vhdl_file(src_path, out_path)
check_msg(result.is_success(), result.get_errors().join("\n"))
check_msg(rt_file_exists(out_path), "VHDL output file was not created")
val output = rt_file_read_text(out_path) ?? ""
check_msg(output.contains("result_out <= to_signed(2, 32) + to_signed(3, 32);"), output)

delete_file(src_path)
delete_file(out_path)
```

</details>

#### aot_vhdl_file lowers an inline boolean if expression

- aot_vhdl_file lowers an inline boolean if expression


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("aot_vhdl_file lowers an inline boolean if expression")
val src_path = "/tmp/sml_vhdl_source_facade_if_inline.spl"
val out_path = "/tmp/sml_vhdl_source_facade_if_inline.vhd"
delete_file(src_path)
delete_file(out_path)
write_file(src_path, "fn choose(flag: bool) -> i32:\n    if flag: 1 else: 0")

val result = aot_vhdl_file(src_path, out_path)
check_msg(result.is_success(), result.get_errors().join("\n"))
check_msg(rt_file_exists(out_path), "VHDL output file was not created")
val output = rt_file_read_text(out_path) ?? ""
check_msg(output.contains("result_out <= to_signed(1, 32) when flag = '1' else to_signed(0, 32);"), output)

delete_file(src_path)
delete_file(out_path)
```

</details>

#### aot_vhdl_file lowers a block boolean if expression

- aot_vhdl_file lowers a block boolean if expression


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("aot_vhdl_file lowers a block boolean if expression")
val src_path = "/tmp/sml_vhdl_source_facade_if_block.spl"
val out_path = "/tmp/sml_vhdl_source_facade_if_block.vhd"
delete_file(src_path)
delete_file(out_path)
write_file(src_path, "fn choose_block(flag: bool) -> i32:\n    if flag:\n        1\n    else:\n        0")

val result = aot_vhdl_file(src_path, out_path)
check_msg(result.is_success(), result.get_errors().join("\n"))
check_msg(rt_file_exists(out_path), "VHDL output file was not created")
val output = rt_file_read_text(out_path) ?? ""
check_msg(output.contains("result_out <= to_signed(1, 32) when flag = '1' else to_signed(0, 32);"), output)

delete_file(src_path)
delete_file(out_path)
```

</details>

#### aot_vhdl_file lowers a clean bool to integer cast

- aot_vhdl_file lowers a clean bool to integer cast


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("aot_vhdl_file lowers a clean bool to integer cast")
val src_path = "/tmp/sml_vhdl_source_facade_cast.spl"
val out_path = "/tmp/sml_vhdl_source_facade_cast.vhd"
delete_file(src_path)
delete_file(out_path)
write_file(src_path, "fn cast_flag(flag: bool) -> i32:\n    flag as i32")

val result = aot_vhdl_file(src_path, out_path)
check_msg(result.is_success(), result.get_errors().join("\n"))
check_msg(rt_file_exists(out_path), "VHDL output file was not created")
val output = rt_file_read_text(out_path) ?? ""
check_msg(output.contains("result_out <= to_signed(1, 32) when flag = '1' else to_signed(0, 32);"), output)

delete_file(src_path)
delete_file(out_path)
```

</details>

#### aot_vhdl_file lowers integer comparisons to std_logic

- aot_vhdl_file lowers integer comparisons to std_logic


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("aot_vhdl_file lowers integer comparisons to std_logic")
val src_path = "/tmp/sml_vhdl_source_facade_compare.spl"
val out_path = "/tmp/sml_vhdl_source_facade_compare.vhd"
delete_file(src_path)
delete_file(out_path)
write_file(src_path, "fn less_than(a: i32, b: i32) -> bool:\n    a < b")

val result = aot_vhdl_file(src_path, out_path)
check_msg(result.is_success(), result.get_errors().join("\n"))
check_msg(rt_file_exists(out_path), "VHDL output file was not created")
val output = rt_file_read_text(out_path) ?? ""
check_msg(output.contains("result_out : out std_logic"), output)
check_msg(output.contains("result_out <= '1' when a < b else '0';"), output)

delete_file(src_path)
delete_file(out_path)
```

</details>

#### aot_vhdl_file lowers boolean logic expressions

- aot_vhdl_file lowers boolean logic expressions


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("aot_vhdl_file lowers boolean logic expressions")
val src_path = "/tmp/sml_vhdl_source_facade_bool_logic.spl"
val out_path = "/tmp/sml_vhdl_source_facade_bool_logic.vhd"
delete_file(src_path)
delete_file(out_path)
write_file(src_path, "fn both(a: bool, b: bool) -> bool:\n    a and b")

val result = aot_vhdl_file(src_path, out_path)
check_msg(result.is_success(), result.get_errors().join("\n"))
check_msg(rt_file_exists(out_path), "VHDL output file was not created")
val output = rt_file_read_text(out_path) ?? ""
check_msg(output.contains("a : in std_logic;"), output)
check_msg(output.contains("b : in std_logic;"), output)
check_msg(output.contains("result_out <= a and b;"), output)

delete_file(src_path)
delete_file(out_path)
```

</details>

#### aot_vhdl_file lowers hardware labeled tuple returns to output ports

- aot_vhdl_file lowers hardware labeled tuple returns to output ports


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("aot_vhdl_file lowers hardware labeled tuple returns to output ports")
val src_path = "/tmp/sml_vhdl_source_facade_full_add.spl"
val out_path = "/tmp/sml_vhdl_source_facade_full_add.vhd"
delete_file(src_path)
delete_file(out_path)
write_file(src_path, "@hardware\nfn full_add(a: bool, b: bool, cin: bool) -> (sum: bool, cout: bool):\n    return (sum: a xor b xor cin, cout: (a and b) or (a and cin) or (b and cin))")

val result = aot_vhdl_file(src_path, out_path)
check_msg(result.is_success(), result.get_errors().join("\n"))
check_msg(rt_file_exists(out_path), "VHDL output file was not created")
val output = rt_file_read_text(out_path) ?? ""
check_msg(output.contains("entity full_add is"), output)
check_msg(output.contains("sum : out std_logic;"), output)
check_msg(output.contains("cout : out std_logic"), output)
check_msg(output.contains("sum <= a xor b xor cin;"), output)
check_msg(output.contains("cout <= (a and b) or (a and cin) or (b and cin);"), output)

delete_file(src_path)
delete_file(out_path)
```

</details>

#### aot_vhdl_file lowers multi-function hardware scalar outputs

- aot_vhdl_file lowers multi-function hardware scalar outputs


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("aot_vhdl_file lowers multi-function hardware scalar outputs")
val src_path = "/tmp/sml_vhdl_source_facade_multi_scalar.spl"
val out_path = "/tmp/sml_vhdl_source_facade_multi_scalar.vhd"
delete_file(src_path)
delete_file(out_path)
write_file(src_path, "@hardware\nfn invert_gate(a: bool) -> bool:\n    not a\n\n@hardware\nfn add_one(a: i32) -> i32:\n    a + 1")

val result = aot_vhdl_file(src_path, out_path)
check_msg(result.is_success(), result.get_errors().join("\n"))
check_msg(rt_file_exists(out_path), "VHDL output file was not created")
val output = rt_file_read_text(out_path) ?? ""
check_msg(output.contains("entity invert_gate is"), output)
check_msg(output.contains("result_out : out std_logic"), output)
check_msg(output.contains("result_out <= not a;"), output)
check_msg(output.contains("entity add_one is"), output)
check_msg(output.contains("result_out : out signed(31 downto 0)"), output)
check_msg(output.contains("result_out <= a + to_signed(1, 32);"), output)

delete_file(src_path)
delete_file(out_path)
```

</details>

#### aot_vhdl_file hardware labeled tuple return passes GHDL analysis and elaboration

- aot_vhdl_file hardware labeled tuple return passes GHDL analysis and elaboration


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("aot_vhdl_file hardware labeled tuple return passes GHDL analysis and elaboration")
val src_path = "/tmp/sml_vhdl_source_facade_full_add_ghdl.spl"
val out_path = "/tmp/sml_vhdl_source_facade_full_add_ghdl.vhd"
delete_file(src_path)
delete_file(out_path)
write_file(src_path, "@hardware\nfn full_add_ghdl(a: bool, b: bool, cin: bool) -> (sum: bool, cout: bool):\n    return (sum: a xor b xor cin, cout: (a and b) or (a and cin) or (b and cin))")

val result = aot_vhdl_file(src_path, out_path)
check_msg(result.is_success(), result.get_errors().join("\n"))
check_msg(rt_file_exists(out_path), "VHDL output file was not created")

if not local_ghdl_available():
    print "SKIP: GHDL not available"
    delete_file(src_path)
    delete_file(out_path)
    return

check_msg(local_ghdl_analyze_and_elaborate(out_path, "full_add_ghdl"), "GHDL rejected hardware labeled tuple return VHDL")

delete_file(src_path)
delete_file(out_path)
```

</details>

#### aot_vhdl_file lowers anonymous hardware tuple outputs to deterministic ports

- aot_vhdl_file lowers anonymous hardware tuple outputs to deterministic ports


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("aot_vhdl_file lowers anonymous hardware tuple outputs to deterministic ports")
val src_path = "/tmp/sml_vhdl_source_facade_anonymous_output.spl"
val out_path = "/tmp/sml_vhdl_source_facade_anonymous_output.vhd"
val map_path = out_path + ".map.json"
delete_file(src_path)
delete_file(out_path)
delete_file(map_path)
write_file(src_path, "@hardware\nfn anonymous_outputs(a: bool, b: bool) -> (bool, bool):\n    return (a, b)")

val result = aot_vhdl_file(src_path, out_path)
check_msg(result.is_success(), result.get_errors().join("\n"))
check_msg(rt_file_exists(out_path), "VHDL output file was not created")
val output = rt_file_read_text(out_path) ?? ""
check_msg(output.contains("out_0 : out std_logic;"), output)
check_msg(output.contains("out_1 : out std_logic"), output)
check_msg(output.contains("out_0 <= a;"), output)
check_msg(output.contains("out_1 <= b;"), output)
if local_ghdl_available():
    check_msg(local_ghdl_analyze_and_elaborate(out_path, "anonymous_outputs"), "GHDL rejected anonymous tuple output VHDL")

delete_file(src_path)
delete_file(out_path)
delete_file(map_path)
```

</details>

#### aot_vhdl_file emits generic blocks for hardware entities

- aot_vhdl_file emits generic blocks for hardware entities


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("aot_vhdl_file emits generic blocks for hardware entities")
val src_path = "/tmp/sml_vhdl_source_facade_generic.spl"
val out_path = "/tmp/sml_vhdl_source_facade_generic.vhd"
delete_file(src_path)
delete_file(out_path)
write_file(src_path, "@hardware\n@generic(WIDTH: natural = 8)\nfn generic_passthrough(a: u8) -> u8:\n    a")

val result = aot_vhdl_file(src_path, out_path)
check_msg(result.is_success(), result.get_errors().join("\n"))
check_msg(rt_file_exists(out_path), "VHDL output file was not created")
val output = rt_file_read_text(out_path) ?? ""
check_msg(output.contains("generic ("), output)
check_msg(output.contains("WIDTH : natural := 8"), output)
check_msg(output.contains("a : in unsigned(7 downto 0);"), output)
check_msg(output.contains("result_out : out unsigned(7 downto 0)"), output)
if local_ghdl_available():
    check_msg(local_ghdl_analyze_and_elaborate(out_path, "generic_passthrough"), "GHDL rejected generic VHDL")

delete_file(src_path)
delete_file(out_path)
```

</details>

#### aot_vhdl_file emits clocked reset-aware processes

- aot_vhdl_file emits clocked reset-aware processes


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("aot_vhdl_file emits clocked reset-aware processes")
val src_path = "/tmp/sml_vhdl_source_facade_clocked.spl"
val out_path = "/tmp/sml_vhdl_source_facade_clocked.vhd"
delete_file(src_path)
delete_file(out_path)
write_file(src_path, "@hardware\n@clocked(clk, reset_n)\nfn reg1(clk: bool, reset_n: bool, d: bool) -> bool:\n    d")

val result = aot_vhdl_file(src_path, out_path)
check_msg(result.is_success(), result.get_errors().join("\n"))
check_msg(rt_file_exists(out_path), "VHDL output file was not created")
val output = rt_file_read_text(out_path) ?? ""
check_msg(output.contains("process(clk, reset_n)"), output)
check_msg(output.contains("if reset_n = '0' then"), output)
check_msg(output.contains("result_out <= '0';"), output)
check_msg(output.contains("elsif rising_edge(clk) then"), output)
check_msg(output.contains("result_out <= d;"), output)
if local_ghdl_available():
    check_msg(local_ghdl_analyze_and_elaborate(out_path, "reg1"), "GHDL rejected clocked VHDL")

delete_file(src_path)
delete_file(out_path)
```

</details>

#### aot_vhdl_file emits active-high asynchronous reset when clocked metadata requests it

- aot_vhdl_file emits active-high asynchronous reset when clocked metadata requests it


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("aot_vhdl_file emits active-high asynchronous reset when clocked metadata requests it")
val src_path = "/tmp/sml_vhdl_source_facade_clocked_active_high.spl"
val out_path = "/tmp/sml_vhdl_source_facade_clocked_active_high.vhd"
delete_file(src_path)
delete_file(out_path)
write_file(src_path, "@hardware\n@clocked(clk, reset, active_high)\nfn reg_active_high(clk: bool, reset: bool, d: bool) -> bool:\n    d")

val result = aot_vhdl_file(src_path, out_path)
check_msg(result.is_success(), result.get_errors().join("\n"))
check_msg(rt_file_exists(out_path), "VHDL output file was not created")
val output = rt_file_read_text(out_path) ?? ""
check_msg(output.contains("process(clk, reset)"), output)
check_msg(output.contains("if reset = '1' then"), output)
check_msg(output.contains("elsif rising_edge(clk) then"), output)
check_msg(output.contains("result_out <= d;"), output)
if local_ghdl_available():
    check_msg(local_ghdl_analyze_and_elaborate(out_path, "reg_active_high"), "GHDL rejected active-high reset VHDL")

delete_file(src_path)
delete_file(out_path)
```

</details>

#### aot_vhdl_file emits synchronous reset when clocked metadata requests it

- aot_vhdl_file emits synchronous reset when clocked metadata requests it


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("aot_vhdl_file emits synchronous reset when clocked metadata requests it")
val src_path = "/tmp/sml_vhdl_source_facade_clocked_sync.spl"
val out_path = "/tmp/sml_vhdl_source_facade_clocked_sync.vhd"
delete_file(src_path)
delete_file(out_path)
write_file(src_path, "@hardware\n@clocked(clk, reset_n, active_low, sync)\nfn reg_sync(clk: bool, reset_n: bool, d: bool) -> bool:\n    d")

val result = aot_vhdl_file(src_path, out_path)
check_msg(result.is_success(), result.get_errors().join("\n"))
check_msg(rt_file_exists(out_path), "VHDL output file was not created")
val output = rt_file_read_text(out_path) ?? ""
check_msg(output.contains("process(clk)"), output)
check_msg(output.contains("if rising_edge(clk) then"), output)
check_msg(output.contains("if reset_n = '0' then"), output)
check_msg(output.contains("else\n                result_out <= d;"), output)
if local_ghdl_available():
    check_msg(local_ghdl_analyze_and_elaborate(out_path, "reg_sync"), "GHDL rejected synchronous reset VHDL")

delete_file(src_path)
delete_file(out_path)
```

</details>

#### aot_vhdl_file flattens labeled tuple input ports

- aot_vhdl_file flattens labeled tuple input ports


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("aot_vhdl_file flattens labeled tuple input ports")
val src_path = "/tmp/sml_vhdl_source_facade_tuple_input.spl"
val out_path = "/tmp/sml_vhdl_source_facade_tuple_input.vhd"
delete_file(src_path)
delete_file(out_path)
write_file(src_path, "@hardware\nfn route(bus: (addr: u32, write: bool)) -> (addr: u32, we: bool):\n    return (addr: bus.addr, we: bus.write)")

val result = aot_vhdl_file(src_path, out_path)
check_msg(result.is_success(), result.get_errors().join("\n"))
check_msg(rt_file_exists(out_path), "VHDL output file was not created")
val output = rt_file_read_text(out_path) ?? ""
check_msg(output.contains("bus_addr : in unsigned(31 downto 0);"), output)
check_msg(output.contains("bus_write : in std_logic;"), output)
check_msg(output.contains("addr <= bus_addr;"), output)
check_msg(output.contains("we <= bus_write;"), output)
if local_ghdl_available():
    check_msg(local_ghdl_analyze_and_elaborate(out_path, "route"), "GHDL rejected flattened tuple input VHDL")

delete_file(src_path)
delete_file(out_path)
```

</details>

#### aot_vhdl_file rejects flattened input and output port collisions

- aot_vhdl_file rejects flattened input and output port collisions
   - Expected: result.is_success() is false
   - Expected: rt_file_exists(out_path) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("aot_vhdl_file rejects flattened input and output port collisions")
val src_path = "/tmp/sml_vhdl_source_facade_tuple_input_output_collision.spl"
val out_path = "/tmp/sml_vhdl_source_facade_tuple_input_output_collision.vhd"
delete_file(src_path)
delete_file(out_path)
write_file(src_path, "@hardware\nfn clash(bus: (data: bool)) -> (bus_data: bool):\n    return (bus_data: bus.data)")

val result = aot_vhdl_file(src_path, out_path)
expect(result.is_success()).to_equal(false)
expect(result.get_errors().join("\n")).to_contain("input/output port collision after VHDL sanitization")
expect(result.get_errors().join("\n")).to_contain("bus_data")
expect(rt_file_exists(out_path)).to_equal(false)

delete_file(src_path)
delete_file(out_path)
```

</details>

#### aot_vhdl_file lowers payload-free enum declarations in the source facade

- aot_vhdl_file lowers payload-free enum declarations in the source facade


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("aot_vhdl_file lowers payload-free enum declarations in the source facade")
val src_path = "/tmp/sml_vhdl_source_facade_enum_decl.spl"
val out_path = "/tmp/sml_vhdl_source_facade_enum_decl.vhd"
delete_file(src_path)
delete_file(out_path)
write_file(src_path, "enum State:\n    Idle\n    Busy\n\n@hardware\nfn hold_state(state: State) -> State:\n    state")

val result = aot_vhdl_file(src_path, out_path)
check_msg(result.is_success(), result.get_errors().join("\n"))
check_msg(rt_file_exists(out_path), "VHDL output file was not created")
val output = rt_file_read_text(out_path) ?? ""
check_msg(output.contains("type State_t is (Idle, Busy);"), output)
check_msg(output.contains("state : in State_t;"), output)
check_msg(output.contains("result_out : out State_t"), output)
check_msg(output.contains("result_out <= state;"), output)
if local_ghdl_available():
    check_msg(local_ghdl_analyze_and_elaborate(out_path, "hold_state"), "GHDL rejected payload-free enum VHDL")

delete_file(src_path)
delete_file(out_path)
```

</details>

#### aot_vhdl_file lowers payload enum declarations as tagged records in the source facade

- aot_vhdl_file lowers payload enum declarations as tagged records in the source facade


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("aot_vhdl_file lowers payload enum declarations as tagged records in the source facade")
val src_path = "/tmp/sml_vhdl_source_facade_payload_enum_decl.spl"
val out_path = "/tmp/sml_vhdl_source_facade_payload_enum_decl.vhd"
delete_file(src_path)
delete_file(out_path)
write_file(src_path, "enum State:\n    Idle\n    Busy(code: u8)\n\n@hardware\nfn hold_payload_state(state: State) -> State:\n    state")

val result = aot_vhdl_file(src_path, out_path)
check_msg(result.is_success(), result.get_errors().join("\n"))
check_msg(rt_file_exists(out_path), "VHDL output file was not created")
val output = rt_file_read_text(out_path) ?? ""
check_msg(output.contains("type State_t_tag_t is (Idle, Busy);"), output)
check_msg(output.contains("type State_t is record"), output)
check_msg(output.contains("tag : State_t_tag_t;"), output)
check_msg(output.contains("Busy_payload : unsigned(7 downto 0);"), output)
check_msg(output.contains("state : in State_t;"), output)
check_msg(output.contains("result_out : out State_t"), output)
check_msg(output.contains("result_out <= state;"), output)
if local_ghdl_available():
    check_msg(local_ghdl_analyze_and_elaborate(out_path, "hold_payload_state"), "GHDL rejected payload enum VHDL")

delete_file(src_path)
delete_file(out_path)
```

</details>

#### aot_vhdl_file rejects ROM RAM inference facade paths and removes stale artifacts

- aot_vhdl_file rejects ROM RAM inference facade paths and removes stale artifacts
   - Expected: result.is_success() is false
   - Expected: rt_file_exists(out_path) is false
   - Expected: rt_file_exists(map_path) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("aot_vhdl_file rejects ROM RAM inference facade paths and removes stale artifacts")
val src_path = "/tmp/sml_vhdl_source_facade_memory_decl.spl"
val out_path = "/tmp/sml_vhdl_source_facade_memory_decl.vhd"
val map_path = out_path + ".map.json"
delete_file(src_path)
delete_file(out_path)
delete_file(map_path)
write_file(src_path, "@hardware\nfn read_rom(addr: u8) -> u8:\n    val rom = [1, 2, 3, 4]\n    rom[0]")
write_file(out_path, "stale vhdl")
write_file(map_path, "stale map")

val result = aot_vhdl_file(src_path, out_path)
expect(result.is_success()).to_equal(false)
expect(result.get_errors().join("\n")).to_contain("VHDL-MEM-POLICY: ROM/RAM inference requires an explicit static ROM")
expect(rt_file_exists(out_path)).to_equal(false)
expect(rt_file_exists(map_path)).to_equal(false)

delete_file(src_path)
delete_file(out_path)
delete_file(map_path)
```

</details>

#### aot_vhdl_file rejects undeclared enum-like hardware port types

- aot_vhdl_file rejects undeclared enum-like hardware port types
   - Expected: result.is_success() is false
   - Expected: rt_file_exists(out_path) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("aot_vhdl_file rejects undeclared enum-like hardware port types")
val src_path = "/tmp/sml_vhdl_source_facade_enum_port.spl"
val out_path = "/tmp/sml_vhdl_source_facade_enum_port.vhd"
delete_file(src_path)
delete_file(out_path)
write_file(src_path, "@hardware\nfn active(state: State) -> bool:\n    true")

val result = aot_vhdl_file(src_path, out_path)
expect(result.is_success()).to_equal(false)
expect(result.get_errors().join("\n")).to_contain("VHDL backend unsupported type id")
expect(rt_file_exists(out_path)).to_equal(false)

delete_file(src_path)
delete_file(out_path)
```

</details>

#### aot_vhdl_file flattens one nested labeled tuple input bundle

- aot_vhdl_file flattens one nested labeled tuple input bundle


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("aot_vhdl_file flattens one nested labeled tuple input bundle")
val src_path = "/tmp/sml_vhdl_source_facade_nested_tuple_input.spl"
val out_path = "/tmp/sml_vhdl_source_facade_nested_tuple_input.vhd"
delete_file(src_path)
delete_file(out_path)
write_file(src_path, "@hardware\nfn route_nested(bus: (cmd: (addr: u32, valid: bool), rsp: (ready: bool))) -> (addr: u32, ok: bool):\n    return (addr: bus.cmd.addr, ok: bus.cmd.valid and bus.rsp.ready)")

val result = aot_vhdl_file(src_path, out_path)
check_msg(result.is_success(), result.get_errors().join("\n"))
check_msg(rt_file_exists(out_path), "VHDL output file was not created")
val output = rt_file_read_text(out_path) ?? ""
check_msg(output.contains("bus_cmd_addr : in unsigned(31 downto 0);"), output)
check_msg(output.contains("bus_cmd_valid : in std_logic;"), output)
check_msg(output.contains("bus_rsp_ready : in std_logic;"), output)
check_msg(output.contains("addr <= bus_cmd_addr;"), output)
check_msg(output.contains("ok <= bus_cmd_valid and bus_rsp_ready;"), output)
if local_ghdl_available():
    check_msg(local_ghdl_analyze_and_elaborate(out_path, "route_nested"), "GHDL rejected nested flattened tuple input VHDL")

delete_file(src_path)
delete_file(out_path)
```

</details>

#### aot_vhdl_file flattens named labeled tuple bundle aliases

- aot_vhdl_file flattens named labeled tuple bundle aliases


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("aot_vhdl_file flattens named labeled tuple bundle aliases")
val src_path = "/tmp/sml_vhdl_source_facade_named_bundle_alias.spl"
val out_path = "/tmp/sml_vhdl_source_facade_named_bundle_alias.vhd"
delete_file(src_path)
delete_file(out_path)
write_file(src_path, "type Bus = (addr: u32, write: bool)\ntype Routed = (addr: u32, we: bool)\n\n@hardware\nfn route_alias(bus: Bus) -> Routed:\n    return (addr: bus.addr, we: bus.write)")

val result = aot_vhdl_file(src_path, out_path)
check_msg(result.is_success(), result.get_errors().join("\n"))
check_msg(rt_file_exists(out_path), "VHDL output file was not created")
val output = rt_file_read_text(out_path) ?? ""
check_msg(output.contains("bus_addr : in unsigned(31 downto 0);"), output)
check_msg(output.contains("bus_write : in std_logic;"), output)
check_msg(output.contains("addr : out unsigned(31 downto 0);"), output)
check_msg(output.contains("we : out std_logic"), output)
check_msg(output.contains("addr <= bus_addr;"), output)
check_msg(output.contains("we <= bus_write;"), output)
if local_ghdl_available():
    check_msg(local_ghdl_analyze_and_elaborate(out_path, "route_alias"), "GHDL rejected named bundle alias VHDL")

delete_file(src_path)
delete_file(out_path)
```

</details>

#### aot_vhdl_file flattens nested bundle aliases deterministically

- aot_vhdl_file flattens nested bundle aliases deterministically


<details>
<summary>Executable SSpec</summary>

Runnable source: 27 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("aot_vhdl_file flattens nested bundle aliases deterministically")
val src_path = "/tmp/sml_vhdl_source_facade_nested_bundle_alias.spl"
val out_path = "/tmp/sml_vhdl_source_facade_nested_bundle_alias.vhd"
delete_file(src_path)
delete_file(out_path)
write_file(src_path, "type Cmd = (addr: u32, valid: bool)\ntype Rsp = (ready: bool)\ntype Bus = (cmd: Cmd, rsp: Rsp)\n\n@hardware\nfn route_alias_nested(bus: Bus) -> (addr: u32, ok: bool):\n    return (addr: bus.cmd.addr, ok: bus.cmd.valid and bus.rsp.ready)")

val result = aot_vhdl_file(src_path, out_path)
check_msg(result.is_success(), result.get_errors().join("\n"))
check_msg(rt_file_exists(out_path), "VHDL output file was not created")
val output = rt_file_read_text(out_path) ?? ""
check_msg(output.contains("bus_cmd_addr : in unsigned(31 downto 0);"), output)
check_msg(output.contains("bus_cmd_valid : in std_logic;"), output)
check_msg(output.contains("bus_rsp_ready : in std_logic;"), output)
check_msg(output.contains("addr <= bus_cmd_addr;"), output)
check_msg(output.contains("ok <= bus_cmd_valid and bus_rsp_ready;"), output)
val cmd_addr_index = output.find("bus_cmd_addr").unwrap()
val cmd_valid_index = output.find("bus_cmd_valid").unwrap()
val rsp_ready_index = output.find("bus_rsp_ready").unwrap()
check_msg(cmd_addr_index < cmd_valid_index, output)
check_msg(cmd_valid_index < rsp_ready_index, output)
if local_ghdl_available():
    check_msg(local_ghdl_analyze_and_elaborate(out_path, "route_alias_nested"), "GHDL rejected nested bundle alias VHDL")

delete_file(src_path)
delete_file(out_path)
```

</details>

#### aot_vhdl_file rejects nested bundle alias flattened port collisions

- aot_vhdl_file rejects nested bundle alias flattened port collisions
   - Expected: result.is_success() is false
   - Expected: rt_file_exists(out_path) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("aot_vhdl_file rejects nested bundle alias flattened port collisions")
val src_path = "/tmp/sml_vhdl_source_facade_nested_bundle_alias_collision.spl"
val out_path = "/tmp/sml_vhdl_source_facade_nested_bundle_alias_collision.vhd"
delete_file(src_path)
delete_file(out_path)
write_file(src_path, "type Inner = (value: bool)\ntype Bus = (inner: Inner, inner_value: bool)\n\n@hardware\nfn bad_alias(bus: Bus) -> (ok: bool):\n    return (ok: bus.inner.value)")

val result = aot_vhdl_file(src_path, out_path)
expect(result.is_success()).to_equal(false)
expect(result.get_errors().join("\n")).to_contain("duplicate input port after VHDL sanitization")
expect(result.get_errors().join("\n")).to_contain("bus_inner_value")
expect(rt_file_exists(out_path)).to_equal(false)

delete_file(src_path)
delete_file(out_path)
```

</details>

#### aot_vhdl_file supports all fixed-width integer facade port types

- aot_vhdl_file supports all fixed-width integer facade port types


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("aot_vhdl_file supports all fixed-width integer facade port types")
val src_path = "/tmp/sml_vhdl_source_facade_widths.spl"
val out_path = "/tmp/sml_vhdl_source_facade_widths.vhd"
delete_file(src_path)
delete_file(out_path)
write_file(src_path, "fn pass_u64(a: u64, b: u16) -> u64:\n    a + 1")

val result = aot_vhdl_file(src_path, out_path)
check_msg(result.is_success(), result.get_errors().join("\n"))
check_msg(rt_file_exists(out_path), "VHDL output file was not created")
val output = rt_file_read_text(out_path) ?? ""
check_msg(output.contains("a : in unsigned(63 downto 0);"), output)
check_msg(output.contains("b : in unsigned(15 downto 0);"), output)
check_msg(output.contains("result_out <= a + to_unsigned(1, 64);"), output)

delete_file(src_path)
delete_file(out_path)
```

</details>

#### aot_vhdl_file rejects implicit-width integer facade ports before VHDL output

- aot_vhdl_file rejects implicit-width integer facade ports before VHDL output
   - Expected: result.is_success() is false
   - Expected: rt_file_exists(out_path) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("aot_vhdl_file rejects implicit-width integer facade ports before VHDL output")
val src_path = "/tmp/sml_vhdl_source_facade_implicit_int_port.spl"
val out_path = "/tmp/sml_vhdl_source_facade_implicit_int_port.vhd"
delete_file(src_path)
delete_file(out_path)
write_file(src_path, "fn passthrough(a: int) -> u8:\n    0")

val result = aot_vhdl_file(src_path, out_path)
expect(result.is_success()).to_equal(false)
expect(result.get_errors().join("\n")).to_contain("unsupported implicit-width integer type `int`")
expect(result.get_errors().join("\n")).to_contain("source facade parameter `a` type `int`")
expect(rt_file_exists(out_path)).to_equal(false)

delete_file(src_path)
delete_file(out_path)
```

</details>

#### aot_vhdl_file rejects implicit-width tuple fields before VHDL output

- aot_vhdl_file rejects implicit-width tuple fields before VHDL output
   - Expected: result.is_success() is false
   - Expected: rt_file_exists(out_path) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("aot_vhdl_file rejects implicit-width tuple fields before VHDL output")
val src_path = "/tmp/sml_vhdl_source_facade_implicit_tuple_field.spl"
val out_path = "/tmp/sml_vhdl_source_facade_implicit_tuple_field.vhd"
delete_file(src_path)
delete_file(out_path)
write_file(src_path, "@hardware\nfn bad_bundle(bus: (addr: uint, valid: bool)) -> (valid: bool):\n    return (valid: bus.valid)")

val result = aot_vhdl_file(src_path, out_path)
expect(result.is_success()).to_equal(false)
expect(result.get_errors().join("\n")).to_contain("unsupported implicit-width integer type `uint`")
expect(result.get_errors().join("\n")).to_contain("tuple field `bus.addr` type `uint`")
expect(rt_file_exists(out_path)).to_equal(false)

delete_file(src_path)
delete_file(out_path)
```

</details>

#### aot_vhdl_file rejects implicit-width cast targets before VHDL output

- aot_vhdl_file rejects implicit-width cast targets before VHDL output
   - Expected: result.is_success() is false
   - Expected: rt_file_exists(out_path) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("aot_vhdl_file rejects implicit-width cast targets before VHDL output")
val src_path = "/tmp/sml_vhdl_source_facade_implicit_cast.spl"
val out_path = "/tmp/sml_vhdl_source_facade_implicit_cast.vhd"
delete_file(src_path)
delete_file(out_path)
write_file(src_path, "fn bad_cast(a: u8) -> u8:\n    a as uint")

val result = aot_vhdl_file(src_path, out_path)
expect(result.is_success()).to_equal(false)
expect(result.get_errors().join("\n")).to_contain("unsupported implicit-width integer type `uint`")
expect(result.get_errors().join("\n")).to_contain("cast target type `uint`")
expect(rt_file_exists(out_path)).to_equal(false)

delete_file(src_path)
delete_file(out_path)
```

</details>

#### aot_vhdl_file lowers conservative integer operators

- aot_vhdl_file lowers conservative integer operators


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("aot_vhdl_file lowers conservative integer operators")
val src_path = "/tmp/sml_vhdl_source_facade_integer_ops.spl"
val out_path = "/tmp/sml_vhdl_source_facade_integer_ops.vhd"
delete_file(src_path)
delete_file(out_path)
write_file(src_path, "fn mask(a: u32, b: u32) -> u32:\n    a & b")

val result = aot_vhdl_file(src_path, out_path)
check_msg(result.is_success(), result.get_errors().join("\n"))
check_msg(rt_file_exists(out_path), "VHDL output file was not created")
val output = rt_file_read_text(out_path) ?? ""
check_msg(output.contains("result_out <= a and b;"), output)

delete_file(src_path)
delete_file(out_path)
```

</details>

#### aot_vhdl_file lowers literal shifts

- aot_vhdl_file lowers literal shifts


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("aot_vhdl_file lowers literal shifts")
val src_path = "/tmp/sml_vhdl_source_facade_shift.spl"
val out_path = "/tmp/sml_vhdl_source_facade_shift.vhd"
delete_file(src_path)
delete_file(out_path)
write_file(src_path, "fn shl(a: u32) -> u32:\n    a << 2")

val result = aot_vhdl_file(src_path, out_path)
check_msg(result.is_success(), result.get_errors().join("\n"))
check_msg(rt_file_exists(out_path), "VHDL output file was not created")
val output = rt_file_read_text(out_path) ?? ""
check_msg(output.contains("result_out <= shift_left(a, 2);"), output)

delete_file(src_path)
delete_file(out_path)
```

</details>

#### aot_vhdl_file lowers single-level fixed-width bit slices

- aot_vhdl_file lowers single-level fixed-width bit slices


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("aot_vhdl_file lowers single-level fixed-width bit slices")
val src_path = "/tmp/sml_vhdl_source_facade_slice.spl"
val out_path = "/tmp/sml_vhdl_source_facade_slice.vhd"
delete_file(src_path)
delete_file(out_path)
write_file(src_path, "fn high_byte(a: u16) -> u8:\n    a[15:8]")

val result = aot_vhdl_file(src_path, out_path)
check_msg(result.is_success(), result.get_errors().join("\n"))
check_msg(rt_file_exists(out_path), "VHDL output file was not created")
val output = rt_file_read_text(out_path) ?? ""
check_msg(output.contains("a : in unsigned(15 downto 0);"), output)
check_msg(output.contains("result_out : out unsigned(7 downto 0)"), output)
check_msg(output.contains("result_out <= a(15 downto 8);"), output)
if local_ghdl_available():
    check_msg(local_ghdl_analyze_and_elaborate(out_path, "high_byte"), "GHDL rejected bit-slice VHDL")

delete_file(src_path)
delete_file(out_path)
```

</details>

#### aot_vhdl_file lowers explicit fixed-width concat calls

- aot_vhdl_file lowers explicit fixed-width concat calls


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("aot_vhdl_file lowers explicit fixed-width concat calls")
val src_path = "/tmp/sml_vhdl_source_facade_concat.spl"
val out_path = "/tmp/sml_vhdl_source_facade_concat.vhd"
delete_file(src_path)
delete_file(out_path)
write_file(src_path, "fn join_bytes(hi: u8, lo: u8) -> u16:\n    concat(hi, lo)")

val result = aot_vhdl_file(src_path, out_path)
check_msg(result.is_success(), result.get_errors().join("\n"))
check_msg(rt_file_exists(out_path), "VHDL output file was not created")
val output = rt_file_read_text(out_path) ?? ""
check_msg(output.contains("hi : in unsigned(7 downto 0);"), output)
check_msg(output.contains("lo : in unsigned(7 downto 0);"), output)
check_msg(output.contains("result_out : out unsigned(15 downto 0)"), output)
check_msg(output.contains("result_out <= hi & lo;"), output)
if local_ghdl_available():
    check_msg(local_ghdl_analyze_and_elaborate(out_path, "join_bytes"), "GHDL rejected concat VHDL")

delete_file(src_path)
delete_file(out_path)
```

</details>

#### aot_vhdl_file rejects fixed-width bit slices with mismatched result width

- aot_vhdl_file rejects fixed-width bit slices with mismatched result width


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("aot_vhdl_file rejects fixed-width bit slices with mismatched result width")
val src_path = "/tmp/sml_vhdl_source_facade_slice_error.spl"
val out_path = "/tmp/sml_vhdl_source_facade_slice_error.vhd"
delete_file(src_path)
delete_file(out_path)
write_file(src_path, "fn bad_slice(a: u16) -> u16:\n    a[15:8]")

val result = aot_vhdl_file(src_path, out_path)
check_msg(not result.is_success(), "expected bit-slice width mismatch to fail")
check_msg(result.get_errors().join("\n").contains("bit slice width does not match result type"), result.get_errors().join("\n"))

delete_file(src_path)
delete_file(out_path)
```

</details>

#### aot_vhdl_file lowers unary operators

- aot_vhdl_file lowers unary operators


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("aot_vhdl_file lowers unary operators")
val src_path = "/tmp/sml_vhdl_source_facade_unary.spl"
val out_path = "/tmp/sml_vhdl_source_facade_unary.vhd"
delete_file(src_path)
delete_file(out_path)
write_file(src_path, "fn invert(flag: bool) -> bool:\n    not flag")

val result = aot_vhdl_file(src_path, out_path)
check_msg(result.is_success(), result.get_errors().join("\n"))
check_msg(rt_file_exists(out_path), "VHDL output file was not created")
val output = rt_file_read_text(out_path) ?? ""
check_msg(output.contains("result_out <= not flag;"), output)

delete_file(src_path)
delete_file(out_path)
```

</details>

#### aot_vhdl_file generated VHDL passes GHDL analysis and elaboration

- aot_vhdl_file generated VHDL passes GHDL analysis and elaboration


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("aot_vhdl_file generated VHDL passes GHDL analysis and elaboration")
val src_path = "/tmp/sml_vhdl_source_facade_ghdl.spl"
val out_path = "/tmp/sml_vhdl_source_facade_ghdl.vhd"
delete_file(src_path)
delete_file(out_path)
write_file(src_path, "fn add(a: i32, b: i32) -> i32:\n    a + b")

val result = aot_vhdl_file(src_path, out_path)
check_msg(result.is_success(), result.get_errors().join("\n"))
check_msg(rt_file_exists(out_path), "VHDL output file was not created")

if not local_ghdl_available():
    print "SKIP: GHDL not available"
    delete_file(src_path)
    delete_file(out_path)
    return

check_msg(local_ghdl_analyze_and_elaborate(out_path, "add"), "GHDL rejected source-facade generated add VHDL")

delete_file(src_path)
delete_file(out_path)
```

</details>

#### aot_vhdl_file writes deterministic source map sidecar

- aot_vhdl_file writes deterministic source map sidecar


<details>
<summary>Executable SSpec</summary>

Runnable source: 37 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("aot_vhdl_file writes deterministic source map sidecar")
val src_path = "/tmp/sml_vhdl_source_facade_map.spl"
val out_path = "/tmp/sml_vhdl_source_facade_map.vhd"
val map_path = out_path + ".map.json"
delete_file(src_path)
delete_file(out_path)
delete_file(map_path)
write_file(src_path, "@hardware\nfn mapped(bus: (addr: u8, write: bool)) -> (addr: u8, we: bool):\n    return (addr: bus.addr, we: bus.write)")

val result = aot_vhdl_file(src_path, out_path)
check_msg(result.is_success(), result.get_errors().join("\n"))
check_msg(rt_file_exists(out_path), "VHDL output file was not created")
check_msg(rt_file_exists(map_path), "VHDL source map sidecar was not created")
val map = rt_file_read_text(map_path) ?? ""
check_msg(map.contains("\"version\": 1"), map)
check_msg(map.contains("\"source\": \"" + src_path + "\""), map)
check_msg(map.contains("\"generated\": \"" + out_path + "\""), map)
check_msg(map.contains("\"name\":\"mapped\""), map)
check_msg(map.contains("\"name\":\"mapped\",\"line\":5,\"sourceLine\":2"), map)
check_msg(map.contains("\"name\":\"bus_addr\",\"originalName\":\"bus.addr\",\"sanitizedName\":\"bus_addr\""), map)
check_msg(map.contains("\"name\":\"bus_write\",\"originalName\":\"bus.write\",\"sanitizedName\":\"bus_write\""), map)
check_msg(map.contains("\"name\":\"addr\",\"originalName\":\"addr\",\"sanitizedName\":\"addr\""), map)
check_msg(map.contains("\"name\":\"we\",\"originalName\":\"we\",\"sanitizedName\":\"we\""), map)
check_msg(map.contains("\"sourceLine\":2"), map)
check_msg(map.contains("\"ports\": [{\"name\":\"bus_addr\""), map)
val bus_addr_index = map.find("\"name\":\"bus_addr\"").unwrap()
val bus_write_index = map.find("\"name\":\"bus_write\"").unwrap()
val addr_index = map.find("\"name\":\"addr\"").unwrap()
val we_index = map.find("\"name\":\"we\"").unwrap()
check_msg(bus_addr_index < bus_write_index, map)
check_msg(bus_write_index < addr_index, map)
check_msg(addr_index < we_index, map)

delete_file(src_path)
delete_file(out_path)
delete_file(map_path)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/03_system/compiler/vhdl_source_facade_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering VHDL Source Facade.
- VHDL Source Facade

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 40 |
| Active scenarios | 40 |
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

- Canonical SPipe generation for source `430eaf2c0c02d7d3257d9904f0348fc31a276df46fc33a4fc65f6727d1bcc5c4`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `430eaf2c0c02d7d3257d9904f0348fc31a276df46fc33a4fc65f6727d1bcc5c4`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `430eaf2c0c02d7d3257d9904f0348fc31a276df46fc33a4fc65f6727d1bcc5c4`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/compiler/vhdl_source_facade_spec.spl
mirror: doc/06_spec/03_system/compiler/vhdl_source_facade_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/compiler/vhdl_source_facade_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/compiler/vhdl_source_facade_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/compiler/vhdl_source_facade_spec.spl:44:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'aot_vhdl_file writes a typed add design unit from minimal source' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/compiler/vhdl_source_facade_spec.spl:67:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'aot_vhdl_file writes arithmetic with integer constants' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/compiler/vhdl_source_facade_spec.spl:85:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'aot_vhdl_file writes a boolean if expression as a result mux' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

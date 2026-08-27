# Pure Simple Vhdl Source Of Truth Specification

> 1. delete file

<!-- sdn-diagram:id=pure_simple_vhdl_source_of_truth_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=pure_simple_vhdl_source_of_truth_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

pure_simple_vhdl_source_of_truth_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=pure_simple_vhdl_source_of_truth_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 24 | 24 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Pure Simple Vhdl Source Of Truth Specification

## Scenarios

### pure Simple VHDL source-of-truth metadata

#### preserves @hardware metadata through pure Simple AST HIR and MIR

1. delete file
2. delete file
3. write file
4. check msg
5. check msg
6. check msg
7. check msg
8. check msg
9. delete file
10. delete file


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Fixture: @hardware full_add.
# Expected: the pure Simple compiler selects it as a VHDL entity without
# reparsing raw source text or relying on the Rust MIR backend.
val src_path = "/tmp/sml_pure_vhdl_full_add.spl"
val out_path = "/tmp/sml_pure_vhdl_full_add.vhd"
delete_file(src_path)
delete_file(out_path)
write_file(src_path, "@hardware\nfn full_add(a: i32, b: i32) -> i32:\n    a + b\n")

val output = compile_pure_vhdl(src_path, out_path)
check_msg(output.contains("entity full_add is"), output)
check_msg(output.contains("a : in signed(31 downto 0);"), output)
check_msg(output.contains("b : in signed(31 downto 0);"), output)
check_msg(output.contains("result_out : out signed(31 downto 0)"), output)
check_msg(output.contains("result_out <= tmp_"), output)

delete_file(src_path)
delete_file(out_path)
```

</details>

#### preserves @generic metadata as structured VHDL generic declarations

1. delete file
2. delete file
3. write file
4. check msg
5. check msg
6. check msg
7. check msg
8. delete file
9. delete file


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src_path = "/tmp/sml_pure_vhdl_generic_metadata.spl"
val out_path = "/tmp/sml_pure_vhdl_generic_metadata.vhd"
delete_file(src_path)
delete_file(out_path)
write_file(src_path, "@generic(WIDTH = 8)\n@hardware\nfn passthru(a: u8) -> u8:\n    a\n")

val output = compile_pure_vhdl(src_path, out_path)
check_msg(output.contains("generic ("), output)
check_msg(output.contains("WIDTH : natural := 8"), output)
check_msg(output.contains("a : in unsigned(7 downto 0);"), output)
check_msg(output.contains("result_out : out unsigned(7 downto 0)"), output)

delete_file(src_path)
delete_file(out_path)
```

</details>

#### preserves @clocked reset-domain metadata as structured process metadata

1. delete file
2. delete file
3. write file
4. check msg
5. check msg
6. check msg
7. check msg
8. check msg
9. delete file
10. delete file


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src_path = "/tmp/sml_pure_vhdl_clocked_metadata.spl"
val out_path = "/tmp/sml_pure_vhdl_clocked_metadata.vhd"
delete_file(src_path)
delete_file(out_path)
write_file(src_path, "@clocked(clk, reset_n, active_low, sync)\n@hardware\nfn reg1(a: u8) -> u8:\n    a\n")

val output = compile_pure_vhdl(src_path, out_path)
check_msg(output.contains("clk : in std_logic;"), output)
check_msg(output.contains("reset_n : in std_logic;"), output)
check_msg(output.contains("p_clk: process(clk)"), output)
check_msg(output.contains("if reset_n = '0' then"), output)
check_msg(output.contains("elsif rising_edge(clk)") == false, output)

delete_file(src_path)
delete_file(out_path)
```

</details>

#### preserves labeled tuple return field names through pure Simple MIR

1. delete file
2. delete file
3. write file
4. check msg
5. check msg
6. check msg
7. check msg
8. delete file
9. delete file


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Fixture: @hardware full_add returns (sum: bool, cout: bool).
# Expected: pure Simple VHDL lowering can inspect labels from IR/type
# metadata, not from the original source line.
val src_path = "/tmp/sml_pure_vhdl_labeled_tuple_names.spl"
val out_path = "/tmp/sml_pure_vhdl_labeled_tuple_names.vhd"
delete_file(src_path)
delete_file(out_path)
write_file(src_path, "@hardware\nfn full_add(a: bool, b: bool) -> (sum: bool, cout: bool):\n    (sum: a, cout: b)\n")

val output = compile_pure_vhdl(src_path, out_path)
check_msg(output.contains("sum : out std_logic;"), output)
check_msg(output.contains("cout : out std_logic"), output)
check_msg(output.contains("sum <= a;"), output)
check_msg(output.contains("cout <= b;"), output)

delete_file(src_path)
delete_file(out_path)
```

</details>

### pure Simple VHDL return ABI and diagnostics

#### emits labeled tuple return fields as VHDL output ports

1. delete file
2. delete file
3. write file
4. check msg
5. check msg
   - Expected: output does not contain `result_out`
6. check msg
7. check msg
8. delete file
9. delete file


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Expected: sum/cout are out ports, result_out is absent, and each field
# has its own assignment.
val src_path = "/tmp/sml_pure_vhdl_tuple_outputs.spl"
val out_path = "/tmp/sml_pure_vhdl_tuple_outputs.vhd"
delete_file(src_path)
delete_file(out_path)
write_file(src_path, "@hardware\nfn flags(a: bool, b: bool) -> (left: bool, right: bool):\n    (left: a, right: b)\n")

val output = compile_pure_vhdl(src_path, out_path)
check_msg(output.contains("left : out std_logic;"), output)
check_msg(output.contains("right : out std_logic"), output)
expect(output.contains("result_out")).to_equal(false)
check_msg(output.contains("left <= a;"), output)
check_msg(output.contains("right <= b;"), output)

delete_file(src_path)
delete_file(out_path)
```

</details>

#### accepts same-type labeled output ports

1. delete file
2. delete file
3. write file
4. check msg
5. check msg
6. delete file
7. delete file


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Fixture: @hardware fn flags() -> (left: bool, right: bool).
# Expected: same-type outputs are legal when labels define the ABI.
val src_path = "/tmp/sml_pure_vhdl_same_type_labeled.spl"
val out_path = "/tmp/sml_pure_vhdl_same_type_labeled.vhd"
delete_file(src_path)
delete_file(out_path)
write_file(src_path, "@hardware\nfn flags(a: bool, b: bool) -> (left: bool, right: bool):\n    (left: a, right: b)\n")

val output = compile_pure_vhdl(src_path, out_path)
check_msg(output.contains("left : out std_logic;"), output)
check_msg(output.contains("right : out std_logic"), output)

delete_file(src_path)
delete_file(out_path)
```

</details>

#### emits same-type anonymous hardware outputs with deterministic public ports

1. delete file
2. delete file
3. write file
4. check msg
5. check msg
6. check msg
7. check msg
8. delete file
9. delete file


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Fixture: @hardware fn bad() -> (bool, bool).
# Expected: deterministic out_0/out_1 VHDL output ports and assignments.
val src_path = "/tmp/sml_pure_vhdl_same_type_anonymous.spl"
val out_path = "/tmp/sml_pure_vhdl_same_type_anonymous.vhd"
delete_file(src_path)
delete_file(out_path)
write_file(src_path, "@hardware\nfn flags(a: bool, b: bool) -> (bool, bool):\n    (a, b)\n")

val output = compile_pure_vhdl(src_path, out_path)
check_msg(output.contains("out0 : out std_logic;"), output)
check_msg(output.contains("out1 : out std_logic"), output)
check_msg(output.contains("out0 <= a;"), output)
check_msg(output.contains("out1 <= b;"), output)

delete_file(src_path)
delete_file(out_path)
```

</details>

#### rejects duplicate sanitized pure Simple VHDL port names

1. delete file
2. delete file
3. write file
4. check msg
5. check msg
6. delete file
7. delete file


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Expected: input/output and output/output collisions report both source
# names and the sanitized VHDL name.
val src_path = "/tmp/sml_pure_vhdl_port_collision.spl"
val out_path = "/tmp/sml_pure_vhdl_port_collision.vhd"
delete_file(src_path)
delete_file(out_path)
write_file(src_path, "@hardware\nfn collide(carry_out: bool) -> (carry_out: bool):\n    (carry_out: carry_out)\n")

val diagnostic = compile_pure_vhdl_error(src_path, out_path)
check_msg(diagnostic.contains("VHDL identifier collision after sanitization"), diagnostic)
check_msg(diagnostic.contains("carry_out"), diagnostic)

delete_file(src_path)
delete_file(out_path)
```

</details>

### pure Simple VHDL hardware calls

#### lowers selected pure combinational helpers as explicit hardware entities

1. delete file
2. delete file
3. write file
4. check msg
5. check msg
6. check msg
7. check msg
8. check msg
9. check msg
10. check msg
11. delete file
12. delete file


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Selected helper subset: pure combinational helpers must be explicit
# @hardware entities. Broad HLS inference for ordinary functions remains
# a hard diagnostic covered below.
val src_path = "/tmp/sml_pure_vhdl_explicit_helper.spl"
val out_path = "/tmp/sml_pure_vhdl_explicit_helper.vhd"
delete_file(src_path)
delete_file(out_path)
write_file(src_path, "@hardware\nfn add_one(a: u32) -> u32:\n    a + 1\n\n@hardware\nfn top(a: u32) -> u32:\n    add_one(a)\n")

val output = compile_pure_vhdl(src_path, out_path)
check_msg(output.contains("entity add_one is"), output)
check_msg(output.contains("entity top is"), output)
check_msg(output.contains("u_add_one_0: entity work.add_one"), output)
check_msg(output.contains("a => a,"), output)
check_msg(output.contains("result_out => u_add_one_0_result_out"), output)
check_msg(output.contains("result_out <= u_add_one_0_result_out;"), output)
if local_ghdl_available():
    check_msg(local_ghdl_analyze_and_elaborate(out_path, "top"), "GHDL rejected explicit helper VHDL")

delete_file(src_path)
delete_file(out_path)
```

</details>

#### lowers direct hardware calls to deterministic named entity instances

1. delete file
2. delete file
3. write file
4. check msg
5. check msg
6. delete file
7. delete file


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Fixture: add2 calls full_add twice.
# Expected: u_full_add_0/u_full_add_1 entity instances are emitted in
# stable source order.
val src_path = "/tmp/sml_pure_vhdl_call_instances.spl"
val out_path = "/tmp/sml_pure_vhdl_call_instances.vhd"
delete_file(src_path)
delete_file(out_path)
write_file(src_path, "@hardware\nfn flags(a: bool, b: bool) -> (left: bool, right: bool):\n    (left: a, right: b)\n\n@hardware\nfn top(a: bool, b: bool) -> bool:\n    val lo = flags(a, b)\n    lo.left\n")

val output = compile_pure_vhdl(src_path, out_path)
check_msg(output.contains("u_flags_0: entity work.flags"), output)
check_msg(output.contains("result_out <= u_flags_0_left;"), output)

delete_file(src_path)
delete_file(out_path)
```

</details>

#### emits named port map connections for caller and callee ports

1. delete file
2. delete file
3. write file
4. check msg
5. check msg
6. check msg
7. check msg
8. delete file
9. delete file


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Expected: every input and output is connected by sanitized VHDL port
# name; positional port maps are not used.
val src_path = "/tmp/sml_pure_vhdl_named_port_map.spl"
val out_path = "/tmp/sml_pure_vhdl_named_port_map.vhd"
delete_file(src_path)
delete_file(out_path)
write_file(src_path, "@hardware\nfn flags(a: bool, b: bool) -> (left: bool, right: bool):\n    (left: a, right: b)\n\n@hardware\nfn top(a: bool, b: bool) -> bool:\n    val lo = flags(a, b)\n    lo.right\n")

val output = compile_pure_vhdl(src_path, out_path)
check_msg(output.contains("a => a,"), output)
check_msg(output.contains("b => b,"), output)
check_msg(output.contains("left => u_flags_0_left,"), output)
check_msg(output.contains("right => u_flags_0_right"), output)

delete_file(src_path)
delete_file(out_path)
```

</details>

#### allocates deterministic temp signals for multi-output hardware calls

1. delete file
2. delete file
3. write file
4. check msg
5. check msg
6. delete file
7. delete file


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Expected: repeated pure Simple compilations produce byte-stable signal
# names for full_add_0_sum/full_add_0_cout and later instances.
val src_path = "/tmp/sml_pure_vhdl_temp_signals.spl"
val out_path = "/tmp/sml_pure_vhdl_temp_signals.vhd"
delete_file(src_path)
delete_file(out_path)
write_file(src_path, "@hardware\nfn flags(a: bool, b: bool) -> (left: bool, right: bool):\n    (left: a, right: b)\n\n@hardware\nfn top(a: bool, b: bool) -> bool:\n    val lo = flags(a, b)\n    lo.left\n")

val output = compile_pure_vhdl(src_path, out_path)
check_msg(output.contains("signal u_flags_0_left : std_logic;"), output)
check_msg(output.contains("signal u_flags_0_right : std_logic;"), output)

delete_file(src_path)
delete_file(out_path)
```

</details>

#### resolves labeled field access over hardware call results

1. delete file
2. delete file
3. write file
4. check msg
5. delete file
6. delete file


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Fixture: lo.sum, lo.cout, lo.0, and lo.1.
# Expected: labeled access lowers to temp signals; numeric access works
# but emits the common labeled-tuple numeric-access warning.
val src_path = "/tmp/sml_pure_vhdl_field_access.spl"
val out_path = "/tmp/sml_pure_vhdl_field_access.vhd"
delete_file(src_path)
delete_file(out_path)
write_file(src_path, "@hardware\nfn flags(a: bool, b: bool) -> (left: bool, right: bool):\n    (left: a, right: b)\n\n@hardware\nfn top(a: bool, b: bool) -> bool:\n    val lo = flags(a, b)\n    lo.right\n")

val output = compile_pure_vhdl(src_path, out_path)
check_msg(output.contains("result_out <= u_flags_0_right;"), output)

delete_file(src_path)
delete_file(out_path)
```

</details>

#### rejects dynamic runtime tuple access during pure Simple VHDL lowering

1. delete file
2. delete file
3. write file
4. check msg
5. check msg
6. delete file
7. delete file


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Fixture: lo[index] where index is not a compile-time constant.
# Expected: hard diagnostic before VHDL emission.
val src_path = "/tmp/sml_pure_vhdl_dynamic_tuple_access.spl"
val out_path = "/tmp/sml_pure_vhdl_dynamic_tuple_access.vhd"
delete_file(src_path)
delete_file(out_path)
write_file(src_path, "@hardware\nfn flags(a: bool, b: bool) -> (left: bool, right: bool):\n    (left: a, right: b)\n\n@hardware\nfn top(a: bool, b: bool, index: i32) -> bool:\n    val lo = flags(a, b)\n    lo[index]\n")

val diagnostic = compile_pure_vhdl_error(src_path, out_path)
check_msg(diagnostic.contains("unsupported") or diagnostic.contains("dynamic"), diagnostic)
check_msg(diagnostic.contains("VHDL"), diagnostic)

delete_file(src_path)
delete_file(out_path)
```

</details>

#### rejects broad HLS helper inference outside explicit hardware helpers

1. delete file
2. delete file
3. write file
4. check msg
5. check msg
6. check msg
7. delete file
8. delete file


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Fixture: top calls an ordinary pure helper.
# Expected: no inferred helper subprogram is emitted; the compiler fails
# before VHDL output so the unsupported ownership boundary stays visible.
val src_path = "/tmp/sml_pure_vhdl_unannotated_helper.spl"
val out_path = "/tmp/sml_pure_vhdl_unannotated_helper.vhd"
delete_file(src_path)
delete_file(out_path)
write_file(src_path, "fn clamp_flag(a: u32, b: u32) -> bool:\n    (a + 1) > b\n\n@hardware\nfn top(a: u32, b: u32) -> bool:\n    clamp_flag(a, b)\n")

val output = compile_pure_vhdl_fails(src_path, out_path)
check_msg(output.contains("non-hardware direct call"), output)
check_msg(output.contains("clamp_flag"), output)
check_msg(output.contains("@hardware entity calls"), output)

delete_file(src_path)
delete_file(out_path)
```

</details>

### pure Simple VHDL fixed-width and domains

#### lowers typed integer comparisons from pure Simple IR

1. delete file
2. delete file
3. write file
4. check msg
5. check msg
6. delete file
7. delete file


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src_path = "/tmp/sml_pure_vhdl_compare.spl"
val out_path = "/tmp/sml_pure_vhdl_compare.vhd"
delete_file(src_path)
delete_file(out_path)
write_file(src_path, "@hardware\nfn less_than(a: i32, b: i32) -> bool:\n    a < b\n")

val output = compile_pure_vhdl(src_path, out_path)
check_msg(output.contains("result_out : out std_logic"), output)
check_msg(output.contains("when a < b else"), output)

delete_file(src_path)
delete_file(out_path)
```

</details>

#### lowers unsigned fixed-width literal shifts from typed IR

1. delete file
2. delete file
3. write file
4. check msg
5. check msg
6. check msg
7. delete file
8. delete file


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src_path = "/tmp/sml_pure_vhdl_shift.spl"
val out_path = "/tmp/sml_pure_vhdl_shift.vhd"
delete_file(src_path)
delete_file(out_path)
write_file(src_path, "@hardware\nfn shl(a: u32) -> u32:\n    a << 2\n")

val output = compile_pure_vhdl(src_path, out_path)
check_msg(output.contains("a : in unsigned(31 downto 0);"), output)
check_msg(output.contains("result_out : out unsigned(31 downto 0)"), output)
check_msg(output.contains("shift_left(a, 2)"), output)

delete_file(src_path)
delete_file(out_path)
```

</details>

#### lowers fixed-width slices and concat from typed IR

1. delete file
2. delete file
3. write file
4. check msg
5. check msg
6. check msg
7. check msg
8. delete file
9. delete file
10. write file
11. check msg
12. check msg
13. check msg
14. check msg
15. check msg
16. delete file
17. delete file
18. delete file
19. delete file


<details>
<summary>Executable SSpec</summary>

Runnable source: 33 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Expected: no facade string parsing; widths, signedness, and conversions
# are validated by pure Simple type/IR metadata.
val slice_src = "/tmp/sml_pure_vhdl_slice.spl"
val slice_out = "/tmp/sml_pure_vhdl_slice.vhd"
delete_file(slice_src)
delete_file(slice_out)
write_file(slice_src, "@hardware\nfn high_byte(a: u16) -> u8:\n    a[15:8]\n")

val slice_output = compile_pure_vhdl(slice_src, slice_out)
check_msg(slice_output.contains("a : in unsigned(15 downto 0);"), slice_output)
check_msg(slice_output.contains("result_out : out unsigned(7 downto 0)"), slice_output)
check_msg(slice_output.contains("result_out <= a(15 downto 8);"), slice_output)
if local_ghdl_available():
    check_msg(local_ghdl_analyze_and_elaborate(slice_out, "high_byte"), "GHDL rejected pure bit-slice VHDL")

val concat_src = "/tmp/sml_pure_vhdl_concat.spl"
val concat_out = "/tmp/sml_pure_vhdl_concat.vhd"
delete_file(concat_src)
delete_file(concat_out)
write_file(concat_src, "@hardware\nfn join_bytes(hi: u8, lo: u8) -> u16:\n    concat(hi, lo)\n")

val concat_output = compile_pure_vhdl(concat_src, concat_out)
check_msg(concat_output.contains("hi : in unsigned(7 downto 0);"), concat_output)
check_msg(concat_output.contains("lo : in unsigned(7 downto 0);"), concat_output)
check_msg(concat_output.contains("result_out : out unsigned(15 downto 0)"), concat_output)
check_msg(concat_output.contains("result_out <= hi & lo;"), concat_output)
if local_ghdl_available():
    check_msg(local_ghdl_analyze_and_elaborate(concat_out, "join_bytes"), "GHDL rejected pure concat VHDL")

delete_file(slice_src)
delete_file(slice_out)
delete_file(concat_src)
delete_file(concat_out)
```

</details>

#### lowers named clock domains with reset polarity synchrony and no-reset forms

1. delete file
2. delete file
3. delete file
4. delete file
5. delete file
6. delete file
7. write file
8. check msg
9. check msg
10. write file
11. check msg
12. check msg
13. check msg
14. write file
15. check msg
16. check msg
17. check msg
18. delete file
19. delete file
20. delete file
21. delete file
22. delete file
23. delete file


<details>
<summary>Executable SSpec</summary>

Runnable source: 36 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sync_src = "/tmp/sml_pure_vhdl_domain_sync.spl"
val sync_out = "/tmp/sml_pure_vhdl_domain_sync.vhd"
val async_src = "/tmp/sml_pure_vhdl_domain_async.spl"
val async_out = "/tmp/sml_pure_vhdl_domain_async.vhd"
val no_reset_src = "/tmp/sml_pure_vhdl_domain_no_reset.spl"
val no_reset_out = "/tmp/sml_pure_vhdl_domain_no_reset.vhd"
delete_file(sync_src)
delete_file(sync_out)
delete_file(async_src)
delete_file(async_out)
delete_file(no_reset_src)
delete_file(no_reset_out)

write_file(sync_src, "@clocked(clk_fast, reset_n, active_low, sync, domain_fast)\n@hardware\nfn sync_reg(a: u8) -> u8:\n    a\n")
val sync_output = compile_pure_vhdl(sync_src, sync_out)
check_msg(sync_output.contains("p_fast: process(clk_fast)"), sync_output)
check_msg(sync_output.contains("if reset_n = '0' then"), sync_output)

write_file(async_src, "@clocked(clk_io, rst, active_high, async, domain_io)\n@hardware\nfn async_reg(a: u8) -> u8:\n    a\n")
val async_output = compile_pure_vhdl(async_src, async_out)
check_msg(async_output.contains("p_io: process(clk_io, rst)"), async_output)
check_msg(async_output.contains("if rst = '1' then"), async_output)
check_msg(async_output.contains("elsif rising_edge(clk_io) then"), async_output)

write_file(no_reset_src, "@clocked(clk_aux, none, domain_aux)\n@hardware\nfn no_reset_reg(a: u8) -> u8:\n    a\n")
val no_reset_output = compile_pure_vhdl(no_reset_src, no_reset_out)
check_msg(no_reset_output.contains("p_aux: process(clk_aux)"), no_reset_output)
check_msg(no_reset_output.contains("if rising_edge(clk_aux) then"), no_reset_output)
check_msg(no_reset_output.contains("if none =") == false, no_reset_output)

delete_file(sync_src)
delete_file(sync_out)
delete_file(async_src)
delete_file(async_out)
delete_file(no_reset_src)
delete_file(no_reset_out)
```

</details>

#### rejects implicit cross-domain reads with source and destination names

1. delete file
2. delete file
3. write file
4. check msg
5. check msg
6. check msg
7. delete file
8. delete file


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src_path = "/tmp/sml_pure_vhdl_cross_domain.spl"
val out_path = "/tmp/sml_pure_vhdl_cross_domain.vhd"
delete_file(src_path)
delete_file(out_path)
write_file(src_path, "@clocked(clk_fast, none, domain_fast)\n@hardware\nfn fast(a: u8) -> u8:\n    a\n\n@clocked(clk_slow, none, domain_slow)\n@hardware\nfn slow(a: u8) -> u8:\n    fast(a)\n")

val diagnostic = compile_pure_vhdl_error(src_path, out_path)
check_msg(diagnostic.contains("E0710 clock domain crossing"), diagnostic)
check_msg(diagnostic.contains("domain `slow`"), diagnostic)
check_msg(diagnostic.contains("domain `fast`"), diagnostic)

delete_file(src_path)
delete_file(out_path)
```

</details>

### pure Simple VHDL GHDL acceptance

#### generated pure Simple full_add VHDL passes GHDL analyze elaborate and synth

1. delete file
2. delete file
3. write file
4. check msg
5. check msg
6. delete file
7. delete file


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src_path = "/tmp/sml_pure_vhdl_ghdl_full_add.spl"
val out_path = "/tmp/sml_pure_vhdl_ghdl_full_add.vhd"
delete_file(src_path)
delete_file(out_path)
write_file(src_path, "@hardware\nfn full_add(a: i32, b: i32) -> i32:\n    a + b\n")

val output = compile_pure_vhdl(src_path, out_path)
check_msg(output.contains("entity full_add is"), output)
if local_ghdl_available():
    check_msg(local_ghdl_synth(out_path, "full_add"), "GHDL synth rejected pure full_add VHDL")

delete_file(src_path)
delete_file(out_path)
```

</details>

#### generated pure Simple caller callee VHDL passes GHDL analyze elaborate and synth

1. delete file
2. delete file
3. write file
4. check msg
5. check msg
6. delete file
7. delete file


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src_path = "/tmp/sml_pure_vhdl_ghdl_call.spl"
val out_path = "/tmp/sml_pure_vhdl_ghdl_call.vhd"
delete_file(src_path)
delete_file(out_path)
write_file(src_path, "@hardware\nfn flags(a: bool, b: bool) -> (left: bool, right: bool):\n    (left: a, right: b)\n\n@hardware\nfn top(a: bool, b: bool) -> bool:\n    val lo = flags(a, b)\n    lo.left\n")

val output = compile_pure_vhdl(src_path, out_path)
check_msg(output.contains("entity top is"), output)
if local_ghdl_available():
    check_msg(local_ghdl_synth(out_path, "top"), "GHDL synth rejected pure caller/callee VHDL")

delete_file(src_path)
delete_file(out_path)
```

</details>

#### pure Simple diagnostics prevent writing stale or partial VHDL files

1. delete file
2. delete file
3. write file
4. write file
5. check msg
6. check msg
7. delete file
8. delete file


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src_path = "/tmp/sml_pure_vhdl_stale_failure.spl"
val out_path = "/tmp/sml_pure_vhdl_stale_failure.vhd"
delete_file(src_path)
delete_file(out_path)
write_file(src_path, "@hardware\nfn float_bad(a: f32) -> f32:\n    a\n")
write_file(out_path, "stale VHDL")

val (stdout, stderr, code) = rt_process_run("bin/simple", ["compile", "--backend=vhdl", src_path, "-o", out_path])
check_msg(code != 0, stdout + stderr)
check_msg(not rt_file_exists(out_path), "failed pure VHDL compile left stale output artifact")

delete_file(src_path)
delete_file(out_path)
```

</details>

#### pure Simple VHDL output is byte-stable across compilations

1. delete file
2. delete file
3. delete file
4. write file
5. check msg
6. delete file
7. delete file
8. delete file


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src_path = "/tmp/sml_pure_vhdl_stable.spl"
val out1 = "/tmp/sml_pure_vhdl_stable_run1.vhd"
val out2 = "/tmp/sml_pure_vhdl_stable_run2.vhd"
delete_file(src_path)
delete_file(out1)
delete_file(out2)
write_file(src_path, "@hardware\nfn full_add(a: i32, b: i32) -> i32:\n    a + b\n")

val run1 = compile_pure_vhdl(src_path, out1)
val run2 = compile_pure_vhdl(src_path, out2)
check_msg(run1 == run2, "VHDL output is not byte-stable across compilations")

delete_file(src_path)
delete_file(out1)
delete_file(out2)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/03_system/compiler/pure_simple_vhdl_source_of_truth_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- pure Simple VHDL source-of-truth metadata
- pure Simple VHDL return ABI and diagnostics
- pure Simple VHDL hardware calls
- pure Simple VHDL fixed-width and domains
- pure Simple VHDL GHDL acceptance

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 24 |
| Active scenarios | 24 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

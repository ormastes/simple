# VHDL Testbench Conversion Specification

> Tests that the Simple-to-VHDL testbench converter correctly translates hardware test source into testbench IR, and rejects unsupported constructs with diagnostics.

<!-- sdn-diagram:id=vhdl_testbench_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=vhdl_testbench_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

vhdl_testbench_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=vhdl_testbench_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 46 | 46 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# VHDL Testbench Conversion Specification

Tests that the Simple-to-VHDL testbench converter correctly translates hardware test source into testbench IR, and rejects unsupported constructs with diagnostics.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #VHDL-PARITY-012 |
| Category | Tooling |
| Difficulty | 3/5 |
| Status | In Progress |
| Plan | doc/03_plan/agent_tasks/vhdl_testbench_conversion.md |
| Source | `test/01_unit/compiler/vhdl/vhdl_testbench_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests that the Simple-to-VHDL testbench converter correctly translates
hardware test source into testbench IR, and rejects unsupported constructs
with diagnostics.

## Key Concepts

- Single @hardware DUT extraction from test source
- Literal scalar stimuli (bool, integer, bit-vector)
- expect(...).to_equal(...) assertion mapping
- Unsupported construct rejection before VHDL emission

## Behavior

The converter must:
1. Find exactly one @hardware DUT in the test source
2. Extract port declarations from port comments/annotations
3. Map set/assign stimuli to VhdlTestbenchAssignment IR
4. Map expect().to_equal() to VhdlTestbenchAssertion IR
5. Reject loops, branches, unsupported matchers, multi-DUT, file I/O

## Scenarios

### VHDL Testbench Converter - Identifier Extraction

#### extracts DUT name from @hardware fn declaration

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val line = "@hardware fn half_adder(a: bool, b: bool):"
val dut_name = tb_extract_ident(line, "@hardware")
expect(dut_name).to_equal("half_adder")
```

</details>

#### extracts DUT name from @hardware without fn keyword

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val line = "@hardware adder"
val dut_name = tb_extract_ident(line, "@hardware")
expect(dut_name).to_equal("adder")
```

</details>

#### returns empty for line without @hardware

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val line = "fn regular_function():"
val dut_name = tb_extract_ident(line, "@hardware")
expect(dut_name).to_equal("")
```

</details>

#### handles extra whitespace before identifier

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val line = "@hardware   fn   my_dut(x: i64):"
val dut_name = tb_extract_ident(line, "@hardware")
expect(dut_name).to_equal("my_dut")
```

</details>

#### stops at non-identifier characters

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val line = "@hardware fn alu(a: i32, b: i32):"
val dut_name = tb_extract_ident(line, "@hardware")
expect(dut_name).to_equal("alu")
```

</details>

### VHDL Testbench Converter - Assertion Parsing

#### extracts actual value from expect to_equal

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val line = "        expect(sum).to_equal(true)"
val actual = tb_parse_actual(line)
expect(actual).to_equal("sum")
```

</details>

#### extracts expected value from expect to_equal

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val line = "        expect(sum).to_equal(true)"
val expected_val = tb_parse_expected(line)
expect(expected_val).to_equal("true")
```

</details>

#### handles nested parentheses in actual

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val line = "expect(dut.output(0)).to_equal(false)"
val actual = tb_parse_actual(line)
expect(actual).to_equal("dut.output(0)")
```

</details>

#### returns empty for non-expect lines

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val line = "val x = compute()"
val actual = tb_parse_actual(line)
expect(actual).to_equal("")
```

</details>

#### handles integer expected values

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val line = "expect(counter).to_equal(42)"
val expected_val = tb_parse_expected(line)
expect(expected_val).to_equal("42")
```

</details>

### VHDL Testbench Converter - Stimulus Parsing

#### extracts target from set statement

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tgt = tb_set_target("set a = true")
expect(tgt).to_equal("a")
```

</details>

#### extracts literal from set statement

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val lit = tb_set_literal("set a = true")
expect(lit).to_equal("true")
```

</details>

#### handles integer set literal

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val lit = tb_set_literal("set counter = 255")
expect(lit).to_equal("255")
```

</details>

#### returns empty for non-set lines

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tgt = tb_set_target("val x = 42")
expect(tgt).to_equal("")
```

</details>

#### returns empty literal for non-set lines

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val lit = tb_set_literal("val x = 42")
expect(lit).to_equal("")
```

</details>

### VHDL Testbench Converter - Port Parsing

#### extracts port name from port comment

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pname = tb_port_name("# port: clk in std_logic")
expect(pname).to_equal("clk")
```

</details>

#### extracts port name with vector type

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pname = tb_port_name("# port: data_in in std_logic_vector(7 downto 0)")
expect(pname).to_equal("data_in")
```

</details>

#### returns empty for non-port comments

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pname = tb_port_name("# this is a regular comment")
expect(pname).to_equal("")
```

</details>

#### returns empty for malformed port comment

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pname = tb_port_name("# port: incomplete")
expect(pname).to_equal("")
```

</details>

### VHDL Testbench Converter - Name Sanitization

#### replaces spaces with underscores

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = tb_sanitize("half adder test")
expect(r).to_equal("half_adder_test")
```

</details>

#### replaces special characters

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = tb_sanitize("test-case.1")
expect(r).to_equal("test_case_1")
```

</details>

#### prepends tb_ for names starting with digits

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = tb_sanitize("123_test")
expect(r).to_equal("tb_123_test")
```

</details>

#### handles empty name

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = tb_sanitize("")
expect(r).to_equal("unnamed")
```

</details>

#### preserves valid VHDL identifier

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = tb_sanitize("my_testbench")
expect(r).to_equal("my_testbench")
```

</details>

#### produces deterministic output

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r1 = tb_sanitize("half adder")
val r2 = tb_sanitize("half adder")
expect(r1).to_equal(r2)
```

</details>

### VHDL Testbench Converter - Unsupported Construct Rejection

#### detects to_contain as unsupported

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bad = tb_bad_matcher("expect(x).to_contain(y)")
expect(bad).to_equal(true)
```

</details>

#### detects to_be_greater_than as unsupported

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bad = tb_bad_matcher("expect(x).to_be_greater_than(5)")
expect(bad).to_equal(true)
```

</details>

#### detects to_be_less_than as unsupported

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bad = tb_bad_matcher("expect(x).to_be_less_than(10)")
expect(bad).to_equal(true)
```

</details>

#### detects to_be_nil as unsupported

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bad = tb_bad_matcher("expect(x).to_be_nil")
expect(bad).to_equal(true)
```

</details>

#### accepts to_equal as supported

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bad = tb_bad_matcher("expect(x).to_equal(42)")
expect(bad).to_equal(false)
```

</details>

#### returns false for non-expect lines

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bad = tb_bad_matcher("val x = 42")
expect(bad).to_equal(false)
```

</details>

<details>
<summary>Advanced: detects for-loop as unsupported</summary>

#### detects for-loop as unsupported

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val is_loop = tb_has_loop("for i in 0..10:")
expect(is_loop).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: detects while-loop as unsupported</summary>

#### detects while-loop as unsupported

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val is_loop2 = tb_has_loop("while running:")
expect(is_loop2).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: does not flag regular lines as loops</summary>

#### does not flag regular lines as loops

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val is_loop3 = tb_has_loop("set a = true")
expect(is_loop3).to_equal(false)
```

</details>


</details>

### VHDL Testbench Converter - DUT Declaration Counting

#### finds one DUT in single-DUT source

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = "@hardware fn half_adder(a: bool, b: bool):\n    val x = 1"
val n = tb_count_duts(src)
expect(n).to_equal(1)
```

</details>

#### finds zero DUTs when no @hardware present

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = "fn regular():\n    val x = 1"
val n = tb_count_duts(src)
expect(n).to_equal(0)
```

</details>

#### finds two DUTs in multi-DUT source

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = "@hardware fn adder(a: i32):\n    val x = 1\n@hardware fn mux(sel: bool):\n    val y = 2"
val n = tb_count_duts(src)
expect(n).to_equal(2)
```

</details>

### VHDL Testbench Converter - Parenthesis Matching

#### finds closing paren for simple expression

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = tb_match_paren("expect(x)", 6)
expect(p).to_equal(8)
```

</details>

#### finds closing paren with nested parens

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = tb_match_paren("expect(f(x))", 6)
expect(p).to_equal(11)
```

</details>

#### returns negative one for unmatched paren

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = tb_match_paren("expect(x", 6)
expect(p).to_equal(-1)
```

</details>

#### handles deeply nested parens

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = tb_match_paren("expect(a(b(c)))", 6)
expect(p).to_equal(14)
```

</details>

### VHDL Testbench Converter - Conversion Shape

#### produces testbench name with _tb suffix

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tb_name = tb_sanitize("half_adder") + "_tb"
expect(tb_name).to_equal("half_adder_tb")
```

</details>

#### produces tb_ prefix for numeric-starting names

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tb_name = tb_sanitize("42_test") + "_tb"
expect(tb_name).to_equal("tb_42_test_tb")
```

</details>

#### sanitizes complex test names for VHDL entities

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tb_name = tb_sanitize("test half-adder (basic)") + "_tb"
expect(tb_name).to_equal("test_half_adder__basic__tb")
```

</details>

#### extracts both actual and expected from assertion line

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val line = "expect(s_sum).to_equal(true)"
val actual = tb_parse_actual(line)
val expected_val = tb_parse_expected(line)
expect(actual).to_equal("s_sum")
expect(expected_val).to_equal("true")
```

</details>

#### extracts stimulus target and literal together

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val line = "set s_a = true"
val tgt = tb_set_target(line)
val lit = tb_set_literal(line)
expect(tgt).to_equal("s_a")
expect(lit).to_equal("true")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 46 |
| Active scenarios | 46 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Plan:** [doc/03_plan/agent_tasks/vhdl_testbench_conversion.md](doc/03_plan/agent_tasks/vhdl_testbench_conversion.md)


</details>

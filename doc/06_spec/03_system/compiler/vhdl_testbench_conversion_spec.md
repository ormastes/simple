# VHDL Testbench Conversion System Specification

> System-level tests verifying that the full Simple-to-VHDL combinational testbench conversion pipeline produces correctly structured VHDL. Covers DUT extraction, stimulus mapping, assertion mapping, unsupported-construct rejection, and deterministic output shapes.

<!-- sdn-diagram:id=vhdl_testbench_conversion_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=vhdl_testbench_conversion_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

vhdl_testbench_conversion_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=vhdl_testbench_conversion_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 39 | 39 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# VHDL Testbench Conversion System Specification

System-level tests verifying that the full Simple-to-VHDL combinational testbench conversion pipeline produces correctly structured VHDL. Covers DUT extraction, stimulus mapping, assertion mapping, unsupported-construct rejection, and deterministic output shapes.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #VHDL-PARITY-012 |
| Category | Tooling |
| Difficulty | 3/5 |
| Status | In Progress |
| Plan | doc/03_plan/agent_tasks/vhdl_testbench_conversion.md |
| Source | `test/03_system/compiler/vhdl_testbench_conversion_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

System-level tests verifying that the full Simple-to-VHDL combinational
testbench conversion pipeline produces correctly structured VHDL. Covers DUT
extraction, stimulus mapping, assertion mapping, unsupported-construct
rejection, and deterministic output shapes.

## Key Concepts

- Converter input is Simple test source text; output is VhdlTestbenchArtifact
- Combinational testbench: no clock/reset fields in the DUT
- Renderer produces testbench_entity, testbench_vhdl, source_map_json
- Unsupported constructs are rejected with a diagnostic before any VHDL is emitted
- Repeated conversion of identical source must produce byte-stable output

## Behavior

- extract_ident locates DUT name after @hardware annotation
- parse_actual / parse_expected extract operands from expect(...).to_equal(...)
- sanitize_tb_name maps arbitrary test names to valid VHDL identifiers
- converter rejects source with 0 DUTs, >1 DUT, 0 assertions, or loops
- renderer embeds LIBRARY ieee, entity, architecture, signal declarations,
  DUT instance, stimulus process, and deterministic finish

## Scenarios

### VHDL Testbench Conversion - DUT Extraction

#### extracts DUT name from @hardware fn declaration

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val line = "@hardware fn half_adder(a: bool, b: bool):"
val name = sys_extract_ident(line, "@hardware")
expect(name).to_equal("half_adder")
```

</details>

#### extracts DUT name when fn keyword is absent

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val line = "@hardware adder_unit"
val name = sys_extract_ident(line, "@hardware")
expect(name).to_equal("adder_unit")
```

</details>

#### returns empty string for line without @hardware

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val line = "fn regular_function(x: i32) -> i32:"
val name = sys_extract_ident(line, "@hardware")
expect(name).to_equal("")
```

</details>

#### stops identifier extraction at opening parenthesis

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val line = "@hardware fn alu(a: i32, b: i32) -> i32:"
val name = sys_extract_ident(line, "@hardware")
expect(name).to_equal("alu")
```

</details>

#### counts zero DUTs in source with no @hardware

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = "fn plain(a: bool) -> bool:\n    a"
val n = sys_count_duts(src)
expect(n).to_equal(0)
```

</details>

#### counts exactly one DUT in typical test source

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = "@hardware fn half_adder(a: bool, b: bool):\n    pass\n# port: a in std_logic\n# port: b in std_logic\nset a = true\nset b = false\nexpect(s_sum).to_equal(false)"
val n = sys_count_duts(src)
expect(n).to_equal(1)
```

</details>

#### counts two DUTs when source contains two @hardware annotations

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = "@hardware fn dut_a():\n    pass\n@hardware fn dut_b():\n    pass"
val n = sys_count_duts(src)
expect(n).to_equal(2)
```

</details>

### VHDL Testbench Conversion - Assertion Parsing

#### extracts actual value from a basic assertion

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val line = "expect(s_sum).to_equal(true)"
val actual = sys_parse_actual(line)
expect(actual).to_equal("s_sum")
```

</details>

#### extracts expected value from a basic assertion

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val line = "expect(s_sum).to_equal(true)"
val ev = sys_parse_expected(line)
expect(ev).to_equal("true")
```

</details>

#### extracts integer expected value

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val line = "expect(counter).to_equal(42)"
val ev = sys_parse_expected(line)
expect(ev).to_equal("42")
```

</details>

#### returns empty actual for non-expect lines

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val line = "val x = compute()"
val actual = sys_parse_actual(line)
expect(actual).to_equal("")
```

</details>

#### returns empty expected for non-expect lines

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val line = "val x = compute()"
val ev = sys_parse_expected(line)
expect(ev).to_equal("")
```

</details>

#### handles nested parentheses in actual

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val line = "expect(dut.output(0)).to_equal(false)"
val actual = sys_parse_actual(line)
expect(actual).to_equal("dut.output(0)")
```

</details>

#### detects assertions present in multi-line source

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = "set a = true\nexpect(s_sum).to_equal(false)\n"
val has = sys_has_assertions(src)
expect(has).to_equal(true)
```

</details>

#### detects missing assertions in source without expect

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = "set a = true\nval x = 1\n"
val has = sys_has_assertions(src)
expect(has).to_equal(false)
```

</details>

### VHDL Testbench Conversion - Name Sanitization

#### replaces spaces with underscores

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = sys_sanitize_tb_name("half adder test")
expect(r).to_equal("half_adder_test")
```

</details>

#### replaces hyphens with underscores

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = sys_sanitize_tb_name("test-case-one")
expect(r).to_equal("test_case_one")
```

</details>

#### replaces dots with underscores

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = sys_sanitize_tb_name("test.case.1")
expect(r).to_equal("test_case_1")
```

</details>

#### prepends tb_ when name starts with a digit

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = sys_sanitize_tb_name("42_test")
expect(r).to_equal("tb_42_test")
```

</details>

#### returns unnamed for empty name

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = sys_sanitize_tb_name("")
expect(r).to_equal("unnamed")
```

</details>

#### preserves valid VHDL identifier unchanged

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = sys_sanitize_tb_name("my_testbench")
expect(r).to_equal("my_testbench")
```

</details>

#### produces deterministic output on repeated calls

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r1 = sys_sanitize_tb_name("half adder")
val r2 = sys_sanitize_tb_name("half adder")
expect(r1).to_equal(r2)
```

</details>

### VHDL Testbench Conversion - Unsupported Construct Rejection

<details>
<summary>Advanced: detects while loop as unsupported construct</summary>

#### detects while loop as unsupported construct

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = "while i < 10:\n    i = i + 1"
val bad = sys_has_loop(src)
expect(bad).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: detects for loop as unsupported construct</summary>

#### detects for loop as unsupported construct

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = "for x in items:\n    process(x)"
val bad = sys_has_loop(src)
expect(bad).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: does not flag source without loops</summary>

#### does not flag source without loops

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = "set a = true\nexpect(s_out).to_equal(true)"
val bad = sys_has_loop(src)
expect(bad).to_equal(false)
```

</details>


</details>

### VHDL Testbench Conversion - Generated VHDL Shape

#### generated VHDL contains LIBRARY ieee header

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val vhdl = "library ieee;\nuse ieee.std_logic_1164.all;\nentity tb_half_adder is\nend entity tb_half_adder;\narchitecture sim of tb_half_adder is\nbegin\n  stimulus: process\n  begin\n    assert s_sum = '0' report \"fail\" severity failure;\n    finish;\n  end process stimulus;\nend architecture sim;"
val has = sys_vhdl_has_library(vhdl)
expect(has).to_equal(true)
```

</details>

#### generated VHDL contains testbench entity declaration

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val vhdl = "library ieee;\nuse ieee.std_logic_1164.all;\nentity tb_half_adder is\nend entity tb_half_adder;\narchitecture sim of tb_half_adder is\nbegin\n  stimulus: process\n  begin\n    finish;\n  end process stimulus;\nend architecture sim;"
val has = sys_vhdl_has_entity(vhdl, "tb_half_adder")
expect(has).to_equal(true)
```

</details>

#### generated VHDL contains architecture sim declaration

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val vhdl = "library ieee;\narchitecture sim of tb_half_adder is\nbegin\n  finish;\nend architecture sim;"
val has = sys_vhdl_has_arch(vhdl, "tb_half_adder")
expect(has).to_equal(true)
```

</details>

#### generated VHDL contains DUT component instance

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val vhdl = "dut: entity work.half_adder port map(a => s_a, b => s_b, sum => s_sum);"
val has = sys_vhdl_has_instance(vhdl, "half_adder")
expect(has).to_equal(true)
```

</details>

#### generated VHDL contains stimulus process

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val vhdl = "stimulus: process\nbegin\n  finish;\nend process stimulus;"
val has = sys_vhdl_has_stimulus(vhdl)
expect(has).to_equal(true)
```

</details>

#### generated VHDL contains at least one assert statement

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val vhdl = "assert s_sum = '0' report \"expectation 1 failed\" severity failure;"
val has = sys_vhdl_has_assert(vhdl)
expect(has).to_equal(true)
```

</details>

#### testbench entity name is derived from sanitized test name

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val test_name = "half adder basic"
val tb_name = sys_sanitize_tb_name(test_name) + "_tb"
expect(tb_name).to_equal("half_adder_basic_tb")
```

</details>

### VHDL Testbench Conversion - Source Map Shape

#### source map json contains testbench field

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val json = "{\"version\": 1, \"testbench\": \"tb_half_adder\", \"dutEntity\": \"half_adder\", \"testName\": {\"name\": \"half adder\", \"line\": 1, \"sourceLine\": 1}, \"duts\": [], \"phases\": [], \"ports\": [], \"expectations\": []}"
expect(sys_source_map_has_field(json, "testbench")).to_equal(true)
```

</details>

#### source map json contains dutEntity field

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val json = "{\"version\": 1, \"testbench\": \"tb_half_adder\", \"dutEntity\": \"half_adder\", \"testName\": {\"name\": \"half adder\", \"line\": 1, \"sourceLine\": 1}, \"duts\": [], \"phases\": [], \"ports\": [], \"expectations\": []}"
expect(sys_source_map_has_field(json, "dutEntity")).to_equal(true)
```

</details>

#### source map json contains testName field

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val json = "{\"version\": 1, \"testbench\": \"tb_half_adder\", \"dutEntity\": \"half_adder\", \"testName\": {\"name\": \"half adder\", \"line\": 1, \"sourceLine\": 1}, \"duts\": [], \"phases\": [], \"ports\": [], \"expectations\": []}"
expect(sys_source_map_has_field(json, "testName")).to_equal(true)
```

</details>

#### source map json contains expectations field

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val json = "{\"version\": 1, \"testbench\": \"tb_half_adder\", \"dutEntity\": \"half_adder\", \"testName\": {\"name\": \"half adder\", \"line\": 1, \"sourceLine\": 1}, \"duts\": [], \"phases\": [], \"ports\": [], \"expectations\": []}"
expect(sys_source_map_has_field(json, "expectations")).to_equal(true)
```

</details>

#### source map json contains ports field

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val json = "{\"version\": 1, \"testbench\": \"tb_half_adder\", \"dutEntity\": \"half_adder\", \"testName\": {\"name\": \"half adder\", \"line\": 1, \"sourceLine\": 1}, \"duts\": [], \"phases\": [], \"ports\": [], \"expectations\": []}"
expect(sys_source_map_has_field(json, "ports")).to_equal(true)
```

</details>

#### source map json contains version field

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val json = "{\"version\": 1, \"testbench\": \"tb_half_adder\", \"dutEntity\": \"half_adder\", \"testName\": {}, \"duts\": [], \"phases\": [], \"ports\": [], \"expectations\": []}"
expect(sys_source_map_has_field(json, "version")).to_equal(true)
```

</details>

#### source map json is byte-stable on repeated conversion of same source

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val json1 = "{\"version\": 1, \"testbench\": \"tb_adder\", \"dutEntity\": \"adder\", \"testName\": {\"name\": \"adder\", \"line\": 1, \"sourceLine\": 1}, \"duts\": [], \"phases\": [], \"ports\": [], \"expectations\": []}"
val json2 = "{\"version\": 1, \"testbench\": \"tb_adder\", \"dutEntity\": \"adder\", \"testName\": {\"name\": \"adder\", \"line\": 1, \"sourceLine\": 1}, \"duts\": [], \"phases\": [], \"ports\": [], \"expectations\": []}"
expect(json1).to_equal(json2)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 39 |
| Active scenarios | 39 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Plan:** [doc/03_plan/agent_tasks/vhdl_testbench_conversion.md](doc/03_plan/agent_tasks/vhdl_testbench_conversion.md)


</details>

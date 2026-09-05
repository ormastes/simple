# VHDL Clocked Testbench Conversion System Specification

> System-level tests verifying that the clocked-domain testbench conversion pipeline correctly models clock domains, reset sequences, cycle advances, timing constraints, and the generated VHDL shape for sequential DUTs.

<!-- sdn-diagram:id=vhdl_clocked_testbench_conversion_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=vhdl_clocked_testbench_conversion_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

vhdl_clocked_testbench_conversion_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=vhdl_clocked_testbench_conversion_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 46 | 46 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# VHDL Clocked Testbench Conversion System Specification

System-level tests verifying that the clocked-domain testbench conversion pipeline correctly models clock domains, reset sequences, cycle advances, timing constraints, and the generated VHDL shape for sequential DUTs.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #VHDL-PARITY-012 |
| Category | Tooling |
| Difficulty | 3/5 |
| Status | In Progress |
| Plan | doc/03_plan/agent_tasks/vhdl_testbench_conversion.md |
| Source | `test/03_system/compiler/vhdl_clocked_testbench_conversion_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

System-level tests verifying that the clocked-domain testbench conversion
pipeline correctly models clock domains, reset sequences, cycle advances,
timing constraints, and the generated VHDL shape for sequential DUTs.

## Key Concepts

- ClockConfig: period_ns, edge, domain_name; half_period = period_ns / 2
- ResetSequence: sync/async, active-high/low, duration_cycles, signal_name
- CycleAdvance: cycle_count, from_step, to_step
- TimingConstraint: min/max cycle range, check(cycles) returns updated struct
- ClockedBench: clock_period_ns, reset_cycles, total_cycles; sim_time_ns()
- Generated VHDL must include clock generator process and reset sequence

## Behavior

- Default clock is 10 ns rising-edge "clk"
- Async active-low reset: signal asserted = '0', deasserted = '1'
- Sync active-high reset: signal asserted = '1', deasserted = '0'
- sim_time_ns = total_cycles * clock_period_ns
- TimingConstraint.in_range is true when min_cycles <= cycles <= max_cycles

## Scenarios

### VHDL Clocked Testbench - ClockConfig

#### default clock has 10 ns period

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val period = 10
expect(period).to_equal(10)
```

</details>

#### default clock edge is rising

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val edge = "rising"
expect(clk_is_rising(edge)).to_equal(true)
expect(clk_is_falling(edge)).to_equal(false)
```

</details>

#### default clock domain name is clk

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val domain = "clk"
expect(domain).to_equal("clk")
```

</details>

#### half period is half of full period

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val half = clk_half_period(10)
expect(half).to_equal(5)
```

</details>

#### half period of 20 ns clock is 10 ns

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val half = clk_half_period(20)
expect(half).to_equal(10)
```

</details>

#### custom clock has custom period

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val period = 4
expect(period).to_equal(4)
```

</details>

#### falling edge clock is not rising

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val edge = "falling"
expect(clk_is_rising(edge)).to_equal(false)
expect(clk_is_falling(edge)).to_equal(true)
```

</details>

#### custom clock domain name is preserved

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val domain = "sys_clk"
expect(domain).to_equal("sys_clk")
```

</details>

### VHDL Clocked Testbench - ResetSequence

#### async active-low reset is async

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(reset_is_async("async")).to_equal(true)
expect(reset_is_sync("async")).to_equal(false)
```

</details>

#### sync active-high reset is sync

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(reset_is_sync("sync")).to_equal(true)
expect(reset_is_async("sync")).to_equal(false)
```

</details>

#### active-low polarity is detected

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(reset_is_active_low("active_low")).to_equal(true)
expect(reset_is_active_high("active_low")).to_equal(false)
```

</details>

#### active-high polarity is detected

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(reset_is_active_high("active_high")).to_equal(true)
expect(reset_is_active_low("active_high")).to_equal(false)
```

</details>

#### active-low asserted value is logic zero

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v = reset_asserted_value("active_low")
expect(v).to_equal("'0'")
```

</details>

#### active-low deasserted value is logic one

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v = reset_deasserted_value("active_low")
expect(v).to_equal("'1'")
```

</details>

#### active-high asserted value is logic one

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v = reset_asserted_value("active_high")
expect(v).to_equal("'1'")
```

</details>

#### active-high deasserted value is logic zero

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v = reset_deasserted_value("active_high")
expect(v).to_equal("'0'")
```

</details>

#### reset duration is preserved in duration_cycles field

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cycles = 3
expect(cycles).to_equal(3)
```

</details>

### VHDL Clocked Testbench - CycleAdvance

#### cycle span is to_step minus from_step

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val span = cycle_span(2, 7)
expect(span).to_equal(5)
```

</details>

#### zero span when from equals to

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val span = cycle_span(5, 5)
expect(span).to_equal(0)
```

</details>

#### final advance flag is independent from cycle count

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val count = 3
val is_final = true
expect(count).to_equal(3)
expect(is_final).to_equal(true)
```

</details>

### VHDL Clocked Testbench - TimingConstraint

#### cycle count within range is accepted

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ok = timing_in_range(5, 3, 8)
expect(ok).to_equal(true)
```

</details>

#### cycle count at lower bound is accepted

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ok = timing_in_range(3, 3, 8)
expect(ok).to_equal(true)
```

</details>

#### cycle count at upper bound is accepted

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ok = timing_in_range(8, 3, 8)
expect(ok).to_equal(true)
```

</details>

#### cycle count below lower bound is rejected

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ok = timing_in_range(2, 3, 8)
expect(ok).to_equal(false)
```

</details>

#### cycle count above upper bound is rejected

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ok = timing_in_range(9, 3, 8)
expect(ok).to_equal(false)
```

</details>

### VHDL Clocked Testbench - ClockedBench

#### sim_time_ns is total_cycles multiplied by clock_period_ns

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val time_ns = clocked_sim_time_ns(10, 10)
expect(time_ns).to_equal(100)
```

</details>

#### sim_time_ns with 4 ns period and 20 cycles is 80 ns

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val time_ns = clocked_sim_time_ns(20, 4)
expect(time_ns).to_equal(80)
```

</details>

#### has_reset is true when reset_cycles > 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val has = clocked_has_reset(3)
expect(has).to_equal(true)
```

</details>

#### has_reset is false when reset_cycles == 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val has = clocked_has_reset(0)
expect(has).to_equal(false)
```

</details>

#### to_text includes bench_name and dut_entity

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = clocked_bench_to_text("my_tb", "counter", 10, 20)
expect(s.contains("my_tb")).to_equal(true)
expect(s.contains("counter")).to_equal(true)
```

</details>

#### to_text includes clock period

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = clocked_bench_to_text("my_tb", "counter", 10, 20)
expect(s.contains("10ns")).to_equal(true)
```

</details>

#### to_text includes total cycle count

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = clocked_bench_to_text("my_tb", "counter", 10, 20)
expect(s.contains("20")).to_equal(true)
```

</details>

### VHDL Clocked Testbench - Generated VHDL Shape

#### clocked VHDL contains clock generator process

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val vhdl = "clock_driver: process\nbegin\n  loop\n    clk <= '0'; wait for 5 ns;\n    clk <= '1'; wait for 5 ns;\n  end loop;\nend process clock_driver;"
val has = clk_vhdl_has_clock_process(vhdl)
expect(has).to_equal(true)
```

</details>

#### clocked VHDL contains wait-for half-period timing

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val vhdl = "clk <= '0'; wait for 5 ns;\nclk <= '1'; wait for 5 ns;"
val has = clk_vhdl_has_wait_for(vhdl, "5")
expect(has).to_equal(true)
```

</details>

<details>
<summary>Advanced: clocked VHDL contains loop construct for clock generation</summary>

#### clocked VHDL contains loop construct for clock generation

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val vhdl = "loop\n  clk <= '0'; wait for 5 ns;\n  clk <= '1'; wait for 5 ns;\nend loop;"
val has = clk_vhdl_has_loop(vhdl)
expect(has).to_equal(true)
```

</details>


</details>

#### clocked VHDL contains reset signal assignment

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val vhdl = "rst_n <= '0';\nwait for 30 ns;\nrst_n <= '1';"
val has = clk_vhdl_has_reset_signal(vhdl, "rst_n")
expect(has).to_equal(true)
```

</details>

#### clocked VHDL contains testbench entity declaration

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val vhdl = "entity tb_counter is\nend entity tb_counter;\narchitecture sim of tb_counter is\nbegin\nend architecture sim;"
val has = clk_vhdl_has_entity(vhdl, "tb_counter")
expect(has).to_equal(true)
```

</details>

#### clocked VHDL contains architecture sim declaration

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val vhdl = "architecture sim of tb_counter is\nbegin\nend architecture sim;"
val has = clk_vhdl_has_arch(vhdl, "tb_counter")
expect(has).to_equal(true)
```

</details>

#### clocked VHDL contains DUT instance

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val vhdl = "dut: entity work.counter port map(clk => clk, rst_n => rst_n, count => s_count);"
val has = clk_vhdl_has_instance(vhdl, "counter")
expect(has).to_equal(true)
```

</details>

#### clocked VHDL contains stimulus process

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val vhdl = "stimulus: process\nbegin\n  finish;\nend process stimulus;"
val has = clk_vhdl_has_stimulus(vhdl)
expect(has).to_equal(true)
```

</details>

#### clocked VHDL contains assert statement for expected output

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val vhdl = "assert s_count = \"00000001\" report \"expectation 1 failed\" severity failure;"
val has = clk_vhdl_has_assert(vhdl)
expect(has).to_equal(true)
```

</details>

### VHDL Clocked Testbench - Reset Behavior

#### reset duration of 2 cycles covers at least 2 clock periods

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val reset_cycles = 2
val period_ns = 10
val reset_time_ns = reset_cycles * period_ns
expect(reset_time_ns).to_equal(20)
```

</details>

#### async reset asserted value differs from deasserted value

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val asserted = reset_asserted_value("active_low")
val deasserted = reset_deasserted_value("active_low")
val different = asserted != deasserted
expect(different).to_equal(true)
```

</details>

#### sync reset asserted value differs from deasserted value

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val asserted = reset_asserted_value("active_high")
val deasserted = reset_deasserted_value("active_high")
val different = asserted != deasserted
expect(different).to_equal(true)
```

</details>

#### wrong latency detection: expected output at cycle 1 but output ready at cycle 2

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val expected_latency = 1
val actual_latency = 2
val latency_ok = expected_latency == actual_latency
expect(latency_ok).to_equal(false)
```

</details>

#### correct latency detection: expected output at cycle 2 matches actual

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val expected_latency = 2
val actual_latency = 2
val latency_ok = expected_latency == actual_latency
expect(latency_ok).to_equal(true)
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

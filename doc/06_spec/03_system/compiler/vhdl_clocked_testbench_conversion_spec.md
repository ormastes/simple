# VHDL Clocked Testbench Conversion System Specification

> System-level tests verifying that the clocked-domain testbench conversion pipeline correctly models clock domains, reset sequences, cycle advances, timing constraints, and the generated VHDL shape for sequential DUTs.

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
| Updated | 2026-08-26 |
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

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- default clock has 10 ns period
   - Expected: period equals `10`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("default clock has 10 ns period")
val period = 10
expect(period).to_equal(10)
```

</details>

#### default clock edge is rising

- default clock edge is rising
   - Expected: clk_is_rising(edge) is true
   - Expected: clk_is_falling(edge) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("default clock edge is rising")
val edge = "rising"
expect(clk_is_rising(edge)).to_equal(true)
expect(clk_is_falling(edge)).to_equal(false)
```

</details>

#### default clock domain name is clk

- default clock domain name is clk
   - Expected: domain equals `clk`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("default clock domain name is clk")
val domain = "clk"
expect(domain).to_equal("clk")
```

</details>

#### half period is half of full period

- half period is half of full period
   - Expected: half equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("half period is half of full period")
val half = clk_half_period(10)
expect(half).to_equal(5)
```

</details>

#### half period of 20 ns clock is 10 ns

- half period of 20 ns clock is 10 ns
   - Expected: half equals `10`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("half period of 20 ns clock is 10 ns")
val half = clk_half_period(20)
expect(half).to_equal(10)
```

</details>

#### custom clock has custom period

- custom clock has custom period
   - Expected: period equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("custom clock has custom period")
val period = 4
expect(period).to_equal(4)
```

</details>

#### falling edge clock is not rising

- falling edge clock is not rising
   - Expected: clk_is_rising(edge) is false
   - Expected: clk_is_falling(edge) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("falling edge clock is not rising")
val edge = "falling"
expect(clk_is_rising(edge)).to_equal(false)
expect(clk_is_falling(edge)).to_equal(true)
```

</details>

#### custom clock domain name is preserved

- custom clock domain name is preserved
   - Expected: domain equals `sys_clk`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("custom clock domain name is preserved")
val domain = "sys_clk"
expect(domain).to_equal("sys_clk")
```

</details>

### VHDL Clocked Testbench - ResetSequence

#### async active-low reset is async

- async active-low reset is async
   - Expected: reset_is_async("async") is true
   - Expected: reset_is_sync("async") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("async active-low reset is async")
expect(reset_is_async("async")).to_equal(true)
expect(reset_is_sync("async")).to_equal(false)
```

</details>

#### sync active-high reset is sync

- sync active-high reset is sync
   - Expected: reset_is_sync("sync") is true
   - Expected: reset_is_async("sync") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("sync active-high reset is sync")
expect(reset_is_sync("sync")).to_equal(true)
expect(reset_is_async("sync")).to_equal(false)
```

</details>

#### active-low polarity is detected

- active-low polarity is detected
   - Expected: reset_is_active_low("active_low") is true
   - Expected: reset_is_active_high("active_low") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("active-low polarity is detected")
expect(reset_is_active_low("active_low")).to_equal(true)
expect(reset_is_active_high("active_low")).to_equal(false)
```

</details>

#### active-high polarity is detected

- active-high polarity is detected
   - Expected: reset_is_active_high("active_high") is true
   - Expected: reset_is_active_low("active_high") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("active-high polarity is detected")
expect(reset_is_active_high("active_high")).to_equal(true)
expect(reset_is_active_low("active_high")).to_equal(false)
```

</details>

#### active-low asserted value is logic zero

- active-low asserted value is logic zero
   - Expected: v equals `'0'`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("active-low asserted value is logic zero")
val v = reset_asserted_value("active_low")
expect(v).to_equal("'0'")
```

</details>

#### active-low deasserted value is logic one

- active-low deasserted value is logic one
   - Expected: v equals `'1'`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("active-low deasserted value is logic one")
val v = reset_deasserted_value("active_low")
expect(v).to_equal("'1'")
```

</details>

#### active-high asserted value is logic one

- active-high asserted value is logic one
   - Expected: v equals `'1'`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("active-high asserted value is logic one")
val v = reset_asserted_value("active_high")
expect(v).to_equal("'1'")
```

</details>

#### active-high deasserted value is logic zero

- active-high deasserted value is logic zero
   - Expected: v equals `'0'`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("active-high deasserted value is logic zero")
val v = reset_deasserted_value("active_high")
expect(v).to_equal("'0'")
```

</details>

#### reset duration is preserved in duration_cycles field

- reset duration is preserved in duration_cycles field
   - Expected: cycles equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("reset duration is preserved in duration_cycles field")
val cycles = 3
expect(cycles).to_equal(3)
```

</details>

### VHDL Clocked Testbench - CycleAdvance

#### cycle span is to_step minus from_step

- cycle span is to_step minus from_step
   - Expected: span equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("cycle span is to_step minus from_step")
val span = cycle_span(2, 7)
expect(span).to_equal(5)
```

</details>

#### zero span when from equals to

- zero span when from equals to
   - Expected: span equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("zero span when from equals to")
val span = cycle_span(5, 5)
expect(span).to_equal(0)
```

</details>

#### final advance flag is independent from cycle count

- final advance flag is independent from cycle count
   - Expected: count equals `3`
   - Expected: is_final is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("final advance flag is independent from cycle count")
val count = 3
val is_final = true
expect(count).to_equal(3)
expect(is_final).to_equal(true)
```

</details>

### VHDL Clocked Testbench - TimingConstraint

#### cycle count within range is accepted

- cycle count within range is accepted
   - Expected: ok is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("cycle count within range is accepted")
val ok = timing_in_range(5, 3, 8)
expect(ok).to_equal(true)
```

</details>

#### cycle count at lower bound is accepted

- cycle count at lower bound is accepted
   - Expected: ok is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("cycle count at lower bound is accepted")
val ok = timing_in_range(3, 3, 8)
expect(ok).to_equal(true)
```

</details>

#### cycle count at upper bound is accepted

- cycle count at upper bound is accepted
   - Expected: ok is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("cycle count at upper bound is accepted")
val ok = timing_in_range(8, 3, 8)
expect(ok).to_equal(true)
```

</details>

#### cycle count below lower bound is rejected

- cycle count below lower bound is rejected
   - Expected: ok is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("cycle count below lower bound is rejected")
val ok = timing_in_range(2, 3, 8)
expect(ok).to_equal(false)
```

</details>

#### cycle count above upper bound is rejected

- cycle count above upper bound is rejected
   - Expected: ok is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("cycle count above upper bound is rejected")
val ok = timing_in_range(9, 3, 8)
expect(ok).to_equal(false)
```

</details>

### VHDL Clocked Testbench - ClockedBench

#### sim_time_ns is total_cycles multiplied by clock_period_ns

- sim_time_ns is total_cycles multiplied by clock_period_ns
   - Expected: time_ns equals `100`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("sim_time_ns is total_cycles multiplied by clock_period_ns")
val time_ns = clocked_sim_time_ns(10, 10)
expect(time_ns).to_equal(100)
```

</details>

#### sim_time_ns with 4 ns period and 20 cycles is 80 ns

- sim_time_ns with 4 ns period and 20 cycles is 80 ns
   - Expected: time_ns equals `80`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("sim_time_ns with 4 ns period and 20 cycles is 80 ns")
val time_ns = clocked_sim_time_ns(20, 4)
expect(time_ns).to_equal(80)
```

</details>

#### has_reset is true when reset_cycles > 0

- has_reset is true when reset_cycles > 0
   - Expected: has is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("has_reset is true when reset_cycles > 0")
val has = clocked_has_reset(3)
expect(has).to_equal(true)
```

</details>

#### has_reset is false when reset_cycles == 0

- has_reset is false when reset_cycles == 0
   - Expected: has is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("has_reset is false when reset_cycles == 0")
val has = clocked_has_reset(0)
expect(has).to_equal(false)
```

</details>

#### to_text includes bench_name and dut_entity

- to_text includes bench_name and dut_entity
   - Expected: s contains `my_tb`
   - Expected: s contains `counter`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("to_text includes bench_name and dut_entity")
val s = clocked_bench_to_text("my_tb", "counter", 10, 20)
expect(s.contains("my_tb")).to_equal(true)
expect(s.contains("counter")).to_equal(true)
```

</details>

#### to_text includes clock period

- to_text includes clock period
   - Expected: s contains `10ns`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("to_text includes clock period")
val s = clocked_bench_to_text("my_tb", "counter", 10, 20)
expect(s.contains("10ns")).to_equal(true)
```

</details>

#### to_text includes total cycle count

- to_text includes total cycle count
   - Expected: s contains `20`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("to_text includes total cycle count")
val s = clocked_bench_to_text("my_tb", "counter", 10, 20)
expect(s.contains("20")).to_equal(true)
```

</details>

### VHDL Clocked Testbench - Generated VHDL Shape

#### clocked VHDL contains clock generator process

- clocked VHDL contains clock generator process
   - Expected: has is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("clocked VHDL contains clock generator process")
val vhdl = "clock_driver: process\nbegin\n  loop\n    clk <= '0'; wait for 5 ns;\n    clk <= '1'; wait for 5 ns;\n  end loop;\nend process clock_driver;"
val has = clk_vhdl_has_clock_process(vhdl)
expect(has).to_equal(true)
```

</details>

#### clocked VHDL contains wait-for half-period timing

- clocked VHDL contains wait-for half-period timing
   - Expected: has is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("clocked VHDL contains wait-for half-period timing")
val vhdl = "clk <= '0'; wait for 5 ns;\nclk <= '1'; wait for 5 ns;"
val has = clk_vhdl_has_wait_for(vhdl, "5")
expect(has).to_equal(true)
```

</details>

<details>
<summary>Advanced: clocked VHDL contains loop construct for clock generation</summary>

#### clocked VHDL contains loop construct for clock generation

- clocked VHDL contains loop construct for clock generation
   - Expected: has is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("clocked VHDL contains loop construct for clock generation")
val vhdl = "loop\n  clk <= '0'; wait for 5 ns;\n  clk <= '1'; wait for 5 ns;\nend loop;"
val has = clk_vhdl_has_loop(vhdl)
expect(has).to_equal(true)
```

</details>


</details>

#### clocked VHDL contains reset signal assignment

- clocked VHDL contains reset signal assignment
   - Expected: has is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("clocked VHDL contains reset signal assignment")
val vhdl = "rst_n <= '0';\nwait for 30 ns;\nrst_n <= '1';"
val has = clk_vhdl_has_reset_signal(vhdl, "rst_n")
expect(has).to_equal(true)
```

</details>

#### clocked VHDL contains testbench entity declaration

- clocked VHDL contains testbench entity declaration
   - Expected: has is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("clocked VHDL contains testbench entity declaration")
val vhdl = "entity tb_counter is\nend entity tb_counter;\narchitecture sim of tb_counter is\nbegin\nend architecture sim;"
val has = clk_vhdl_has_entity(vhdl, "tb_counter")
expect(has).to_equal(true)
```

</details>

#### clocked VHDL contains architecture sim declaration

- clocked VHDL contains architecture sim declaration
   - Expected: has is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("clocked VHDL contains architecture sim declaration")
val vhdl = "architecture sim of tb_counter is\nbegin\nend architecture sim;"
val has = clk_vhdl_has_arch(vhdl, "tb_counter")
expect(has).to_equal(true)
```

</details>

#### clocked VHDL contains DUT instance

- clocked VHDL contains DUT instance
   - Expected: has is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("clocked VHDL contains DUT instance")
val vhdl = "dut: entity work.counter port map(clk => clk, rst_n => rst_n, count => s_count);"
val has = clk_vhdl_has_instance(vhdl, "counter")
expect(has).to_equal(true)
```

</details>

#### clocked VHDL contains stimulus process

- clocked VHDL contains stimulus process
   - Expected: has is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("clocked VHDL contains stimulus process")
val vhdl = "stimulus: process\nbegin\n  finish;\nend process stimulus;"
val has = clk_vhdl_has_stimulus(vhdl)
expect(has).to_equal(true)
```

</details>

#### clocked VHDL contains assert statement for expected output

- clocked VHDL contains assert statement for expected output
   - Expected: has is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("clocked VHDL contains assert statement for expected output")
val vhdl = "assert s_count = \"00000001\" report \"expectation 1 failed\" severity failure;"
val has = clk_vhdl_has_assert(vhdl)
expect(has).to_equal(true)
```

</details>

### VHDL Clocked Testbench - Reset Behavior

#### reset duration of 2 cycles covers at least 2 clock periods

- reset duration of 2 cycles covers at least 2 clock periods
   - Expected: reset_time_ns equals `20`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("reset duration of 2 cycles covers at least 2 clock periods")
val reset_cycles = 2
val period_ns = 10
val reset_time_ns = reset_cycles * period_ns
expect(reset_time_ns).to_equal(20)
```

</details>

#### async reset asserted value differs from deasserted value

- async reset asserted value differs from deasserted value
   - Expected: different is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("async reset asserted value differs from deasserted value")
val asserted = reset_asserted_value("active_low")
val deasserted = reset_deasserted_value("active_low")
val different = asserted != deasserted
expect(different).to_equal(true)
```

</details>

#### sync reset asserted value differs from deasserted value

- sync reset asserted value differs from deasserted value
   - Expected: different is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("sync reset asserted value differs from deasserted value")
val asserted = reset_asserted_value("active_high")
val deasserted = reset_deasserted_value("active_high")
val different = asserted != deasserted
expect(different).to_equal(true)
```

</details>

#### wrong latency detection: expected output at cycle 1 but output ready at cycle 2

- wrong latency detection: expected output at cycle 1 but output ready at cycle 2
   - Expected: latency_ok is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("wrong latency detection: expected output at cycle 1 but output ready at cycle 2")
val expected_latency = 1
val actual_latency = 2
val latency_ok = expected_latency == actual_latency
expect(latency_ok).to_equal(false)
```

</details>

#### correct latency detection: expected output at cycle 2 matches actual

- correct latency detection: expected output at cycle 2 matches actual
   - Expected: latency_ok is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("correct latency detection: expected output at cycle 2 matches actual")
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

- **Plan:** `doc/03_plan/agent_tasks/vhdl_testbench_conversion.md`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `7ca3a75d41396df544cb82551916d7a854ca438a35ce32cfaa6928f2b5cab8f2`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `7ca3a75d41396df544cb82551916d7a854ca438a35ce32cfaa6928f2b5cab8f2`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `7ca3a75d41396df544cb82551916d7a854ca438a35ce32cfaa6928f2b5cab8f2`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/03_system/compiler/vhdl_clocked_testbench_conversion_spec.spl
mirror: doc/06_spec/03_system/compiler/vhdl_clocked_testbench_conversion_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/compiler/vhdl_clocked_testbench_conversion_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/compiler/vhdl_clocked_testbench_conversion_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/compiler/vhdl_clocked_testbench_conversion_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 11 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/compiler/vhdl_clocked_testbench_conversion_spec.spl:157:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'default clock has 10 ns period' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/compiler/vhdl_clocked_testbench_conversion_spec.spl:163:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'default clock edge is rising' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/compiler/vhdl_clocked_testbench_conversion_spec.spl:170:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'default clock domain name is clk' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

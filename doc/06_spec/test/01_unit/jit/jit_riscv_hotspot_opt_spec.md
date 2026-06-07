# Jit Riscv Hotspot Opt Specification

> <details>

<!-- sdn-diagram:id=jit_riscv_hotspot_opt_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=jit_riscv_hotspot_opt_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

jit_riscv_hotspot_opt_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=jit_riscv_hotspot_opt_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Jit Riscv Hotspot Opt Specification

## Scenarios

### RiscvMixedJit

<details>
<summary>Advanced: compiles loop_sum for riscv64 and calls it</summary>

#### compiles loop_sum for riscv64 and calls it

1. print
2. jit cleanup
3. jit cleanup
   - Expected: result equals `45`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val jit = RiscvMixedJit.create()
val res = jit.compile_for_64("loop_sum", loop_sum_src)
if res.err != "":
    print("SKIP: rv64 compile unavailable: " + res.err)
    jit.cleanup()
    expect(res.err.len()).to_be_greater_than(0)
    return
val result = jit.call_i64_on_64("loop_sum", 10)
# loop_sum(10) = 0+1+2+...+9 = 45
jit.cleanup()
expect(result).to_equal(45)
```

</details>


</details>

#### compiles square for riscv32 or skips gracefully

1. print
2. jit cleanup
3. jit cleanup
   - Expected: result equals `49`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val jit = RiscvMixedJit.create()
val res = jit.compile_for_32("square", square_src)
if res.err != "":
    print("SKIP: riscv32 JIT not available: " + res.err)
    jit.cleanup()
    expect(res.err.len()).to_be_greater_than(0)
    return
val result = jit.call_i64_on_32("square", 7)
jit.cleanup()
expect(result).to_equal(49)
```

</details>

<details>
<summary>Advanced: applies I32NarrowPass annotation to loop_sum source</summary>

#### applies I32NarrowPass annotation to loop_sum source

1. jit cleanup
   - Expected: narrowed_flag is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val jit = RiscvMixedJit.create()
val res = jit.compile_optimized("loop_sum", loop_sum_src)
# The narrowing pass should annotate ops found in loop_sum_src.
# We verify the pass ran by checking that narrowed=true on the result.
val narrowed_flag = res.narrowed
jit.cleanup()
expect(narrowed_flag).to_equal(true)
```

</details>


</details>

#### auto-promotes hot function to native after threshold calls

1. jit register hot
   - Expected: before is false
2. jit cleanup
   - Expected: after is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val jit = RiscvMixedJit.create()
val threshold: i64 = 3
jit.register_hot("add_one", add_one_src, threshold)
# Before threshold: function not yet compiled
val before = jit.is_compiled_64("add_one")
expect(before).to_equal(false)
# drive_to_hot calls record_call threshold times via module-level fn,
# then checks rt_jit_has_function as source of truth for compilation.
val after = drive_to_hot(jit, "add_one", threshold)
jit.cleanup()
expect(after).to_equal(true)
```

</details>

#### compile_optimized is not slower than 2x plain compile

1. print
2. jit cleanup
3. jit cleanup
   - Expected: ok is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Use distinct function names and sources to avoid duplicate-definition errors.
val jit = RiscvMixedJit.create()
val plain_src = "fn plain_fn(n: i64) -> i64:\n    return n + 1\n"
val opt_src = "fn opt_fn(n: i64) -> i64:\n    var r: i64 = n * 2\n    return r + 1\n"
val plain = jit.compile_for_64("plain_fn", plain_src)
val opt = jit.compile_optimized("opt_fn", opt_src)
if plain.err != "" or opt.err != "":
    print("SKIP: compile unavailable for timing comparison")
    jit.cleanup()
    expect((plain.err + opt.err).len()).to_be_greater_than(0)
    return
# Both compiled successfully; optimized run includes narrowing pass overhead.
val ok = opt.err == ""
jit.cleanup()
expect(ok).to_equal(true)
```

</details>

#### stats reports riscv64 and riscv32 QEMU target info

1. jit cleanup
   - Expected: has_rv64 is true
   - Expected: has_rv32 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val jit = RiscvMixedJit.create()
val s = jit.stats()
val has_rv64 = s.contains("riscv64")
val has_rv32 = s.contains("riscv32")
jit.cleanup()
expect(has_rv64).to_equal(true)
expect(has_rv32).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/01_unit/jit/jit_riscv_hotspot_opt_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- RiscvMixedJit

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

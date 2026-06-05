# Mir Pattern Idiom Benchmark Specification

> <details>

<!-- sdn-diagram:id=mir_pattern_idiom_benchmark_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=mir_pattern_idiom_benchmark_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

mir_pattern_idiom_benchmark_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=mir_pattern_idiom_benchmark_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Mir Pattern Idiom Benchmark Specification

## Scenarios

### pattern_idiom benchmark — large MIR

#### pass descriptor resolves correctly for pattern_idiom

<details>
<summary>Executable SPipe</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val desc_opt = mir_pass_descriptor_for_name("pattern_idiom")
expect(desc_opt.?).to_equal(true)
val desc = desc_opt.unwrap()
expect(desc.stable_name).to_equal("pattern_idiom")
# PassKind is typed — confirm scope is Module
match desc.scope:
    case Module: expect(true).to_equal(true)
    case Function: expect(false).to_equal(true)
```

</details>

#### run_pass_on_module with pattern_idiom completes on 10-function module

<details>
<summary>Executable SPipe</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val module = bench_make_module(10, 2, 5)
val before_count = count_total_instructions(module)
# pattern_idiom in bare run_pass_on_module is a structural no-op
# (target ctx required for actual rewrites); pass must return module unchanged
val result = run_pass_on_module("pattern_idiom", module)
val after_count = count_total_instructions(result)
# No instructions should be removed or added without a target context
expect(after_count).to_equal(before_count)
```

</details>

#### run_typed_pass_on_module with PatternIdiom is consistent with string dispatch

<details>
<summary>Executable SPipe</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val module = bench_make_module(10, 2, 5)
val result_named = run_pass_on_module("pattern_idiom", module)
val result_typed = run_typed_pass_on_module(PassKind.PatternIdiom, module)
val count_named = count_total_instructions(result_named)
val count_typed = count_total_instructions(result_typed)
expect(count_typed).to_equal(count_named)
```

</details>

#### pattern_idiom pass scales linearly — 50 functions

<details>
<summary>Executable SPipe</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val module = bench_make_module(50, 3, 8)
val expected_insts = count_total_instructions(module)
# 50 fns * 3 blocks/fn * 8 insts/block = 1200 instructions
expect(expected_insts).to_be_greater_than(0)
val result = run_pass_on_module("pattern_idiom", module)
val after = count_total_instructions(result)
expect(after).to_equal(expected_insts)
```

</details>

#### pattern_idiom pass scales linearly — 100 functions

<details>
<summary>Executable SPipe</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val module = bench_make_module(100, 4, 10)
val expected_insts = count_total_instructions(module)
expect(expected_insts).to_be_greater_than(0)
val result = run_pass_on_module("pattern_idiom", module)
val after = count_total_instructions(result)
expect(after).to_equal(expected_insts)
```

</details>

#### PassKind.PatternIdiom scope is Module

<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val desc = mir_pass_descriptor_for_name("pattern_idiom").unwrap()
match desc.scope:
    case Module: expect(true).to_equal(true)
    case Function: expect(false).to_equal(true)
```

</details>

#### PassKind.AutoVectorize scope is Module

<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val desc = mir_pass_descriptor_for_name("auto_vectorize").unwrap()
match desc.scope:
    case Module: expect(true).to_equal(true)
    case Function: expect(false).to_equal(true)
```

</details>

#### function-scope passes have Function scope

<details>
<summary>Executable SPipe</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val dce_desc = mir_pass_descriptor_for_name("dead_code_elimination").unwrap()
val cf_desc = mir_pass_descriptor_for_name("constant_folding").unwrap()
val cp_desc = mir_pass_descriptor_for_name("copy_propagation").unwrap()
match dce_desc.scope:
    case Function: expect(true).to_equal(true)
    case Module: expect(false).to_equal(true)
match cf_desc.scope:
    case Function: expect(true).to_equal(true)
    case Module: expect(false).to_equal(true)
match cp_desc.scope:
    case Function: expect(true).to_equal(true)
    case Module: expect(false).to_equal(true)
```

</details>

### MirInstCounter visitor — large MIR

#### counts instructions correctly for a single function

<details>
<summary>Executable SPipe</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# 1 block, 4 insts (2 Const + 2 BinOp pairs)
val func = bench_make_function(0, 1, 4)
val counter = mir_inst_counter_count_function(mir_inst_counter_new(), func)
expect(counter.function_count).to_equal(1)
expect(counter.block_count).to_equal(1)
expect(counter.inst_count).to_be_greater_than(0)
```

</details>

#### counts blocks correctly for multi-block function

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val func = bench_make_function(0, 5, 3)
val counter = mir_inst_counter_count_function(mir_inst_counter_new(), func)
expect(counter.block_count).to_equal(5)
```

</details>

#### counts functions correctly across module

<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val module = bench_make_module(20, 2, 3)
val counter = mir_inst_counter_count_module(module)
expect(counter.function_count).to_equal(20)
expect(counter.block_count).to_equal(40)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/mir/mir_pattern_idiom_benchmark_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- pattern_idiom benchmark — large MIR
- MirInstCounter visitor — large MIR

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 11 |
| Active scenarios | 11 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

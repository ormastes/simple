# Llvm Ir Builder Specification

> 1. builder emit module header

<!-- sdn-diagram:id=llvm_ir_builder_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=llvm_ir_builder_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

llvm_ir_builder_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=llvm_ir_builder_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Llvm Ir Builder Specification

## Scenarios

### LLVM IR Builder

#### emits the module header from the selected target

1. builder emit module header
   - Expected: builder.instructions.len() equals `5`
   - Expected: builder.instructions[0] equals `; ModuleID = 'demo.module'`
   - Expected: builder.instructions[1] equals `source_filename = "demo.module.spl"`
   - Expected: builder.instructions[4] equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val builder = new_builder()

builder.emit_module_header()

expect(builder.instructions.len()).to_equal(5)
expect(builder.instructions[0]).to_equal("; ModuleID = 'demo.module'")
expect(builder.instructions[1]).to_equal("source_filename = \"demo.module.spl\"")
expect(builder.instructions[2]).to_contain("target datalayout = \"")
expect(builder.instructions[3]).to_contain("target triple = \"")
expect(builder.instructions[4]).to_equal("")
```

</details>

#### creates fresh locals and wraps a function body

1. builder start function
2. builder emit ret
3. builder end function
   - Expected: builder.instructions[0] equals `define i64 @add_numbers(i64 %lhs, i64 %rhs) nounwind {`
   - Expected: builder.instructions[1] equals `  ret i64 %lhs`
   - Expected: builder.instructions[2] equals `}`
   - Expected: builder.instructions[3] equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val builder = new_builder()
val local0 = builder.fresh_local()
val local1 = builder.fresh_local()

expect(local0).to_equal("%0")
expect(local1).to_equal("%1")

builder.start_function("add_numbers", ["i64 %lhs", "i64 %rhs"], "i64")
builder.emit_ret("i64", "%lhs")
builder.end_function()

expect(builder.instructions[0]).to_equal("define i64 @add_numbers(i64 %lhs, i64 %rhs) nounwind {")
expect(builder.instructions[1]).to_equal("  ret i64 %lhs")
expect(builder.instructions[2]).to_equal("}")
expect(builder.instructions[3]).to_equal("")
```

</details>

#### emits direct arithmetic, memory, and comparison instructions

1. builder emit add
2. builder emit load
3. builder emit store
4. builder emit icmp eq
   - Expected: builder.instructions[0] equals `  %2 = add i64 %0, %1`
   - Expected: builder.instructions[1] equals `  %3 = load i64, ptr %ptr, align 8`
   - Expected: builder.instructions[2] equals `  store i64 %3, ptr %ptr, align 8`
   - Expected: builder.instructions[3] equals `  %4 = icmp eq i64 %3, %2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val builder = new_builder()

builder.emit_add("%2", "i64", "%0", "%1")
builder.emit_load("%3", "i64", "%ptr")
builder.emit_store("i64", "%3", "%ptr")
builder.emit_icmp_eq("%4", "i64", "%3", "%2")

expect(builder.instructions[0]).to_equal("  %2 = add i64 %0, %1")
expect(builder.instructions[1]).to_equal("  %3 = load i64, ptr %ptr, align 8")
expect(builder.instructions[2]).to_equal("  store i64 %3, ptr %ptr, align 8")
expect(builder.instructions[3]).to_equal("  %4 = icmp eq i64 %3, %2")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/backend/llvm_ir_builder_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- LLVM IR Builder

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

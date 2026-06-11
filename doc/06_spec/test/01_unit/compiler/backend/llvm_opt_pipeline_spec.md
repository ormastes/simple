# Llvm Opt Pipeline Specification

> <details>

<!-- sdn-diagram:id=llvm_opt_pipeline_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=llvm_opt_pipeline_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

llvm_opt_pipeline_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=llvm_opt_pipeline_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Llvm Opt Pipeline Specification

## Scenarios

### Llvm Opt Pipeline

#### maps Simple optimization levels to LLVM default pipelines

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(llvm_default_pipeline_for_level(OptimizationLevel.None_)).to_equal("default<O0>")
expect(llvm_default_pipeline_for_level(OptimizationLevel.Debug)).to_equal("default<O0>")
expect(llvm_default_pipeline_for_level(OptimizationLevel.Size)).to_equal("default<Os>")
expect(llvm_default_pipeline_for_level(OptimizationLevel.Speed)).to_equal("default<O2>")
expect(llvm_default_pipeline_for_level(OptimizationLevel.Aggressive)).to_equal("default<O3>")
expect(llvm_default_pipeline_for_size_min()).to_equal("default<Oz>")
```

</details>

#### maps CLI optimization flags to LLVM default pipelines

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(llvm_default_pipeline_for_flag("-O0")).to_equal("default<O0>")
expect(llvm_default_pipeline_for_flag("-O1")).to_equal("default<O1>")
expect(llvm_default_pipeline_for_flag("-O2")).to_equal("default<O2>")
expect(llvm_default_pipeline_for_flag("-O3")).to_equal("default<O3>")
expect(llvm_default_pipeline_for_flag("-Os")).to_equal("default<Os>")
expect(llvm_default_pipeline_for_flag("-Oz")).to_equal("default<Oz>")
expect(llvm_default_pipeline_for_flag("-Ofast")).to_be_nil()
```

</details>

#### preserves explicit pass diagnostics separately from default pipelines

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(passes_for_level(OptimizationLevel.Speed).len()).to_be_greater_than(0)
expect(passes_for_level(OptimizationLevel.Speed)[0].to_text()).to_equal("instcombine")
```

</details>

#### emits nsw and nuw arithmetic flags

1. b emit add nsw
2. b emit sub nsw
3. b emit mul nsw
4. b emit add nuw
5. b emit add


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val b = builder()
b.emit_add_nsw("%r1", "i64", "%a", "%b")
b.emit_sub_nsw("%r2", "i64", "%a", "%b")
b.emit_mul_nsw("%r3", "i64", "%a", "%b")
b.emit_add_nuw("%r4", "i64", "%a", "%b")
b.emit_add("%r5", "i64", "%a", "%b")

val ir = b.build()

expect(ir).to_contain("%r1 = add nsw i64 %a, %b")
expect(ir).to_contain("%r2 = sub nsw i64 %a, %b")
expect(ir).to_contain("%r3 = mul nsw i64 %a, %b")
expect(ir).to_contain("%r4 = add nuw i64 %a, %b")
expect(ir).to_contain("%r5 = add i64 %a, %b")
```

</details>

#### reports natural alignment and integer helpers

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(natural_alignment("i64")).to_equal(8)
expect(natural_alignment("i32")).to_equal(4)
expect(natural_alignment("i16")).to_equal(2)
expect(natural_alignment("i8")).to_equal(1)
expect(natural_alignment("double")).to_equal(8)
expect(natural_alignment("ptr")).to_equal(8)
expect(is_integer_type("i64")).to_equal(true)
expect(is_integer_type("double")).to_equal(false)
expect(is_signed_int_type("i64")).to_equal(true)
expect(is_signed_int_type("i8")).to_equal(false)
```

</details>

#### emits aligned allocas, loads, and stores

1. b emit alloca aligned
2. b emit load
3. b emit store


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val b = builder()
b.emit_alloca_aligned("%simd", "i64", 32)
b.emit_load("%v", "float", "%p")
b.emit_store("double", "%v", "%p")

val ir = b.build()

expect(ir).to_contain("%simd = alloca i64, align 32")
expect(ir).to_contain("%v = load float, ptr %p, align 4")
expect(ir).to_contain("store double %v, ptr %p, align 8")
```

</details>

#### emits optimized function framing

1. b start function opt
2. b emit ret
3. b end function


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val b = builder()
b.start_function_opt("pure_fn", ["i64 %x"], "i64", true, true)
b.emit_ret("i64", "%x")
b.end_function()

val ir = b.build()

expect(ir).to_contain("define i64 @pure_fn(i64 %x) nounwind readonly alwaysinline {")
expect(ir).to_contain("ret i64 %x")
```

</details>

#### emits TBAA metadata and tags

1. b emit tbaa hierarchy
2. b emit load tbaa
3. b emit store tbaa
   - Expected: tag_i64 equals `tag_i32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val b = builder()
val tag_i64 = b.tbaa_tag_for_type("i64")
val tag_i32 = b.tbaa_tag_for_type("i32")
val tag_float = b.tbaa_tag_for_type("double")

b.emit_tbaa_hierarchy()
b.emit_load_tbaa("%v", "i64", "%p")
b.emit_store_tbaa("double", "%v", "%p")

val ir = b.build()

expect(tag_i64).to_equal(tag_i32)
expect(tag_i64).to_not_equal(tag_float)
expect(ir).to_contain("Simple TBAA")
expect(ir).to_contain("!tbaa")
expect(ir).to_contain("align 8")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/backend/llvm_opt_pipeline_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Llvm Opt Pipeline

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

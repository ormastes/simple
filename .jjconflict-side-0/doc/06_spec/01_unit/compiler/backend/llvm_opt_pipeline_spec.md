# llvm_opt_pipeline_spec

> Purpose: Prove that Llvm Opt Pipeline.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# llvm_opt_pipeline_spec

Purpose: Prove that Llvm Opt Pipeline.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/backend/llvm_opt_pipeline_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Prove that Llvm Opt Pipeline.
Audience: COMP maintainers who read this spec to confirm the behavior still holds.

## Scenarios

### Llvm Opt Pipeline

#### maps Simple optimization levels to LLVM default pipelines

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- maps Simple optimization levels to LLVM default pipelines
- Verify: maps Simple optimization levels to LLVM default pipelines
   - Expected: llvm_default_pipeline_for_level(OptimizationLevel.None_) equals `default<O0>`
   - Expected: llvm_default_pipeline_for_level(OptimizationLevel.Debug) equals `default<O0>`
   - Expected: llvm_default_pipeline_for_level(OptimizationLevel.Size) equals `default<Os>`
   - Expected: llvm_default_pipeline_for_level(OptimizationLevel.Speed) equals `default<O2>`
   - Expected: llvm_default_pipeline_for_level(OptimizationLevel.Aggressive) equals `default<O3>`
   - Expected: llvm_default_pipeline_for_size_min() equals `default<Oz>`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("maps Simple optimization levels to LLVM default pipelines")
step("Verify: maps Simple optimization levels to LLVM default pipelines")
# @req: REQ-COMP-LLVM-OPT-PIPELINE-001
expect(llvm_default_pipeline_for_level(OptimizationLevel.None_)).to_equal("default<O0>")
expect(llvm_default_pipeline_for_level(OptimizationLevel.Debug)).to_equal("default<O0>")
expect(llvm_default_pipeline_for_level(OptimizationLevel.Size)).to_equal("default<Os>")
expect(llvm_default_pipeline_for_level(OptimizationLevel.Speed)).to_equal("default<O2>")
expect(llvm_default_pipeline_for_level(OptimizationLevel.Aggressive)).to_equal("default<O3>")
expect(llvm_default_pipeline_for_size_min()).to_equal("default<Oz>")
```

</details>

#### maps CLI optimization flags to LLVM default pipelines

- maps CLI optimization flags to LLVM default pipelines
- Verify: maps CLI optimization flags to LLVM default pipelines
   - Expected: llvm_default_pipeline_for_flag("-O0") equals `default<O0>`
   - Expected: llvm_default_pipeline_for_flag("-O1") equals `default<O1>`
   - Expected: llvm_default_pipeline_for_flag("-O2") equals `default<O2>`
   - Expected: llvm_default_pipeline_for_flag("-O3") equals `default<O3>`
   - Expected: llvm_default_pipeline_for_flag("-Os") equals `default<Os>`
   - Expected: llvm_default_pipeline_for_flag("-Oz") equals `default<Oz>`
   - Expected: llvm_default_pipeline_for_flag("-Ofast").is_none() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("maps CLI optimization flags to LLVM default pipelines")
step("Verify: maps CLI optimization flags to LLVM default pipelines")
expect(llvm_default_pipeline_for_flag("-O0")).to_equal("default<O0>")
expect(llvm_default_pipeline_for_flag("-O1")).to_equal("default<O1>")
expect(llvm_default_pipeline_for_flag("-O2")).to_equal("default<O2>")
expect(llvm_default_pipeline_for_flag("-O3")).to_equal("default<O3>")
expect(llvm_default_pipeline_for_flag("-Os")).to_equal("default<Os>")
expect(llvm_default_pipeline_for_flag("-Oz")).to_equal("default<Oz>")
expect(llvm_default_pipeline_for_flag("-Ofast").is_none()).to_equal(true)
```

</details>

#### preserves explicit pass diagnostics separately from default pipelines

- preserves explicit pass diagnostics separately from default pipelines
- Verify: preserves explicit pass diagnostics separately from default pipelines
   - Expected: passes_for_level(OptimizationLevel.Speed)[0].to_text() equals `instcombine`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("preserves explicit pass diagnostics separately from default pipelines")
step("Verify: preserves explicit pass diagnostics separately from default pipelines")
expect(passes_for_level(OptimizationLevel.Speed).len()).to_be_greater_than(0)
expect(passes_for_level(OptimizationLevel.Speed)[0].to_text()).to_equal("instcombine")
```

</details>

#### emits nsw and nuw arithmetic flags

- emits nsw and nuw arithmetic flags
- Verify: emits nsw and nuw arithmetic flags


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("emits nsw and nuw arithmetic flags")
step("Verify: emits nsw and nuw arithmetic flags")
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

- reports natural alignment and integer helpers
- Verify: reports natural alignment and integer helpers
   - Expected: natural_alignment("i64") equals `8`
   - Expected: natural_alignment("i32") equals `4`
   - Expected: natural_alignment("i16") equals `2`
   - Expected: natural_alignment("i8") equals `1`
   - Expected: natural_alignment("double") equals `8`
   - Expected: natural_alignment("ptr") equals `8`
   - Expected: is_integer_type("i64") is true
   - Expected: is_integer_type("double") is false
   - Expected: is_signed_int_type("i64") is true
   - Expected: is_signed_int_type("i8") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("reports natural alignment and integer helpers")
step("Verify: reports natural alignment and integer helpers")
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

- emits aligned allocas, loads, and stores
- Verify: emits aligned allocas, loads, and stores


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("emits aligned allocas, loads, and stores")
step("Verify: emits aligned allocas, loads, and stores")
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

- emits optimized function framing
- Verify: emits optimized function framing


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("emits optimized function framing")
step("Verify: emits optimized function framing")
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

- emits TBAA metadata and tags
- Verify: emits TBAA metadata and tags
   - Expected: tag_i64 equals `tag_i32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("emits TBAA metadata and tags")
step("Verify: emits TBAA metadata and tags")
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

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-COMPILER`
- `REQ-COMP-LLVM-OPT-PIPELINE-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `fd377325bf43e0ebcb2b2e2a43d191a3f1c0cb2c6f63c2dc4a7b773dd09ffe72`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `fd377325bf43e0ebcb2b2e2a43d191a3f1c0cb2c6f63c2dc4a7b773dd09ffe72`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `fd377325bf43e0ebcb2b2e2a43d191a3f1c0cb2c6f63c2dc4a7b773dd09ffe72`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/compiler/backend/llvm_opt_pipeline_spec.spl
mirror: doc/06_spec/01_unit/compiler/backend/llvm_opt_pipeline_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/backend/llvm_opt_pipeline_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/backend/llvm_opt_pipeline_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/backend/llvm_opt_pipeline_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 6 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/backend/llvm_opt_pipeline_spec.spl:29:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'maps Simple optimization levels to LLVM default pipelines' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/backend/llvm_opt_pipeline_spec.spl:41:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'maps CLI optimization flags to LLVM default pipelines' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/backend/llvm_opt_pipeline_spec.spl:53:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'preserves explicit pass diagnostics separately from default pipelines' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

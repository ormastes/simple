# Llvm Array Value Copy Single Ssa Def Specification

> Tests covering alloca SSA transform admits value-returning functions, array value copy emits a single SSA definition per local.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Llvm Array Value Copy Single Ssa Def Specification

## Scenarios

### alloca SSA transform admits value-returning functions

<details>
<summary>Advanced: applies to a value-returning function whose copy-loop counter is multi-def</summary>

#### applies to a value-returning function whose copy-loop counter is multi-def

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- applies to a value-returning function whose copy-loop counter is multi-def
   - Expected: r.applied is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("applies to a value-returning function whose copy-loop counter is multi-def")
val mir = lower_source(copy_in_value_fn)
val f = find_function(mir, "copy_len").unwrap()
expect(count_value_returns(f)).to_be_greater_than(0)
val r = ssa_alloca_transform_blocks(f.blocks, f.locals, f.entry_block)
expect(r.applied).to_equal(true)
```

</details>


</details>

#### loads a reassigned local at the ret instead of leaving it unrewritten

- loads a reassigned local at the ret instead of leaving it unrewritten
   - Expected: r.applied is true
   - Expected: first_duplicate_ssa_def(llvm) equals ``
   - Expected: llvm contains `= load i64, ptr`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("loads a reassigned local at the ret instead of leaving it unrewritten")
val mir = lower_source(loop_ret_local)
val f = find_function(mir, "total").unwrap()
val r = ssa_alloca_transform_blocks(f.blocks, f.locals, f.entry_block)
expect(r.applied).to_equal(true)
val llvm = MirToLlvm.create("test.copy.total", CodegenTarget.X86_64, nil).translate_module(mir)
expect(first_duplicate_ssa_def(llvm)).to_equal("")
expect(llvm.contains("= load i64, ptr")).to_equal(true)
```

</details>

### array value copy emits a single SSA definition per local

#### copy inside a value-returning fn

- copy inside a value-returning fn
   - Expected: first_duplicate_ssa_def(llvm) equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("copy inside a value-returning fn")
val mir = lower_source(copy_in_value_fn)
val llvm = MirToLlvm.create("test.copy.value_fn", CodegenTarget.X86_64, nil).translate_module(mir)
expect(first_duplicate_ssa_def(llvm)).to_equal("")
```

</details>

#### aliased copy then mutate original in main

- aliased copy then mutate original in main
   - Expected: first_duplicate_ssa_def(llvm) equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("aliased copy then mutate original in main")
val mir = lower_source(copy_in_main)
val llvm = MirToLlvm.create("test.copy.main", CodegenTarget.X86_64, nil).translate_module(mir)
expect(first_duplicate_ssa_def(llvm)).to_equal("")
```

</details>

#### text and struct element arrays

- text and struct element arrays
   - Expected: first_duplicate_ssa_def(llvm) equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("text and struct element arrays")
val src = "struct Pt:\n    x: i64\n\nfn go() -> i64:\n    val ss = [\"a\"]\n    val ts = ss\n    val ps = [Pt(x: 1)]\n    val tp = ps\n    ts.len() + tp.len()\n"
val mir = lower_source(src)
val llvm = MirToLlvm.create("test.copy.texts", CodegenTarget.X86_64, nil).translate_module(mir)
expect(first_duplicate_ssa_def(llvm)).to_equal("")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/backend/llvm_array_value_copy_single_ssa_def_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering alloca SSA transform admits value-returning functions, array value copy emits a single SSA definition per local.
- alloca SSA transform admits value-returning functions
- array value copy emits a single SSA definition per local

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `ca82f5018d8be2e204147435470c09ed6ed2c0eca8c45863d872050ffb3a908c`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `ca82f5018d8be2e204147435470c09ed6ed2c0eca8c45863d872050ffb3a908c`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `ca82f5018d8be2e204147435470c09ed6ed2c0eca8c45863d872050ffb3a908c`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/compiler/backend/llvm_array_value_copy_single_ssa_def_spec.spl
mirror: doc/06_spec/01_unit/compiler/backend/llvm_array_value_copy_single_ssa_def_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/backend/llvm_array_value_copy_single_ssa_def_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/backend/llvm_array_value_copy_single_ssa_def_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/backend/llvm_array_value_copy_single_ssa_def_spec.spl:75:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'applies to a value-returning function whose copy-loop counter is multi-def' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/backend/llvm_array_value_copy_single_ssa_def_spec.spl:84:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'loads a reassigned local at the ret instead of leaving it unrewritten' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/backend/llvm_array_value_copy_single_ssa_def_spec.spl:96:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'copy inside a value-returning fn' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

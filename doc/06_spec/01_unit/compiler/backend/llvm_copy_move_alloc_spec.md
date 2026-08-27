# Llvm Copy Move Alloc Specification

> Tests covering LLVM alloc copy move.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Llvm Copy Move Alloc Specification

## Scenarios

### LLVM alloc copy move

#### keeps alloc results pointer-typed across copy and move chains

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- keeps alloc results pointer-typed across copy and move chains
   - Expected: output does not contain `add i64 %l2, 0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps alloc results pointer-typed across copy and move chains")
val translator = MirToLlvm.create("test.llvm.alloc_copy_move", CodegenTarget.X86_64, nil)
val output = translator.translate_module(build_alloc_copy_module())

expect(output).to_contain("%l1 = alloca i64")
expect(output).to_contain("%l2 = getelementptr i8, ptr %l1, i64 0  ; copy")
expect(output).to_contain("%l3 = getelementptr i8, ptr %l2, i64 0  ; move")
expect(output.contains("add i64 %l2, 0")).to_equal(false)
```

</details>

#### treats local id zero as a real SSA local

- treats local id zero as a real SSA local
   - Expected: output does not contain `ptr 0, i64 0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("treats local id zero as a real SSA local")
val translator = MirToLlvm.create("test.llvm.local_zero_pointer_copy", CodegenTarget.X86_64, nil)
val output = translator.translate_module(build_local_zero_pointer_copy_module())

expect(output).to_contain("%l0 = inttoptr i64 0 to ptr  ; const null")
expect(output).to_contain("%l1 = getelementptr i8, ptr %l0, i64 0  ; copy")
expect(output.contains("ptr 0, i64 0")).to_equal(false)
```

</details>

#### compares pointer branch conditions against null

- compares pointer branch conditions against null


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("compares pointer branch conditions against null")
val translator = MirToLlvm.create("test.llvm.pointer_condition", CodegenTarget.X86_64, nil)
val output = translator.translate_module(build_pointer_condition_module())

expect(output).to_contain("icmp ne ptr %l0, null")
```

</details>

#### compares pointer unary not against null

- compares pointer unary not against null
   - Expected: output does not contain `icmp eq i1 %l0, 0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("compares pointer unary not against null")
val translator = MirToLlvm.create("test.llvm.pointer_not", CodegenTarget.X86_64, nil)
val output = translator.translate_module(build_pointer_not_module())

expect(output).to_contain("icmp eq ptr %l0, null")
expect(output.contains("icmp eq i1 %l0, 0")).to_equal(false)
```

</details>

#### does not reference declared locals before a definition

- does not reference declared locals before a definition
   - Expected: output does not contain `add i64 %l2, 0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does not reference declared locals before a definition")
val translator = MirToLlvm.create("test.llvm.declared_undefined_copy", CodegenTarget.X86_64, nil)
val output = translator.translate_module(build_declared_undefined_copy_module())

expect(output).to_contain("%l3 = add i64 undef, 0  ; copy")
expect(output.contains("add i64 %l2, 0")).to_equal(false)
```

</details>

#### keeps a fresh slotted string constant pointer-typed

- keeps a fresh slotted string constant pointer-typed
   - Expected: output does not contain `inttoptr i64 %l3 to ptr`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps a fresh slotted string constant pointer-typed")
val translator = MirToLlvm.create("test.llvm.cross_block_string_const", CodegenTarget.X86_64, nil)
val output = translator.translate_module(build_cross_block_string_const_module())

expect(output).to_contain("%l2 = alloca ptr")
expect(output).to_contain("%l3 = getelementptr inbounds [3 x i8]")
expect(output).to_contain("store ptr %l3, ptr %l2")
expect(output.contains("inttoptr i64 %l3 to ptr")).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/backend/llvm_copy_move_alloc_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering LLVM alloc copy move.
- LLVM alloc copy move

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
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

- Canonical SPipe generation for source `6bd80d148cad8d117ddb81bae80367cf978471b4ab359a13a78b76b3ee4bb8e4`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `6bd80d148cad8d117ddb81bae80367cf978471b4ab359a13a78b76b3ee4bb8e4`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `6bd80d148cad8d117ddb81bae80367cf978471b4ab359a13a78b76b3ee4bb8e4`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/compiler/backend/llvm_copy_move_alloc_spec.spl
mirror: doc/06_spec/01_unit/compiler/backend/llvm_copy_move_alloc_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/backend/llvm_copy_move_alloc_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/backend/llvm_copy_move_alloc_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/backend/llvm_copy_move_alloc_spec.spl:313:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps alloc results pointer-typed across copy and move chains' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/backend/llvm_copy_move_alloc_spec.spl:324:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'treats local id zero as a real SSA local' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/backend/llvm_copy_move_alloc_spec.spl:334:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'compares pointer branch conditions against null' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

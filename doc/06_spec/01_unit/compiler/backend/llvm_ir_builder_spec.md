# Llvm Ir Builder Specification

> Tests covering LLVM IR Builder.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Llvm Ir Builder Specification

## Scenarios

### LLVM IR Builder

#### emits the module header from the selected target

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- emits the module header from the selected target
   - Expected: lines.len() equals `5`
   - Expected: lines[0] equals `; ModuleID = 'demo.module'`
   - Expected: lines[1] equals `source_filename = "demo.module.spl"`
   - Expected: lines[4] equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("emits the module header from the selected target")
val builder = new_builder()

builder.emit_module_header()

val lines = emitted_lines(builder)
expect(lines.len()).to_equal(5)
expect(lines[0]).to_equal("; ModuleID = 'demo.module'")
expect(lines[1]).to_equal("source_filename = \"demo.module.spl\"")
expect(lines[2]).to_contain("target datalayout = \"")
expect(lines[3]).to_contain("target triple = \"")
expect(lines[4]).to_equal("")
```

</details>

#### creates fresh locals and wraps a function body

- creates fresh locals and wraps a function body
   - Expected: local0 equals `%t0`
   - Expected: local1 equals `%t1`
   - Expected: lines[0] equals `define i64 @add_numbers(i64 %lhs, i64 %rhs) nounwind {`
   - Expected: lines[1] equals `  ret i64 %lhs`
   - Expected: lines[2] equals `}`
   - Expected: lines[3] equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("creates fresh locals and wraps a function body")
val builder = new_builder()
val local0 = builder.fresh_local()
val local1 = builder.fresh_local()

# NAMED temporaries (`%tN`), not anonymous `%N`: llc rejects an
# anonymous `%0` interspersed with named `%lN` locals ("instruction
# expected to be numbered '%3' or greater"). See fresh_local's
# docstring in llvm_ir_builder.spl:258-270.
expect(local0).to_equal("%t0")
expect(local1).to_equal("%t1")

builder.start_function("add_numbers", ["i64 %lhs", "i64 %rhs"], "i64")
builder.emit_ret("i64", "%lhs")
builder.end_function()

val lines = emitted_lines(builder)
expect(lines[0]).to_equal("define i64 @add_numbers(i64 %lhs, i64 %rhs) nounwind {")
expect(lines[1]).to_equal("  ret i64 %lhs")
expect(lines[2]).to_equal("}")
expect(lines[3]).to_equal("")
```

</details>

#### emits direct arithmetic, memory, and comparison instructions

- emits direct arithmetic, memory, and comparison instructions
   - Expected: lines[0] equals `  %2 = add i64 %0, %1`
   - Expected: lines[1] equals `  %3 = load i64, ptr %ptr, align 8`
   - Expected: lines[2] equals `  store i64 %3, ptr %ptr, align 8`
   - Expected: lines[3] equals `  %4 = icmp eq i64 %3, %2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("emits direct arithmetic, memory, and comparison instructions")
val builder = new_builder()

builder.emit_add("%2", "i64", "%0", "%1")
builder.emit_load("%3", "i64", "%ptr")
builder.emit_store("i64", "%3", "%ptr")
builder.emit_icmp_eq("%4", "i64", "%3", "%2")

val lines = emitted_lines(builder)
expect(lines[0]).to_equal("  %2 = add i64 %0, %1")
expect(lines[1]).to_equal("  %3 = load i64, ptr %ptr, align 8")
expect(lines[2]).to_equal("  store i64 %3, ptr %ptr, align 8")
expect(lines[3]).to_equal("  %4 = icmp eq i64 %3, %2")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/backend/llvm_ir_builder_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering LLVM IR Builder.
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-COMPILER`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `1e930d82571d0e69d036902b3fa26e4d5910d5b9c9fe3caeaf90a3a14608a5d5`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `1e930d82571d0e69d036902b3fa26e4d5910d5b9c9fe3caeaf90a3a14608a5d5`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `1e930d82571d0e69d036902b3fa26e4d5910d5b9c9fe3caeaf90a3a14608a5d5`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/01_unit/compiler/backend/llvm_ir_builder_spec.spl
mirror: doc/06_spec/01_unit/compiler/backend/llvm_ir_builder_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/backend/llvm_ir_builder_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/backend/llvm_ir_builder_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/backend/llvm_ir_builder_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/backend/llvm_ir_builder_spec.spl:28:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'emits the module header from the selected target' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/backend/llvm_ir_builder_spec.spl:43:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates fresh locals and wraps a function body' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/backend/llvm_ir_builder_spec.spl:67:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'emits direct arithmetic, memory, and comparison instructions' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

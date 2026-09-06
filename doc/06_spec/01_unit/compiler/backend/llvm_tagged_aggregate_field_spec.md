# Llvm Tagged Aggregate Field Specification

> Tests covering LLVM tagged aggregate fields.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Llvm Tagged Aggregate Field Specification

## Scenarios

### LLVM tagged aggregate fields

#### strips runtime tag bits before 64-bit field reads and writes

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- strips runtime tag bits before 64-bit field reads and writes
   - Expected: ir.split("ptrtoint ptr %l0 to i64").len() equals `3`
   - Expected: ir.split("icmp eq i64").len() equals `3`
   - Expected: ir.split("select i1").len() equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("strips runtime tag bits before 64-bit field reads and writes")
val ir = tagged_field_ir(CodegenTarget.X86_64)

expect(ir).to_contain("ptrtoint ptr %l0 to i64")
expect(ir.split("ptrtoint ptr %l0 to i64").len()).to_equal(3)
expect(ir.split("icmp eq i64").len()).to_equal(3)
expect(ir.split("select i1").len()).to_equal(3)
expect(ir).to_contain("and i64")
expect(ir).to_contain(", 7")
expect(ir).to_contain(", 1")
expect(ir).to_contain(", -8")
expect(ir).to_contain("inttoptr i64")
expect(ir).to_contain("getelementptr inbounds i64")
```

</details>

#### uses the target-native integer for 32-bit aggregate pointers

- uses the target-native integer for 32-bit aggregate pointers
   - Expected: ir.split("ptrtoint ptr %l0 to i32").len() equals `3`
   - Expected: ir.split("icmp eq i32").len() equals `3`
   - Expected: ir.split("select i1").len() equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("uses the target-native integer for 32-bit aggregate pointers")
val ir = tagged_field_ir(CodegenTarget.Riscv32)

expect(ir).to_contain("ptrtoint ptr %l0 to i32")
expect(ir.split("ptrtoint ptr %l0 to i32").len()).to_equal(3)
expect(ir.split("icmp eq i32").len()).to_equal(3)
expect(ir.split("select i1").len()).to_equal(3)
expect(ir).to_contain("and i32")
expect(ir).to_contain(", 7")
expect(ir).to_contain(", 1")
expect(ir).to_contain(", -8")
expect(ir).to_contain("inttoptr i32")
expect(ir).to_contain("getelementptr inbounds i32")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/backend/llvm_tagged_aggregate_field_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering LLVM tagged aggregate fields.
- LLVM tagged aggregate fields

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
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

- Canonical SPipe generation for source `1a35a344e5a3b24ee93fcec5ac96db1c99d181745d349c9293295b1b72c4afb5`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `1a35a344e5a3b24ee93fcec5ac96db1c99d181745d349c9293295b1b72c4afb5`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `1a35a344e5a3b24ee93fcec5ac96db1c99d181745d349c9293295b1b72c4afb5`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/01_unit/compiler/backend/llvm_tagged_aggregate_field_spec.spl
mirror: doc/06_spec/01_unit/compiler/backend/llvm_tagged_aggregate_field_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/backend/llvm_tagged_aggregate_field_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/backend/llvm_tagged_aggregate_field_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/backend/llvm_tagged_aggregate_field_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 6 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/backend/llvm_tagged_aggregate_field_spec.spl:30:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'strips runtime tag bits before 64-bit field reads and writes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/backend/llvm_tagged_aggregate_field_spec.spl:46:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'uses the target-native integer for 32-bit aggregate pointers' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

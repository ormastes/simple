# Llvm Bitcast Pointer Bool Specification

> Tests covering LLVM pointer and boolean bitcast lowering.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Llvm Bitcast Pointer Bool Specification

## Scenarios

### LLVM pointer and boolean bitcast lowering

#### preserves an i1 value through native integer before pointer conversion

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- preserves an i1 value through native integer before pointer conversion
   - Expected: ir does not contain `inttoptr i64 0 to ptr`
   - Expected: ir does not contain `bitcast i1 %l0 to ptr`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("preserves an i1 value through native integer before pointer conversion")
val ir = emit_bitcast_ir("i1", "ptr")

expect(ir).to_contain("zext i1 %l0 to i64")
expect(ir).to_contain("inttoptr i64")
expect(ir).to_contain("to ptr")
expect(ir).to_contain("ret ptr %")
expect(ir.contains("inttoptr i64 0 to ptr")).to_equal(false)
expect(ir.contains("bitcast i1 %l0 to ptr")).to_equal(false)
```

</details>

#### compares a pointer against null when producing i1

- compares a pointer against null when producing i1
   - Expected: ir does not contain `bitcast ptr %l0 to i1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("compares a pointer against null when producing i1")
val ir = emit_bitcast_ir("ptr", "i1")

expect(ir).to_contain("icmp ne ptr %l0, null")
expect(ir).to_contain("ret i1 %")
expect(ir.contains("bitcast ptr %l0 to i1")).to_equal(false)
```

</details>

#### uses inttoptr for an integer to pointer conversion

- uses inttoptr for an integer to pointer conversion
   - Expected: ir does not contain `bitcast i64 %l0 to ptr`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("uses inttoptr for an integer to pointer conversion")
val ir = emit_bitcast_ir("i64", "ptr")

expect(ir).to_contain("inttoptr i64 %l0 to ptr")
expect(ir.contains("bitcast i64 %l0 to ptr")).to_equal(false)
```

</details>

#### uses ptrtoint for a pointer to integer conversion

- uses ptrtoint for a pointer to integer conversion
   - Expected: ir does not contain `bitcast ptr %l0 to i64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("uses ptrtoint for a pointer to integer conversion")
val ir = emit_bitcast_ir("ptr", "i64")

expect(ir).to_contain("ptrtoint ptr %l0 to i64")
expect(ir.contains("bitcast ptr %l0 to i64")).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/backend/llvm_bitcast_pointer_bool_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering LLVM pointer and boolean bitcast lowering.
- LLVM pointer and boolean bitcast lowering

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
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

- Canonical SPipe generation for source `852183a860e080475a6b93fa0dfbeb3024fb8e98cc9c6e4cf50f336bd0b5ecd4`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `852183a860e080475a6b93fa0dfbeb3024fb8e98cc9c6e4cf50f336bd0b5ecd4`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `852183a860e080475a6b93fa0dfbeb3024fb8e98cc9c6e4cf50f336bd0b5ecd4`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/compiler/backend/llvm_bitcast_pointer_bool_spec.spl
mirror: doc/06_spec/01_unit/compiler/backend/llvm_bitcast_pointer_bool_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/backend/llvm_bitcast_pointer_bool_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/backend/llvm_bitcast_pointer_bool_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/backend/llvm_bitcast_pointer_bool_spec.spl:32:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'preserves an i1 value through native integer before pointer conversion' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/backend/llvm_bitcast_pointer_bool_spec.spl:44:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'compares a pointer against null when producing i1' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/backend/llvm_bitcast_pointer_bool_spec.spl:53:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'uses inttoptr for an integer to pointer conversion' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

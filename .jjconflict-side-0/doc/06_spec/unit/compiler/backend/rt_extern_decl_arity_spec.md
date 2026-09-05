# Rt Extern Decl Arity Specification

> Tests covering rt_file_open extern declaration arity (repro), adjacent extern declarations do not regress to the 3-arg form (generalization).

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Rt Extern Decl Arity Specification

## Scenarios

### rt_file_open extern declaration arity (repro)

#### llvm_backend.spl declares rt_file_open with the 4-arg (ptr,len,ptr,len) ABI

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- llvm_backend.spl declares rt_file_open with the 4-arg (ptr,len,ptr,len) ABI


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("llvm_backend.spl declares rt_file_open with the 4-arg (ptr,len,ptr,len) ABI")
val src = source_of("src/compiler/70.backend/backend/llvm_backend.spl")
expect(src).to_contain("declare i32 @rt_file_open(ptr, i64, ptr, i64)")
```

</details>

#### llvm_lib_translate.spl declares rt_file_open with the 4-arg (ptr,len,ptr,len) ABI

- llvm_lib_translate.spl declares rt_file_open with the 4-arg (ptr,len,ptr,len) ABI


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("llvm_lib_translate.spl declares rt_file_open with the 4-arg (ptr,len,ptr,len) ABI")
val src = source_of("src/compiler/70.backend/backend/llvm_lib_translate.spl")
expect(src).to_contain("\"rt_file_open\", llvm_function_type(i32_ty, [ptr_ty, i64_ty, ptr_ty, i64_ty], false)")
```

</details>

### adjacent extern declarations do not regress to the 3-arg form (generalization)

#### neither backend carries the old 3-arg rt_file_open declaration

- neither backend carries the old 3-arg rt_file_open declaration


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("neither backend carries the old 3-arg rt_file_open declaration")
val a = source_of("src/compiler/70.backend/backend/llvm_backend.spl")
val b = source_of("src/compiler/70.backend/backend/llvm_lib_translate.spl")
assert_false(a.contains("@rt_file_open(ptr, i64, i32)"))
assert_false(b.contains("\"rt_file_open\", llvm_function_type(i32_ty, [ptr_ty, i64_ty, i32_ty]"))
```

</details>

#### both backends actually declare rt_file_open (the checks above are not vacuous)

- both backends actually declare rt_file_open (the checks above are not vacuous)


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("both backends actually declare rt_file_open (the checks above are not vacuous)")
val a = source_of("src/compiler/70.backend/backend/llvm_backend.spl")
val b = source_of("src/compiler/70.backend/backend/llvm_lib_translate.spl")
assert_true(a.contains("rt_file_open"))
assert_true(b.contains("rt_file_open"))
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/unit/compiler/backend/rt_extern_decl_arity_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering rt_file_open extern declaration arity (repro), adjacent extern declarations do not regress to the 3-arg form (generalization).
- rt_file_open extern declaration arity (repro)
- adjacent extern declarations do not regress to the 3-arg form (generalization)

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

- Canonical SPipe generation for source `6d35d730f877781af6949572a9d91a8973cc9b3e19439e68d601ef34efb8e5a6`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `6d35d730f877781af6949572a9d91a8973cc9b3e19439e68d601ef34efb8e5a6`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `6d35d730f877781af6949572a9d91a8973cc9b3e19439e68d601ef34efb8e5a6`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/compiler/backend/rt_extern_decl_arity_spec.spl
mirror: doc/06_spec/unit/compiler/backend/rt_extern_decl_arity_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/compiler/backend/rt_extern_decl_arity_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/compiler/backend/rt_extern_decl_arity_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/compiler/backend/rt_extern_decl_arity_spec.spl:21:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'llvm_backend.spl declares rt_file_open with the 4-arg (ptr,len,ptr,len) ABI' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/backend/rt_extern_decl_arity_spec.spl:27:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'llvm_lib_translate.spl declares rt_file_open with the 4-arg (ptr,len,ptr,len) ABI' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/backend/rt_extern_decl_arity_spec.spl:34:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'neither backend carries the old 3-arg rt_file_open declaration' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

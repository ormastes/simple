# Extern Text Arg Marshalling Completeness Specification

> Tests covering every text-taking runtime symbol is in the codegen text-arg expansion tables.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Extern Text Arg Marshalling Completeness Specification

## Scenarios

### every text-taking runtime symbol is in the codegen text-arg expansion tables

#### actually classified symbols — a zero-symbol scan is a broken scan, not a pass

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- actually classified symbols — a zero-symbol scan is a broken scan, not a pass
- Run the static cross-check of runtime C signatures against the codegen tables
- the receipt must state a non-zero count of text-taking symbols


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("actually classified symbols — a zero-symbol scan is a broken scan, not a pass")
step("Run the static cross-check of runtime C signatures against the codegen tables")
val out = scan_output()

step("the receipt must state a non-zero count of text-taking symbols")
expect(out).to_contain("text-taking symbol(s)")
expect(out).not_to_contain("SCANNED 0 text-taking symbol(s)")
expect(out).not_to_contain("ERROR missing codegen tables")
```

</details>

#### detects the class on the JIT path: no symbol may be missing from the cranelift table

- detects the class on the JIT path: no symbol may be missing from the cranelift table
- Run the scan
- a MISSING_INSTR line is a symbol the JIT will call with an unexpanded text handle


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("detects the class on the JIT path: no symbol may be missing from the cranelift table")
step("Run the scan")
val out = scan_output()

step("a MISSING_INSTR line is a symbol the JIT will call with an unexpanded text handle")
expect(out).not_to_contain("MISSING_INSTR")
```

</details>

#### detects the class on the AOT path: no symbol may be missing from the LLVM table

- detects the class on the AOT path: no symbol may be missing from the LLVM table
- Run the scan
- a MISSING_LLVM line is the same defect in natively built binaries


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("detects the class on the AOT path: no symbol may be missing from the LLVM table")
step("Run the scan")
val out = scan_output()

step("a MISSING_LLVM line is the same defect in natively built binaries")
expect(out).not_to_contain("MISSING_LLVM")
```

</details>

#### names the symbols that started this: the rt_io_file_* text-taking members

- names the symbols that started this: the rt_io_file_* text-taking members
- Run the scan
- open/exists/delete are the three members whose C ABI takes (path_ptr, path_len)


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("names the symbols that started this: the rt_io_file_* text-taking members")
step("Run the scan")
val out = scan_output()

step("open/exists/delete are the three members whose C ABI takes (path_ptr, path_len)")
expect(out).not_to_contain("rt_io_file_open")
expect(out).not_to_contain("rt_io_file_exists")
expect(out).not_to_contain("rt_io_file_delete")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/io/extern_text_arg_marshalling_completeness_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering every text-taking runtime symbol is in the codegen text-arg expansion tables.
- every text-taking runtime symbol is in the codegen text-arg expansion tables

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

- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `228c38adb692dde27321bfc578efa56e74b4ec38d9d5cdcd5b37ba32bb40fadb`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `228c38adb692dde27321bfc578efa56e74b4ec38d9d5cdcd5b37ba32bb40fadb`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `228c38adb692dde27321bfc578efa56e74b4ec38d9d5cdcd5b37ba32bb40fadb`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/io/extern_text_arg_marshalling_completeness_spec.spl
mirror: doc/06_spec/01_unit/lib/io/extern_text_arg_marshalling_completeness_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/io/extern_text_arg_marshalling_completeness_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/io/extern_text_arg_marshalling_completeness_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/io/extern_text_arg_marshalling_completeness_spec.spl:53:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'actually classified symbols — a zero-symbol scan is a broken scan, not a pass' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/io/extern_text_arg_marshalling_completeness_spec.spl:64:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'detects the class on the JIT path: no symbol may be missing from the cranelift table' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/io/extern_text_arg_marshalling_completeness_spec.spl:73:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'detects the class on the AOT path: no symbol may be missing from the LLVM table' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

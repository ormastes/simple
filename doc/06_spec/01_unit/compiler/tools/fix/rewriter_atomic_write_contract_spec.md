# Rewriter Atomic Write Contract Specification

> Tests covering standalone source rewriter persistence.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Rewriter Atomic Write Contract Specification

## Scenarios

### standalone source rewriter persistence

#### keeps accessor fixes atomic and fail closed

- keeps accessor fixes atomic and fail closed
   - Expected: source does not contain `file_write(path, fr.source)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("keeps accessor fixes atomic and fail closed")
val source = rt_file_read_text("src/compiler/90.tools/fix/accessor_fix_main.spl") ?? ""

expect(source).to_contain("file_atomic_write(path, fr.source)")
expect(source).to_contain("fn main() -> i64")
expect(source).to_contain("return 1")
expect(source.contains("file_write(path, fr.source)")).to_equal(false)
```

</details>

#### distinguishes unchanged, written, and failed bare-import fixes

- distinguishes unchanged, written, and failed bare-import fixes
   - Expected: source does not contain `file_write(path, result)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("distinguishes unchanged, written, and failed bare-import fixes")
val source = rt_file_read_text("src/compiler/90.tools/fix/imports.spl") ?? ""

expect(source).to_contain("fn fix_file(path: text) -> i64")
expect(source).to_contain("file_atomic_write(path, result)")
expect(source).to_contain("return -1")
expect(source).to_contain("if status < 0:\n            print \"Error: failed to write \{file}\"\n            exit(1)")
expect(source.contains("file_write(path, result)")).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/tools/fix/rewriter_atomic_write_contract_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering standalone source rewriter persistence.
- standalone source rewriter persistence

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

- Canonical SPipe generation for source `ff3461491f8ca73ce0f65b4dd8a80e8bf24a2a11474cc982630a8a655d3e8579`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `ff3461491f8ca73ce0f65b4dd8a80e8bf24a2a11474cc982630a8a655d3e8579`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `ff3461491f8ca73ce0f65b4dd8a80e8bf24a2a11474cc982630a8a655d3e8579`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **84/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/compiler/tools/fix/rewriter_atomic_write_contract_spec.spl
mirror: doc/06_spec/01_unit/compiler/tools/fix/rewriter_atomic_write_contract_spec.md (current)
findings: 5 blockers: 1
  narrative=100 structure=100 oracle=50
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=84; blocker cap makes effective=49
doc/06_spec/01_unit/compiler/tools/fix/rewriter_atomic_write_contract_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/tools/fix/rewriter_atomic_write_contract_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/tools/fix/rewriter_atomic_write_contract_spec.spl:1:1: blocker SSDOC-ORA-002 [oracle] (-50): scenario relies on source-text inspection as system evidence
  why: Source presence or self-created arithmetic does not demonstrate production behavior.
  improve: Observe runtime behavior or a stable generated artifact instead.
test/01_unit/compiler/tools/fix/rewriter_atomic_write_contract_spec.spl:13:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps accessor fixes atomic and fail closed' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/tools/fix/rewriter_atomic_write_contract_spec.spl:23:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'distinguishes unchanged, written, and failed bare-import fixes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

# Regeneration Specification

> Tests covering Lean Regeneration.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Regeneration Specification

## Scenarios

### Lean Regeneration

#### module generators

#### regenerates async compile output

- regenerates async compile output
   - Expected: lean_code does not contain `sorry`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("regenerates async compile output")
val lean_code = regen_async.regenerate_async_compile()
expect(lean_code).to_contain("inductive Effect")
expect(lean_code).to_contain("theorem append_safe")
expect(lean_code).to_contain("theorem wait_detected")
expect(lean_code.contains("sorry")).to_equal(false)
```

</details>

#### regenerates GC borrow output

- regenerates GC borrow output
   - Expected: lean_code does not contain `sorry`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("regenerates GC borrow output")
val lean_code = regen_gc.regenerate_gc_manual_borrow()
expect(lean_code).to_contain("structure GcState")
expect(lean_code).to_contain("theorem borrow_preserves")
expect(lean_code).to_contain("theorem collect_preserves")
expect(lean_code.contains("sorry")).to_equal(false)
```

</details>

#### regenerates memory capability output

- regenerates memory capability output


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("regenerates memory capability output")
val lean_code = regen_mem_cap.regenerate_memory_capabilities()
expect(lean_code).to_contain("inductive RefCapability")
expect(lean_code).to_contain("def canConvert")
expect(lean_code).to_contain("theorem conversion_is_safe")
```

</details>

#### regenerate_all

#### returns all expected file entries

- returns all expected file entries
   - Expected: files.len() equals `15`
   - Expected: files.has("src/verification/async_compile/src/AsyncCompile.lean") is true
   - Expected: files.has("src/verification/gc_manual_borrow/src/GcManualBorrow.lean") is true
   - Expected: async_file contains `theorem append_safe`
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("returns all expected file entries")
val files = regen.regenerate_all()
expect(files.len()).to_equal(15)
expect(files.has("src/verification/async_compile/src/AsyncCompile.lean")).to_equal(true)
expect(files.has("src/verification/gc_manual_borrow/src/GcManualBorrow.lean")).to_equal(true)

if files.has("src/verification/async_compile/src/AsyncCompile.lean"):
    val async_file = files.get("src/verification/async_compile/src/AsyncCompile.lean")
    expect(async_file.contains("theorem append_safe")).to_equal(true)
else:
    expect(false).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/verification/regeneration_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Lean Regeneration.
- Lean Regeneration

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

- `REQ-SSPEC-COMPILER`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `00e14b6cf5f2a140b53602f714dee82bf81ba027857873e1e6190b513aaabbe3`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `00e14b6cf5f2a140b53602f714dee82bf81ba027857873e1e6190b513aaabbe3`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `00e14b6cf5f2a140b53602f714dee82bf81ba027857873e1e6190b513aaabbe3`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/01_unit/compiler/verification/regeneration_spec.spl
mirror: doc/06_spec/01_unit/compiler/verification/regeneration_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/verification/regeneration_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/verification/regeneration_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/verification/regeneration_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/verification/regeneration_spec.spl:15:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'regenerates async compile output' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/verification/regeneration_spec.spl:24:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'regenerates GC borrow output' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/verification/regeneration_spec.spl:33:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'regenerates memory capability output' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

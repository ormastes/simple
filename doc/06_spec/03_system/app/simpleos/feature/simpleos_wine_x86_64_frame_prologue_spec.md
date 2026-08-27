# Simpleos Wine X86 64 Frame Prologue Specification

> Tests covering SimpleOS Wine x86_64 frame prologue decode, REQ-018: bounded known-console process dispatch plan.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Simpleos Wine X86 64 Frame Prologue Specification

## Scenarios

### SimpleOS Wine x86_64 frame prologue decode

### REQ-018: bounded known-console process dispatch plan

#### classifies frame-pointer prologue and epilogue forms before dispatch handoff

- frame-pointer prologue and epilogue forms are classified before dispatch handoff
   - Expected: wine_x86_64_instruction_at(data, 0) equals `push-rbp`
   - Expected: wine_x86_64_instruction_len_at(data, 0) equals `1`
   - Expected: wine_x86_64_instruction_at(data, 1) equals `mov-rbp-rsp`
   - Expected: wine_x86_64_instruction_len_at(data, 1) equals `3`
   - Expected: wine_x86_64_instruction_at(data, 12) equals `pop-rbp`
   - Expected: wine_x86_64_instruction_len_at(data, 12) equals `1`
   - Expected: scan.ok is true
   - Expected: scan.state equals `ready`
   - Expected: scan.end_offset equals `14`
   - Expected: scan.instruction_count equals `6`
   - Expected: scan.last_offset equals `13`
   - Expected: scan.last_instruction equals `ret`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-018
# @req REQ-SSPEC-SYSTEM
step("frame-pointer prologue and epilogue forms are classified before dispatch handoff")
val data = _frame_prologue_bytes()
expect(wine_x86_64_instruction_at(data, 0)).to_equal("push-rbp")
expect(wine_x86_64_instruction_len_at(data, 0)).to_equal(1)
expect(wine_x86_64_instruction_at(data, 1)).to_equal("mov-rbp-rsp")
expect(wine_x86_64_instruction_len_at(data, 1)).to_equal(3)
expect(wine_x86_64_instruction_at(data, 12)).to_equal("pop-rbp")
expect(wine_x86_64_instruction_len_at(data, 12)).to_equal(1)
val scan = wine_x86_64_scan_window(data, 0, 14, 8)
expect(scan.ok).to_equal(true)
expect(scan.state).to_equal("ready")
expect(scan.end_offset).to_equal(14)
expect(scan.instruction_count).to_equal(6)
expect(scan.last_offset).to_equal(13)
expect(scan.last_instruction).to_equal("ret")
```

</details>

#### should classify wide imm32 stack allocation before dispatch handoff

- should classify wide imm32 stack allocation before dispatch handoff
   - Expected: wine_x86_64_instruction_at(data, 4) equals `sub-rsp-imm32`
   - Expected: wine_x86_64_instruction_len_at(data, 4) equals `7`
   - Expected: wine_x86_64_instruction_at(data, 11) equals `add-rsp-imm32`
   - Expected: wine_x86_64_instruction_len_at(data, 11) equals `7`
   - Expected: scan.ok is true
   - Expected: scan.state equals `ready`
   - Expected: scan.end_offset equals `20`
   - Expected: scan.instruction_count equals `6`
   - Expected: scan.last_offset equals `19`
   - Expected: scan.last_instruction equals `ret`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should classify wide imm32 stack allocation before dispatch handoff")
val data = _wide_stack_frame_prologue_bytes()
expect(wine_x86_64_instruction_at(data, 4)).to_equal("sub-rsp-imm32")
expect(wine_x86_64_instruction_len_at(data, 4)).to_equal(7)
expect(wine_x86_64_instruction_at(data, 11)).to_equal("add-rsp-imm32")
expect(wine_x86_64_instruction_len_at(data, 11)).to_equal(7)
val scan = wine_x86_64_scan_window(data, 0, 20, 8)
expect(scan.ok).to_equal(true)
expect(scan.state).to_equal("ready")
expect(scan.end_offset).to_equal(20)
expect(scan.instruction_count).to_equal(6)
expect(scan.last_offset).to_equal(19)
expect(scan.last_instruction).to_equal("ret")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/app/simpleos/feature/simpleos_wine_x86_64_frame_prologue_spec.spl` |
| Updated | 2026-08-27 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering SimpleOS Wine x86_64 frame prologue decode, REQ-018: bounded known-console process dispatch plan.
- SimpleOS Wine x86_64 frame prologue decode
- REQ-018: bounded known-console process dispatch plan

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

- `REQ-SSPEC-SYSTEM`
- `REQ-018`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `87c9a6b2753bd0fd553e8131061be7a6083e175d8cce1ec8a09a9cb9bb9ddfc0`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `87c9a6b2753bd0fd553e8131061be7a6083e175d8cce1ec8a09a9cb9bb9ddfc0`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `87c9a6b2753bd0fd553e8131061be7a6083e175d8cce1ec8a09a9cb9bb9ddfc0`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **84/100**; effective score: **84/100**; blockers: **0**.

SSpec documentization score: 84/100
source: test/03_system/app/simpleos/feature/simpleos_wine_x86_64_frame_prologue_spec.spl
mirror: doc/06_spec/03_system/app/simpleos/feature/simpleos_wine_x86_64_frame_prologue_spec.md (current)
findings: 7 blockers: 0
  narrative=80 structure=95 oracle=70
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/app/simpleos/feature/simpleos_wine_x86_64_frame_prologue_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/app/simpleos/feature/simpleos_wine_x86_64_frame_prologue_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/app/simpleos/feature/simpleos_wine_x86_64_frame_prologue_spec.spl:1:1: warning SSDOC-NAR-001 [narrative] (-20): missing authored purpose and audience
  why: Readers need scope, audience, and intent before executable detail.
  improve: Add authored purpose, scope, and audience facts.
test/03_system/app/simpleos/feature/simpleos_wine_x86_64_frame_prologue_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 11 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/app/simpleos/feature/simpleos_wine_x86_64_frame_prologue_spec.spl:62:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'classifies frame-pointer prologue and epilogue forms before dispatch handoff' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/app/simpleos/feature/simpleos_wine_x86_64_frame_prologue_spec.spl:81:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should classify wide imm32 stack allocation before dispatch handoff' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/simpleos/feature/simpleos_wine_x86_64_frame_prologue_spec.spl:81:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should classify wide imm32 stack allocation before dispatch handoff' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

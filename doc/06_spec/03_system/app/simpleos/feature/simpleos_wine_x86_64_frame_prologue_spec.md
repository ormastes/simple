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

#### should classify frame-pointer prologue and epilogue forms before dispatch handoff
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
| Updated | 2026-08-26 |
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

- Canonical SPipe generation for source `23f978057b7e70cb457c3141cf03a11d0c58620a59ef00068a3610fc3e3e4cae`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `23f978057b7e70cb457c3141cf03a11d0c58620a59ef00068a3610fc3e3e4cae`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `23f978057b7e70cb457c3141cf03a11d0c58620a59ef00068a3610fc3e3e4cae`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **80/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/03_system/app/simpleos/feature/simpleos_wine_x86_64_frame_prologue_spec.spl
mirror: doc/06_spec/03_system/app/simpleos/feature/simpleos_wine_x86_64_frame_prologue_spec.md (current)
findings: 8 blockers: 1
  narrative=100 structure=80 oracle=70
  traceability=60 evidence=90 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=80; blocker cap makes effective=49
doc/06_spec/03_system/app/simpleos/feature/simpleos_wine_x86_64_frame_prologue_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/app/simpleos/feature/simpleos_wine_x86_64_frame_prologue_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/app/simpleos/feature/simpleos_wine_x86_64_frame_prologue_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 5 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/app/simpleos/feature/simpleos_wine_x86_64_frame_prologue_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 1 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/03_system/app/simpleos/feature/simpleos_wine_x86_64_frame_prologue_spec.spl:62:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'should classify frame-pointer prologue and epilogue forms before dispatch handoff' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/03_system/app/simpleos/feature/simpleos_wine_x86_64_frame_prologue_spec.spl:62:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should classify frame-pointer prologue and epilogue forms before dispatch handoff' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/simpleos/feature/simpleos_wine_x86_64_frame_prologue_spec.spl:82:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should classify wide imm32 stack allocation before dispatch handoff' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/simpleos/feature/simpleos_wine_x86_64_frame_prologue_spec.spl:82:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should classify wide imm32 stack allocation before dispatch handoff' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

# Practice Runner Specification

> Tests covering T32 Practice Runner.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Practice Runner Specification

## Scenarios

### T32 Practice Runner

#### formats DO command

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- formats DO command
   - Expected: cmd equals `DO scripts/startup.cmm`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("formats DO command")
val script = "scripts/startup.cmm"
val cmd = "DO {script}"
expect(cmd).to_equal("DO scripts/startup.cmm")
```

</details>

#### formats DO with arguments

- formats DO with arguments
   - Expected: cmd equals `DO scripts/flash.cmm 0x08000000 firmware.elf`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("formats DO with arguments")
val script = "scripts/flash.cmm"
val args = ["0x08000000", "firmware.elf"]
val args_str = args.join(" ")
val cmd = "DO {script} {args_str}"
expect(cmd).to_equal("DO scripts/flash.cmm 0x08000000 firmware.elf")
```

</details>

#### formats PRACTICE.STATE query

- formats PRACTICE.STATE query
   - Expected: cmd equals `PRACTICE.STATE()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("formats PRACTICE.STATE query")
val cmd = "PRACTICE.STATE()"
expect(cmd).to_equal("PRACTICE.STATE()")
```

</details>

#### formats EVAL expression

- formats EVAL expression
   - Expected: cmd equals `EVAL Register(PC)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("formats EVAL expression")
val expr = "Register(PC)"
val cmd = "EVAL {expr}"
expect(cmd).to_equal("EVAL Register(PC)")
```

</details>

#### formats InterCom execute

- formats InterCom execute
   - Expected: cmd equals `InterCom.execute ARM_A53_0 SYStem.Mode.Prepare`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("formats InterCom execute")
val target = "ARM_A53_0"
val inner_cmd = "SYStem.Mode.Prepare"
val cmd = "InterCom.execute {target} {inner_cmd}"
expect(cmd).to_equal("InterCom.execute ARM_A53_0 SYStem.Mode.Prepare")
```

</details>

#### formats WinPrint command

- formats WinPrint command
   - Expected: cmd equals `WinPrint.Break.List`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("formats WinPrint command")
val window = "Break.List"
val cmd = "WinPrint.{window}"
expect(cmd).to_equal("WinPrint.Break.List")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/debug/trace32/practice_runner_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering T32 Practice Runner.
- T32 Practice Runner

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

- Canonical SPipe generation for source `5274778ec9b5408dd5061176eb26fb5f38d45f9d9f07643503bb60db0444aa0b`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `5274778ec9b5408dd5061176eb26fb5f38d45f9d9f07643503bb60db0444aa0b`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `5274778ec9b5408dd5061176eb26fb5f38d45f9d9f07643503bb60db0444aa0b`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/debug/trace32/practice_runner_spec.spl
mirror: doc/06_spec/01_unit/lib/debug/trace32/practice_runner_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/debug/trace32/practice_runner_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/debug/trace32/practice_runner_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/debug/trace32/practice_runner_spec.spl:11:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'formats DO command' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/debug/trace32/practice_runner_spec.spl:18:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'formats DO with arguments' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/debug/trace32/practice_runner_spec.spl:27:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'formats PRACTICE.STATE query' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

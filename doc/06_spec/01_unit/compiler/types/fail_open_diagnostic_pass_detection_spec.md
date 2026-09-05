# Fail Open Diagnostic Pass Detection Specification

> Tests covering no driver warn-pass may compute a diagnostic it cannot report.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Fail Open Diagnostic Pass Detection Specification

## Scenarios

### no driver warn-pass may compute a diagnostic it cannot report

#### routes typecheck diagnostics to the compile context, not only to the log

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- routes typecheck diagnostics to the compile context, not only to the log
- The typecheck pass must have a severity projection, exactly as the safety pass does
- Deny severity must actually reach ctx.add_error — this is the line whose absence WAS the bug
- Warn severity must reach ctx.add_warning, so the migration window is visible rather than silent


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("routes typecheck diagnostics to the compile context, not only to the log")
step("The typecheck pass must have a severity projection, exactly as the safety pass does")
assert_true(count_in(PASSES, "typecheck_pass_severity") > 0)

step("Deny severity must actually reach ctx.add_error — this is the line whose absence WAS the bug")
assert_true(count_in(PASSES, "ctx.add_error") > 0)

step("Warn severity must reach ctx.add_warning, so the migration window is visible rather than silent")
assert_true(count_in(PASSES, "ctx.add_warning") > 0)
```

</details>

#### does not gate the typecheck pass behind a log-only flag alone

- does not gate the typecheck pass behind a log-only flag alone
- Reaching enforcement must not require SIMPLE_TYPECHECK_WARN=1; a log flag can only ever produce log output
- The safety pass established this exact pattern; both must use it, or the two will drift apart


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("does not gate the typecheck pass behind a log-only flag alone")
step("Reaching enforcement must not require SIMPLE_TYPECHECK_WARN=1; a log flag can only ever produce log output")
assert_true(count_in(LOWERING, "typecheck_enforcing") > 0)

step("The safety pass established this exact pattern; both must use it, or the two will drift apart")
assert_true(count_in(LOWERING, "safety_enforcing") > 0)
```

</details>

#### keeps every severity ladder in agreement about the strictest profile

- keeps every severity ladder in agreement about the strictest profile
- A profile ladder that maps its STRONGEST rung to Advisory would silently disable the pass for the users who asked for the most checking
- Both projections must name critical and verified as Deny
- Advisory must remain the default, so an unset profile cannot turn a green build red without an explicit opt-in


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("keeps every severity ladder in agreement about the strictest profile")
step("A profile ladder that maps its STRONGEST rung to Advisory would silently disable the pass for the users who asked for the most checking")
step("Both projections must name critical and verified as Deny")
val sev = "src/compiler/80.driver/driver_typecheck_severity.spl"
assert_true(count_in(sev, "TypecheckPassSeverity.Deny") > 0)
assert_true(count_in(sev, "verified") > 0)

step("Advisory must remain the default, so an unset profile cannot turn a green build red without an explicit opt-in")
assert_true(count_in(sev, "TypecheckPassSeverity.Advisory") > 0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/types/fail_open_diagnostic_pass_detection_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering no driver warn-pass may compute a diagnostic it cannot report.
- no driver warn-pass may compute a diagnostic it cannot report

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

- Canonical SPipe generation for source `d129f2b16c8d28bcb166a9c4eabf7f7ea58052064c15e949d3a756c125df54ab`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `d129f2b16c8d28bcb166a9c4eabf7f7ea58052064c15e949d3a756c125df54ab`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `d129f2b16c8d28bcb166a9c4eabf7f7ea58052064c15e949d3a756c125df54ab`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/compiler/types/fail_open_diagnostic_pass_detection_spec.spl
mirror: doc/06_spec/01_unit/compiler/types/fail_open_diagnostic_pass_detection_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/types/fail_open_diagnostic_pass_detection_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/types/fail_open_diagnostic_pass_detection_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/types/fail_open_diagnostic_pass_detection_spec.spl:59:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'routes typecheck diagnostics to the compile context, not only to the log' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/types/fail_open_diagnostic_pass_detection_spec.spl:71:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'does not gate the typecheck pass behind a log-only flag alone' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/types/fail_open_diagnostic_pass_detection_spec.spl:80:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps every severity ladder in agreement about the strictest profile' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

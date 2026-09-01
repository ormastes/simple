# Interp Double Exec Specification

> Tests covering Double execution bug.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Interp Double Exec Specification

## Scenarios

### Double execution bug

#### guard prevents multiple executions

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- guard prevents multiple executions
   - Expected: _test_guard_single_call() equals `1`
   - Expected: _test_guard_is_set() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("guard prevents multiple executions")
expect(_test_guard_single_call()).to_equal(1)
expect(_test_guard_is_set()).to_equal(true)
```

</details>

#### calling guarded_main again is a no-op

- calling guarded_main again is a no-op
   - Expected: _test_guard_multiple_calls() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("calling guarded_main again is a no-op")
expect(_test_guard_multiple_calls()).to_equal(1)
```

</details>

#### without guard, count increments each call

- without guard, count increments each call
   - Expected: _test_unguarded_calls() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("without guard, count increments each call")
expect(_test_unguarded_calls()).to_equal(2)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Bug Regression |
| Status | Active |
| Source | `test/unit/bugs/interp_double_exec_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Double execution bug.
- Double execution bug

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

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `58043310aaf56d28bd4a76daa788653c2fa02cd777506f8fe00fe19ea661907f`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `58043310aaf56d28bd4a76daa788653c2fa02cd777506f8fe00fe19ea661907f`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `58043310aaf56d28bd4a76daa788653c2fa02cd777506f8fe00fe19ea661907f`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/unit/bugs/interp_double_exec_spec.spl
mirror: doc/06_spec/unit/bugs/interp_double_exec_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/bugs/interp_double_exec_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/bugs/interp_double_exec_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/bugs/interp_double_exec_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 3 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/bugs/interp_double_exec_spec.spl:53:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'guard prevents multiple executions' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/bugs/interp_double_exec_spec.spl:59:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'calling guarded_main again is a no-op' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/bugs/interp_double_exec_spec.spl:64:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'without guard, count increments each call' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

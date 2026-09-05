# Startup No Dynsmf On Help Specification

> Tests covering app root minimal launch dispatcher.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Startup No Dynsmf On Help Specification

## Scenarios

### app root minimal launch dispatcher

#### control: --dynsmf-status DOES initialize dynSMF (trace line present)

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- control: --dynsmf-status DOES initialize dynSMF (trace line present)
   - Expected: code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("control: --dynsmf-status DOES initialize dynSMF (trace line present)")
val (out, err, code) = run_app_root_traced("--dynsmf-status")
expect(code).to_equal(0)
expect(out).to_contain("dynsmf-trace: startup_session_init")
```

</details>

#### no-op startup does not initialize dynSMF

- no-op startup does not initialize dynSMF
   - Expected: code equals `0`
   - Expected: out equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("no-op startup does not initialize dynSMF")
val (out, err, code) = run_app_root_traced("")
expect(code).to_equal(0)
expect(out).to_equal("")
```

</details>

#### --help does not initialize dynSMF

- --help does not initialize dynSMF
   - Expected: code equals `0`
   - Expected: out does not contain `dynsmf-trace: startup_session_init`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("--help does not initialize dynSMF")
val (out, err, code) = run_app_root_traced("--help")
expect(code).to_equal(0)
expect(out).to_contain("USAGE:")
expect(out.contains("dynsmf-trace: startup_session_init")).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/app/simple/startup_no_dynsmf_on_help_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering app root minimal launch dispatcher.
- app root minimal launch dispatcher

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

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `c3c3b17964d594d6b7b688edac44ab219f0436a44c2c8ec5c3b6ae32aa7bcc2e`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `c3c3b17964d594d6b7b688edac44ab219f0436a44c2c8ec5c3b6ae32aa7bcc2e`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `c3c3b17964d594d6b7b688edac44ab219f0436a44c2c8ec5c3b6ae32aa7bcc2e`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/03_system/app/simple/startup_no_dynsmf_on_help_spec.spl
mirror: doc/06_spec/03_system/app/simple/startup_no_dynsmf_on_help_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/app/simple/startup_no_dynsmf_on_help_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/app/simple/startup_no_dynsmf_on_help_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/app/simple/startup_no_dynsmf_on_help_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 3 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/app/simple/startup_no_dynsmf_on_help_spec.spl:32:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'control: --dynsmf-status DOES initialize dynSMF (trace line present)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/app/simple/startup_no_dynsmf_on_help_spec.spl:39:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'no-op startup does not initialize dynSMF' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/app/simple/startup_no_dynsmf_on_help_spec.spl:46:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario '--help does not initialize dynSMF' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

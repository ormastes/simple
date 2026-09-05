# Signal Classification Subprocess Specification

> Tests covering signal classification (subprocess path).

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Signal Classification Subprocess Specification

## Scenarios

### signal classification (subprocess path)

#### classifies an unbudgeted SIGKILL (137) as CRASHED with failed: 1

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- classifies an unbudgeted SIGKILL (137) as CRASHED with failed: 1


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("classifies an unbudgeted SIGKILL (137) as CRASHED with failed: 1")
val r = make_result_from_output("/tmp/no_such_spec.spl", "", "", 137, 10, 60)
assert_equal(r.failed, 1)
assert_contains(r.error, "CRASHED")
assert_equal(r.timed_out, false)
```

</details>

#### classifies SIGSEGV (139) as CRASHED with failed: 1

- classifies SIGSEGV (139) as CRASHED with failed: 1


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("classifies SIGSEGV (139) as CRASHED with failed: 1")
val r = make_result_from_output("/tmp/no_such_spec.spl", "", "", 139, 10, 60)
assert_equal(r.failed, 1)
assert_contains(r.error, "CRASHED")
```

</details>

#### classifies SIGABRT (134) as CRASHED with failed: 1

- classifies SIGABRT (134) as CRASHED with failed: 1


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("classifies SIGABRT (134) as CRASHED with failed: 1")
val r = make_result_from_output("/tmp/no_such_spec.spl", "", "", 134, 10, 60)
assert_equal(r.failed, 1)
assert_contains(r.error, "CRASHED")
```

</details>

#### does not scrape a green stdout summary out of a killed child

- does not scrape a green stdout summary out of a killed child


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does not scrape a green stdout summary out of a killed child")
# The exact silent-green shape: the child printed a full pass summary,
# then died by SIGKILL. Its self-reported counts must not survive.
val out = "Results: 5 total, 5 passed, 0 failed"
val r = make_result_from_output("/tmp/no_such_spec.spl", out, "", 137, 10, 60)
assert_equal(r.passed, 0)
assert_equal(r.failed, 1)
assert_contains(r.error, "CRASHED")
```

</details>

#### keeps SIGTERM (143) unverified with failed: 0

- keeps SIGTERM (143) unverified with failed: 0


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps SIGTERM (143) unverified with failed: 0")
# earlyoom SIGTERMs `simple` on this host, so a SIGTERM says nothing
# about the code under test. Never a failure -- but the non-empty error
# keeps is_ok() false so it cannot be swallowed into a green run.
val r = make_result_from_output("/tmp/no_such_spec.spl", "", "", 143, 10, 60)
assert_equal(r.failed, 0)
assert_contains(r.error, "TERMINATED")
assert_false(r.error == "")
```

</details>

#### keeps 144 in the unverified class

- keeps 144 in the unverified class


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps 144 in the unverified class")
val r = make_result_from_output("/tmp/no_such_spec.spl", "", "", 144, 10, 60)
assert_equal(r.failed, 0)
assert_false(r.error == "")
```

</details>

#### maps -1 with TIMEOUT evidence to an unverified TIMEOUT

- maps -1 with TIMEOUT evidence to an unverified TIMEOUT


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("maps -1 with TIMEOUT evidence to an unverified TIMEOUT")
val r = make_result_from_output("/tmp/no_such_spec.spl", "", "\nTIMEOUT\n", -1, 10, 60)
assert_equal(r.failed, 0)
assert_equal(r.timed_out, true)
assert_contains(r.error, "TIMEOUT")
```

</details>

#### never returns an empty error for any signal death

- never returns an empty error for any signal death


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("never returns an empty error for any signal death")
for code in [137, 139, 134, 143, 144]:
    val r = make_result_from_output("/tmp/no_such_spec.spl", "", "", code, 10, 60)
    assert_false(r.error == "")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/01_unit/test_runner/signal_classification_subprocess_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering signal classification (subprocess path).
- signal classification (subprocess path)

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
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

- Canonical SPipe generation for source `2889f6c9e74a1c21cf9d2258aa3885119dd30f627710cfda41f0688211d84d25`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `2889f6c9e74a1c21cf9d2258aa3885119dd30f627710cfda41f0688211d84d25`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `2889f6c9e74a1c21cf9d2258aa3885119dd30f627710cfda41f0688211d84d25`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/test_runner/signal_classification_subprocess_spec.spl
mirror: doc/06_spec/01_unit/test_runner/signal_classification_subprocess_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/test_runner/signal_classification_subprocess_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/test_runner/signal_classification_subprocess_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/test_runner/signal_classification_subprocess_spec.spl:21:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'classifies an unbudgeted SIGKILL (137) as CRASHED with failed: 1' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/test_runner/signal_classification_subprocess_spec.spl:29:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'classifies SIGSEGV (139) as CRASHED with failed: 1' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/test_runner/signal_classification_subprocess_spec.spl:36:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'classifies SIGABRT (134) as CRASHED with failed: 1' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

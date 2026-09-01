# Test Runner Operator Contract

> An operator (or a CI job standing in for one) points `simple test` at a `.spl` fixture — or a directory of them — and trusts the exit code plus the printed console report to decide whether a build is green. This manual is the operator-facing contract for that surface: a genuine failure must exit nonzero and name the failing file, and a genuine pass must exit zero and name the passing file. It also records two currently-open gaps in that contract (a zero-example spec, and a directory scan) so the manual stays honest about what an operator can rely on today. Every scenario below drives the real seed binary end-to-end; nothing is mocked.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Test Runner Operator Contract

An operator (or a CI job standing in for one) points `simple test` at a `.spl` fixture — or a directory of them — and trusts the exit code plus the printed console report to decide whether a build is green. This manual is the operator-facing contract for that surface: a genuine failure must exit nonzero and name the failing file, and a genuine pass must exit zero and name the passing file. It also records two currently-open gaps in that contract (a zero-example spec, and a directory scan) so the manual stays honest about what an operator can rely on today. Every scenario below drives the real seed binary end-to-end; nothing is mocked.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #test-runner-contract |
| Category | Tooling |
| Status | Implemented |
| Source | `test/03_system/app/test_runner/test_runner_contract_system_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

An operator (or a CI job standing in for one) points `simple test` at a
`.spl` fixture — or a directory of them — and trusts the exit code plus the
printed console report to decide whether a build is green. This manual is
the operator-facing contract for that surface: a genuine failure must exit
nonzero and name the failing file, and a genuine pass must exit zero and
name the passing file. It also records two currently-open gaps in that
contract (a zero-example spec, and a directory scan) so the manual stays
honest about what an operator can rely on today. Every scenario below drives
the real seed binary end-to-end; nothing is mocked.

## Related Specifications

- [Single-example failure contract](../../check/test_runner_single_example_failure_contract_spec.spl) — child-summary trust boundary for the minimal wrapper
- [Zero-executed greenwash bug](../../../../08_tracking/bug/test_runner_zero_executed_single_file_greenwash_2026-07-17.md) — fix drafted but not yet landed in committed history as of this writing; see the guardrail scenario below
- [`app.io.mod` interpreter stack-overflow bug](../../../../08_tracking/bug/interp_app_io_mod_import_stack_overflow_2026-07-17.md) — why this spec drives the seed via `std.io_runtime` + a shell `timeout` wrapper instead of `app.io.mod.process_run_timeout`
- [Daemon-startup extern gap](../../../../08_tracking/bug/host_toolchain_seed_pinned_lint_fmt_doccov_unrunnable_2026-07-17.md) — `unknown extern function: rt_cli_arg_count`; why directory scans fall back to an unbounded-feeling direct run (scenario below)

## Scenarios

### Test runner operator contract

#### fails the build when a spec has a genuine expectation failure

**Manual warnings:**
- invalid manual visibility metadata: # @manual_section: Single-file pass/fail contract (expected show, folded, detail, or skip)


- fails the build when a spec has a genuine expectation failure
   - Protocol capture: after_step
- Run the seed runner on the deliberately-failing font-evidence fixture
   - Protocol capture: after_step
- Confirm the build fails closed and names the failing fixture
   - Protocol capture: after_step
   - Evidence: protocol response verified by 1 expected check
   - Expected: code equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("fails the build when a spec has a genuine expectation failure")
"""The operator runs the runner against a fixture carrying one deliberately-red expectation. CI must see a nonzero exit and a `FAIL` line naming the file — not a swallowed error buried in scrollback."""
step("Run the seed runner on the deliberately-failing font-evidence fixture")
val (out, err, code) = run_seed_test("scripts/check/fixtures/font_evidence_runner_fail_spec.spl", 60)
val report = out + err
capture_evidence("fail_spec_report", report)

step("Confirm the build fails closed and names the failing fixture")
expect(code).to_equal(1)
expect(report).to_contain("1 example, 1 failure")
expect(report).to_contain("FAIL scripts/check/fixtures/font_evidence_runner_fail_spec.spl")
Then_capture_matches("fail_spec_report", report)
```

</details>

#### passes the build when every example in a spec is green

**Manual warnings:**
- invalid manual visibility metadata: # @manual_section: Single-file pass/fail contract (expected show, folded, detail, or skip)


- passes the build when every example in a spec is green
   - Protocol capture: after_step
- Run the seed runner on a minimal green fixture
   - Protocol capture: after_step
- Confirm the build passes and names the green fixture
   - Protocol capture: after_step
   - Evidence: protocol response verified by 1 expected check
   - Expected: code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("passes the build when every example in a spec is green")
"""The operator runs the runner against a minimal fixture whose single expectation holds. CI must see a zero exit and a `PASS` line naming the file."""
step("Run the seed runner on a minimal green fixture")
val (out, err, code) = run_seed_test("test/fixtures/test_runner_system/green_spec.spl", 60)
val report = out + err
capture_evidence("green_spec_report", report)

step("Confirm the build passes and names the green fixture")
expect(code).to_equal(0)
expect(report).to_contain("1 example, 0 failures")
expect(report).to_contain("PASS test/fixtures/test_runner_system/green_spec.spl")
Then_capture_matches("green_spec_report", report)
```

</details>

<details>
<summary>Advanced: refuses a synthetic pass when a spec executes zero real examples</summary>

#### refuses a synthetic pass when a spec executes zero real examples

**Manual warnings:**
- invalid manual visibility metadata: # @manual_section: Guardrails against false-green results (expected show, folded, detail, or skip)


- refuses a synthetic pass when a spec executes zero real examples
- Run the seed runner on a spec containing only a pending() placeholder
- Confirm the runner fails closed instead of trusting the misleading summary line
   - Expected: code equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("refuses a synthetic pass when a spec executes zero real examples")
"""A spec whose only content is a bare `pending()` placeholder must not read as a build pass just because the interpreter's own aggregate summary line miscounts it as `1 example, 0 failures`. Regression coverage for doc/08_tracking/bug/test_runner_zero_executed_single_file_greenwash_2026-07-17.md."""
step("Run the seed runner on a spec containing only a pending() placeholder")
val (out, err, code) = run_seed_test("scripts/check/fixtures/font_evidence_runner_empty_spec.spl", 60)
val report = out + err
capture_evidence("empty_spec_report", report)

step("Confirm the runner fails closed instead of trusting the misleading summary line")
expect(code).to_equal(1)
expect(report).to_contain("error: test-runner: no examples executed")
Then_capture_matches("empty_spec_report", report)
```

</details>


</details>

<details>
<summary>Advanced: cannot yet report a directory scan within an operator-reasonable time</summary>

#### cannot yet report a directory scan within an operator-reasonable time

- cannot yet report a directory scan within an operator-reasonable time
- Point the seed runner at a directory of two green fixtures, bounded far past the single-file cost
- Confirm the runner at least discovers both fixture files
- Confirm it does not reach a clean directory summary within the bound (the known gap)
   - Expected: report does not contain `Passed: 2`
   - Expected: timed_out_or_failed is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("cannot yet report a directory scan within an operator-reasonable time")
"""An operator pointing the runner at a directory holding two trivial green fixtures expects a per-file report within seconds — the single-file path above answers in well under a minute. Today the light test daemon fails to start on this seed (`error: semantic: unknown extern function: rt_cli_arg_count`, doc/08_tracking/bug/host_toolchain_seed_pinned_lint_fmt_doccov_unrunnable_2026-07-17.md), so the runner falls back to an unassisted direct interpreter run that discovers both files but does not reach a `Files: N` / `Passed: N` summary even after many times the single-file budget. This scenario records that gap honestly instead of asserting a directory result nobody can currently observe."""
step("Point the seed runner at a directory of two green fixtures, bounded far past the single-file cost")
val (out, err, code) = run_seed_test_dir("test/fixtures/test_runner_system", 45)
val report = out + err
capture_evidence("directory_scan_report", report)

step("Confirm the runner at least discovers both fixture files")
expect(report).to_contain("Running 2 test file(s)")

step("Confirm it does not reach a clean directory summary within the bound (the known gap)")
expect(report.contains("Passed: 2")).to_equal(false)
val timed_out_or_failed = code != 0
expect(timed_out_or_failed).to_equal(true)
```

</details>


</details>

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

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `1b9f6070d558a707f1b5c07b0ce3f6fb3848fa00026521535d4fca42eddc5637`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `1b9f6070d558a707f1b5c07b0ce3f6fb3848fa00026521535d4fca42eddc5637`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `1b9f6070d558a707f1b5c07b0ce3f6fb3848fa00026521535d4fca42eddc5637`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **91/100**; effective score: **91/100**; blockers: **0**.

SSpec documentization score: 91/100
source: test/03_system/app/test_runner/test_runner_contract_system_spec.spl
mirror: doc/06_spec/03_system/app/test_runner/test_runner_contract_system_spec.md (current)
findings: 3 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=100 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/app/test_runner/test_runner_contract_system_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/app/test_runner/test_runner_contract_system_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/app/test_runner/test_runner_contract_system_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 3 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
<!-- sspec-maintain:scorecard:end -->

# @req REQ-TESTRUNNER-NO-EXAMPLES-FAIL-CLOSED

> 0 examples executed must never exit 0 — the test-runner's fail-closed rule.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 12 | 12 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# @req REQ-TESTRUNNER-NO-EXAMPLES-FAIL-CLOSED

0 examples executed must never exit 0 — the test-runner's fail-closed rule.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/test_runner_new/no_examples_fail_closed_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

0 examples executed must never exit 0 — the test-runner's fail-closed rule.

Audience: anyone editing `src/app/test_runner_new/no_examples_gate.spl`,
`test_runner_client.spl`'s `fail_closed_on_no_examples`, or
`src/app/test_daemon/light_daemon.spl`.

Why this spec exists (REPRODUCER). Measured 2026-08-21: two concurrent
`simple test <spec>` processes in the SAME worktree could make one of them
return rc=0 with ZERO test output — no examples, no failure, not even a
`SPEC FILE VERDICT:` line. 42 of 122 spec logs in a 2-way sharded run came
back that way; a serial re-run of the same specs was clean. Because the
client returned the child's exit code verbatim, every sweep that reads exit
codes scored those 42 as PASSED. That is a silent false green, and it is the
worst failure a test runner can have.

The output-losing mechanism was in the shared light-daemon lane (duplicate
daemons racing to answer the same request; closed by `claim_lane` in
light_daemon.spl). This spec pins the OTHER half — the rule that makes any
such loss loud instead of green, whichever lane loses the output next time.

Assertions here are ALGORITHMIC (exit code as a function of output + child
code), never wall-clock, so they are stable on a contended host.

## Scenarios

### test-runner 0-examples fail-closed rule

### recognising that something actually ran

#### sees a verdict line in a real run's output

- sees a verdict line in a real run's output


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("sees a verdict line in a real run's output")
expect(output_has_verdict(REAL_VERDICT)).to_be_true()
```

</details>

#### sees no verdict line in empty output

- sees no verdict line in empty output


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("sees no verdict line in empty output")
expect(output_has_verdict("")).to_be_false()
```

</details>

#### does not accept unrelated chatter as evidence of a run

- does not accept unrelated chatter as evidence of a run


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("does not accept unrelated chatter as evidence of a run")
# Warnings alone are exactly what a lost-output run leaves behind.
expect(output_has_verdict("[gc-warning] higher layer module\n")).to_be_false()
```

</details>

#### names the marker every lane agrees on

- names the marker every lane agrees on
   - Expected: NO_EXAMPLES_VERDICT_MARKER equals `SPEC FILE VERDICT:`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("names the marker every lane agrees on")
expect(NO_EXAMPLES_VERDICT_MARKER).to_equal("SPEC FILE VERDICT:")
```

</details>

### the exit code as a function of output and child code

#### rewrites a silent green to a failure

- rewrites a silent green to a failure
   - Expected: no_examples_exit_code("", 0) equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("rewrites a silent green to a failure")
# THE REGRESSION: rc=0 with zero output used to be returned as 0.
expect(no_examples_exit_code("", 0)).to_equal(1)
```

</details>

#### rewrites a warnings-only green to a failure

- rewrites a warnings-only green to a failure
   - Expected: no_examples_exit_code("[gc-warning] x\n", 0) equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("rewrites a warnings-only green to a failure")
expect(no_examples_exit_code("[gc-warning] x\n", 0)).to_equal(1)
```

</details>

#### keeps a genuine pass green

- keeps a genuine pass green
   - Expected: no_examples_exit_code(REAL_VERDICT, 0) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("keeps a genuine pass green")
expect(no_examples_exit_code(REAL_VERDICT, 0)).to_equal(0)
```

</details>

#### passes a real failure through untouched

- passes a real failure through untouched
   - Expected: no_examples_exit_code(REAL_VERDICT, 3) equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("passes a real failure through untouched")
expect(no_examples_exit_code(REAL_VERDICT, 3)).to_equal(3)
```

</details>

#### never masks a non-zero code even with no verdict line

- never masks a non-zero code even with no verdict line
   - Expected: no_examples_exit_code("", 139) equals `139`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("never masks a non-zero code even with no verdict line")
# A crash that printed nothing must stay its own exit code, not
# become a generic 1 — the diagnosis is in that number.
expect(no_examples_exit_code("", 139)).to_equal(139)
```

</details>

### classifying the silent green itself

#### flags rc=0 with no verdict line

- flags rc=0 with no verdict line


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("flags rc=0 with no verdict line")
expect(no_examples_is_silent_green("", 0)).to_be_true()
```

</details>

#### does not flag a real pass

- does not flag a real pass


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("does not flag a real pass")
expect(no_examples_is_silent_green(REAL_VERDICT, 0)).to_be_false()
```

</details>

#### does not flag an already-loud failure

- does not flag an already-loud failure


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("does not flag an already-loud failure")
expect(no_examples_is_silent_green("", 1)).to_be_false()
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 12 |
| Active scenarios | 12 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-APP`
- `REQ-TESTRUNNER-NO-EXAMPLES-FAIL-CLOSED`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `77c6215d87563fa054d79d891bbb31351dd15c30f3f194c9c048dd2190ee5a49`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `77c6215d87563fa054d79d891bbb31351dd15c30f3f194c9c048dd2190ee5a49`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `77c6215d87563fa054d79d891bbb31351dd15c30f3f194c9c048dd2190ee5a49`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/app/test_runner_new/no_examples_fail_closed_spec.spl
mirror: doc/06_spec/01_unit/app/test_runner_new/no_examples_fail_closed_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/app/test_runner_new/no_examples_fail_closed_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/test_runner_new/no_examples_fail_closed_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/test_runner_new/no_examples_fail_closed_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 5 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/app/test_runner_new/no_examples_fail_closed_spec.spl:51:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'sees a verdict line in a real run's output' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/test_runner_new/no_examples_fail_closed_spec.spl:56:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'sees no verdict line in empty output' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/test_runner_new/no_examples_fail_closed_spec.spl:61:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'does not accept unrelated chatter as evidence of a run' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

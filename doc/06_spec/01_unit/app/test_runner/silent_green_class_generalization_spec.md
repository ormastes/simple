# silent_green_class_generalization_spec

> Four different ways a test run can fail to produce evidence. A verifier

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# silent_green_class_generalization_spec

Four different ways a test run can fail to produce evidence. A verifier

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/test_runner/silent_green_class_generalization_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Four different ways a test run can fail to produce evidence. A verifier
    reading only the exit code must be told the truth in every one of them.

## Scenarios

### No verdict is never green

#### treats a zero-example run as a failure, not a pass

- treats a zero-example run as a failure, not a pass
- A runner that discovers nothing and exits 0 with no counts
- Judge the run
   - Expected: guard_exit(fixture) equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("treats a zero-example run as a failure, not a pass")
step("A runner that discovers nothing and exits 0 with no counts")
val fixture = write_fixture("zero_examples", "echo 'No tests discovered'\nexit 0\n")

step("Judge the run")
expect(guard_exit(fixture)).to_equal(1)
```

</details>

#### treats a loader failure with no summary as a failure

- treats a loader failure with no summary as a failure
- A runner whose module graph fails to load, leaving no summary behind
- Judge the run
   - Expected: guard_exit(fixture) equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("treats a loader failure with no summary as a failure")
step("A runner whose module graph fails to load, leaving no summary behind")
val fixture = write_fixture("loader_fail", "echo 'error: unresolved name: describe'\nexit 0\n")

step("Judge the run")
expect(guard_exit(fixture)).to_equal(1)
```

</details>

#### reports a signal-killed run as ERROR rather than a result

- reports a signal-killed run as ERROR rather than a result
- A runner killed by SIGTERM mid-run, as the 60s CPU guard does
- Judge the run
   - Expected: guard_exit(fixture) equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("reports a signal-killed run as ERROR rather than a result")
step("A runner killed by SIGTERM mid-run, as the 60s CPU guard does")
val fixture = write_fixture("sigterm", "echo 'warning: noise'\nkill -TERM $$\n")

step("Judge the run")
expect(guard_output(fixture)).to_contain("VERDICT_E")
expect(guard_exit(fixture)).to_equal(2)
```

</details>

#### leaves a genuinely red run classified as a real result

- leaves a genuinely red run classified as a real result
- A runner that printed its counts and failed honestly
- The gate does not relabel a real failure as missing evidence
   - Expected: guard_exit(fixture) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("leaves a genuinely red run classified as a real result")
step("A runner that printed its counts and failed honestly")
val fixture = write_fixture("honest_red", "echo 'Results: 4 total, 3 passed, 1 failed'\nexit 1\n")

step("The gate does not relabel a real failure as missing evidence")
expect(guard_output(fixture)).to_contain("VERDICT_P")
expect(guard_exit(fixture)).to_equal(0)
```

</details>

#### refuses to pass when it was given nothing to check

- refuses to pass when it was given nothing to check
- Invoke the gate with no targets at all
- A run that checked nothing is ERROR, never a vacuous pass
   - Expected: code equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("refuses to pass when it was given nothing to check")
step("Invoke the gate with no targets at all")
val (out, err, code) = process_run("sh", [
    "-c",
    "o=$(sh {GUARD} 2>&1); r=$?; printf '%s' \"$o\" | tail -1 | sed '{SANITIZE}'; exit $r",
])

step("A run that checked nothing is ERROR, never a vacuous pass")
expect(out).to_contain("VERDICT_E — nothing was checked")
expect(code).to_equal(2)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
- `REQ-TESTRUNNER-VERDICT-001`
- `REQ-SSPEC-APP`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `3a7870ba7a808d3e6937af0672cae0bc6074a662dba97ec17f2b695dabbacf1e`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `3a7870ba7a808d3e6937af0672cae0bc6074a662dba97ec17f2b695dabbacf1e`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `3a7870ba7a808d3e6937af0672cae0bc6074a662dba97ec17f2b695dabbacf1e`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **80/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/app/test_runner/silent_green_class_generalization_spec.spl
mirror: doc/06_spec/01_unit/app/test_runner/silent_green_class_generalization_spec.md (current)
findings: 7 blockers: 1
  narrative=100 structure=100 oracle=70
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=80; blocker cap makes effective=49
doc/06_spec/01_unit/app/test_runner/silent_green_class_generalization_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/test_runner/silent_green_class_generalization_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/test_runner/silent_green_class_generalization_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 5 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/app/test_runner/silent_green_class_generalization_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 2 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/app/test_runner/silent_green_class_generalization_spec.spl:66:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'treats a zero-example run as a failure, not a pass' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/test_runner/silent_green_class_generalization_spec.spl:75:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'treats a loader failure with no summary as a failure' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/test_runner/silent_green_class_generalization_spec.spl:84:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reports a signal-killed run as ERROR rather than a result' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

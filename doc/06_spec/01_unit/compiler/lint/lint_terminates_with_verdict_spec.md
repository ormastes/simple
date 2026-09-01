# Lint Terminates And Says So

> `sh scripts/check/lint-cached.shs src/compiler/50.mir/hwir/zca_rows.spl` was

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Lint Terminates And Says So

`sh scripts/check/lint-cached.shs src/compiler/50.mir/hwir/zca_rows.spl` was

## At a Glance

| Field | Value |
|-------|-------|
| Category | Tooling |
| Status | Implemented |
| Source | `test/01_unit/compiler/lint/lint_terminates_with_verdict_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and Audience

`sh scripts/check/lint-cached.shs src/compiler/50.mir/hwir/zca_rows.spl` was
killed by a 600-second budget with no verdict line, and was filed as a lint
hang. It is not a hang. Measurement showed the linter runs to completion and
prints an explicit verdict; that file is simply far past the budget it was given.

The distinction matters because the two diagnoses have opposite fixes. A hang is
a deadlock to break. A cost problem is either optimised or given an honest,
written bound -- and pretending to "fix a hang" that was never a hang would
leave the real bound undocumented and the next agent equally stuck.

This spec pins the half that is cheap to check and easy to regress: for a file
it can process, lint finishes and reports a verdict rather than exiting silently.

## Scope and Preconditions

Drives the real `bin/simple lint` as a subprocess over a small committed
fixture. The fixture's single function is a deeply nested call expression --
the shape that dominates cost in the hwir row builders -- kept small enough to
lint quickly.

Measured cost model is recorded in the bug document, not asserted here: wall
time depends on machine load, and a timing assertion would be flaky rather than
informative.

## Primary Workflow

Lint the fixture, then read the verdict off stdout. The oracle is the presence
of an explicit result line, never the exit status on its own.

## Recovery and Troubleshooting

A failure with empty output and a non-zero status is the timeout signature, not
a lint finding. Re-run with a longer budget and record the machine load before
concluding anything about the linter.

## Compatibility and Limitations

Only asserts termination and reporting. It deliberately does not assert a time
bound; see the bug document for measured numbers and the load they were taken
under.

## Scenarios

### Lint reports a verdict instead of ending silently

#### finishes a deeply nested expression file and states the outcome

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- finishes a deeply nested expression file and states the outcome
- Run bin/simple lint over the nested-expression fixture
- Read the explicit verdict sentence the linter prints when it completes
- Confirm the run ended cleanly, with the exit status as corroboration rather than the oracle
   - Expected: code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("finishes a deeply nested expression file and states the outcome")
step("Run bin/simple lint over the nested-expression fixture")
val (out, err, code) = process_run("bin/simple", ["lint", LINT_FIXTURE])

step("Read the explicit verdict sentence the linter prints when it completes")
expect(out).to_contain("Lint passed")

step("Confirm the run ended cleanly, with the exit status as corroboration rather than the oracle")
expect(code).to_equal(0)
```

</details>

#### reports a clean file as clean, and says so in words

- reports a clean file as clean, and says so in words
- Lint the same fixture and look for the verdict sentence
- A silent exit 0 is indistinguishable from a skipped run, so require the sentence
   - Expected: code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("reports a clean file as clean, and says so in words")
step("Lint the same fixture and look for the verdict sentence")
val (out, err, code) = process_run("bin/simple", ["lint", LINT_FIXTURE])

step("A silent exit 0 is indistinguishable from a skipped run, so require the sentence")
expect(out).to_contain("Lint passed")
expect(code).to_equal(0)
```

</details>

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

- `REQ-SSPEC-UNIT`
- `REQ-LINT-COST-001`
- `REQ-SSPEC-COMPILER`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `33d7e1ce3adab039e3509db5e151c27039e993665d6e8e0d3013b64c5bcca9b2`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `33d7e1ce3adab039e3509db5e151c27039e993665d6e8e0d3013b64c5bcca9b2`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `33d7e1ce3adab039e3509db5e151c27039e993665d6e8e0d3013b64c5bcca9b2`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/compiler/lint/lint_terminates_with_verdict_spec.spl
mirror: doc/06_spec/01_unit/compiler/lint/lint_terminates_with_verdict_spec.md (current)
findings: 5 blockers: 1
  narrative=100 structure=100 oracle=80
  traceability=60 evidence=80 coverage=100 maintainability=90
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=86; blocker cap makes effective=49
doc/06_spec/01_unit/compiler/lint/lint_terminates_with_verdict_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
test/01_unit/compiler/lint/lint_terminates_with_verdict_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/lint/lint_terminates_with_verdict_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 2 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/compiler/lint/lint_terminates_with_verdict_spec.spl:68:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'finishes a deeply nested expression file and states the outcome' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/lint/lint_terminates_with_verdict_spec.spl:80:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reports a clean file as clean, and says so in words' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

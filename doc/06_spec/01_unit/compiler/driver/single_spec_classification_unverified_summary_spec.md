# single_spec_classification_unverified_summary_spec

> val (stdout, stderr, code) = process_run_bounded(

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# single_spec_classification_unverified_summary_spec

val (stdout, stderr, code) = process_run_bounded(

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/driver/single_spec_classification_unverified_summary_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

val (stdout, stderr, code) = process_run_bounded(
        SIMPLE_BIN,
        ["test", "--no-session-daemon", "--timeout", "{budget_secs}", spec_path],
        (budget_secs + 240) * 1000,
        4000000)
    (stdout + "\n" + stderr, code)

fn last_verdict_word(output: text) -> text:
    """The runner's final PASS/FAIL/UNVERIFIED banner line, as a bare word.

    Scanned rather than grepped for a substring: the word PASS appears in
    hundreds of lint/warning lines this runner emits before its summary, so a
    plain `.contains("PASS")` is not an oracle at all.

## Scenarios

### single-spec runner classifies an unverified child in its summary

#### prints UNVERIFIED, not PASS, when the child is killed at its budget

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- prints UNVERIFIED, not PASS, when the child is killed at its budget


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("prints UNVERIFIED, not PASS, when the child is killed at its budget")
"""A spec that never terminates produces no verified result. The
summary must say so in words, not print PASS with a 0-total tally."""
val p = "/tmp/single_spec_classification_hang_spec.spl"
assert_true(write_temp_spec(p, "use std.spec\n\ndescribe \"hang\":\n    it \"never finishes\":\n        var i = 0\n        while true:\n            i = i + 1\n"))
val (out, rc) = run_single(p, 10)
# Non-vacuity: if the runner produced no banner at all, the assertions
# below would be comparing NONE to PASS and passing for the wrong
# reason. Require that a summary was actually reached.
assert_true(out.contains("Results:"))
assert_equal(last_verdict_word(out), "UNVERIFIED")
# Exit code 2 is the pre-existing contract for an unverified run; it
# must remain distinct from both 0 (green) and 1 (real failure).
assert_equal(rc, 2)
```

</details>

#### still prints PASS for a spec that genuinely passes

- still prints PASS for a spec that genuinely passes


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("still prints PASS for a spec that genuinely passes")
"""Boundary guard: the UNVERIFIED branch must fire only on the
TIMEOUT/TERMINATED classes, never on an ordinary green run."""
val p = "/tmp/single_spec_classification_ok_spec.spl"
assert_true(write_temp_spec(p, "use std.spec\n\ndescribe \"ok\":\n    it \"adds\":\n        expect(1 + 1).to_equal(2)\n"))
val (out, rc) = run_single(p, 120)
assert_true(out.contains("Results:"))
assert_equal(last_verdict_word(out), "PASS")
assert_equal(rc, 0)
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
- `REQ-TEST-RUNNER-UNVERIFIED-SUMMARY`
- `REQ-SSPEC-COMPILER`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `423a5a6a32be8ea8e5e015cf945ee1cb4758b48654c92b4841650086d8c407d3`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `423a5a6a32be8ea8e5e015cf945ee1cb4758b48654c92b4841650086d8c407d3`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `423a5a6a32be8ea8e5e015cf945ee1cb4758b48654c92b4841650086d8c407d3`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/compiler/driver/single_spec_classification_unverified_summary_spec.spl
mirror: doc/06_spec/01_unit/compiler/driver/single_spec_classification_unverified_summary_spec.md (current)
findings: 5 blockers: 1
  narrative=100 structure=100 oracle=100
  traceability=60 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=88; blocker cap makes effective=49
doc/06_spec/01_unit/compiler/driver/single_spec_classification_unverified_summary_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/driver/single_spec_classification_unverified_summary_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/driver/single_spec_classification_unverified_summary_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 2 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/compiler/driver/single_spec_classification_unverified_summary_spec.spl:74:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'prints UNVERIFIED, not PASS, when the child is killed at its budget' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/driver/single_spec_classification_unverified_summary_spec.spl:91:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'still prints PASS for a spec that genuinely passes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

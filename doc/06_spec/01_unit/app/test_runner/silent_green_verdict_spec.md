# silent_green_verdict_spec

> A release engineer relies on `bin/simple test <spec>` to decide whether a

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# silent_green_verdict_spec

A release engineer relies on `bin/simple test <spec>` to decide whether a

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/test_runner/silent_green_verdict_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

A release engineer relies on `bin/simple test <spec>` to decide whether a
    change is safe to land. This scenario proves the runner can no longer
    report success by saying nothing at all.

## Scenarios

### Test runner verdict honesty

#### reports a real pass only when it prints its counts

- reports a real pass only when it prints its counts
- Stand up a runner that prints an explicit results line and exits 0
- Ask the verdict gate to judge that run
- The gate accepts it, because the counts are on the record
   - Expected: code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("reports a real pass only when it prints its counts")
step("Stand up a runner that prints an explicit results line and exits 0")
val fixture = write_fixture("counts", "echo 'warning: noise'\necho 'Results: 4 total, 4 passed, 0 failed'\nexit 0\n")

step("Ask the verdict gate to judge that run")
val (output, code) = run_guard(fixture)

step("The gate accepts it, because the counts are on the record")
expect(output).to_contain("PASS")
expect(code).to_equal(0)
```

</details>

#### rejects a run that printed only warnings and exited zero

- rejects a run that printed only warnings and exited zero
- Reproduce the incident: warnings on stderr, no verdict, exit 0
- Ask the verdict gate to judge that run
- The gate calls it a silent green and fails, instead of passing it through
   - Expected: code equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("rejects a run that printed only warnings and exited zero")
step("Reproduce the incident: warnings on stderr, no verdict, exit 0")
val fixture = write_fixture("silent", "echo \"warning: 'export use *' is deprecated\"\necho 'warning: compiler_cross_module_private_symbol_collision'\nexit 0\n")

step("Ask the verdict gate to judge that run")
val (output, code) = run_guard(fixture)

step("The gate calls it a silent green and fails, instead of passing it through")
expect(output).to_contain("FAIL")
expect(output).to_contain("silent green")
expect(code).to_equal(1)
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
- `REQ-TESTRUNNER-VERDICT-001`
- `REQ-SSPEC-APP`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `8d2be8165edc59b277da3ddee979b2efbb8a3f25eeb49b007c539ba10bab203c`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `8d2be8165edc59b277da3ddee979b2efbb8a3f25eeb49b007c539ba10bab203c`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `8d2be8165edc59b277da3ddee979b2efbb8a3f25eeb49b007c539ba10bab203c`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **84/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/app/test_runner/silent_green_verdict_spec.spl
mirror: doc/06_spec/01_unit/app/test_runner/silent_green_verdict_spec.md (current)
findings: 6 blockers: 1
  narrative=100 structure=100 oracle=80
  traceability=60 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=84; blocker cap makes effective=49
doc/06_spec/01_unit/app/test_runner/silent_green_verdict_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/test_runner/silent_green_verdict_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/test_runner/silent_green_verdict_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/app/test_runner/silent_green_verdict_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 2 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/app/test_runner/silent_green_verdict_spec.spl:54:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reports a real pass only when it prints its counts' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/test_runner/silent_green_verdict_spec.spl:67:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects a run that printed only warnings and exited zero' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

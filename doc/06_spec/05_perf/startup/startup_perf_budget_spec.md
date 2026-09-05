# Startup Perf Budget Specification

> Tests covering startup perf budget lane.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Startup Perf Budget Specification

## Scenarios

### startup perf budget lane

#### the detector's own selftest still covers all four fixtures

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- the detector's own selftest still covers all four fixtures
- Run the detector in --selftest mode; its fixtures are the positive control for this whole lane
- must-FAIL (0ms budget), must-PASS (absurd budget) and must-ERROR (missing budgets file) must all still be exercised
- A selftest that cannot prove its own fixtures is fatal upstream, so it must exit 0 here
   - Expected: code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("the detector's own selftest still covers all four fixtures")
step("Run the detector in --selftest mode; its fixtures are the positive control for this whole lane")
val (out, code) = run_sh("sh " + CHECK + " --selftest 2>&1")

step("must-FAIL (0ms budget), must-PASS (absurd budget) and must-ERROR (missing budgets file) must all still be exercised")
expect(out).to_contain("selftest OK: 4 fixture(s)")

step("A selftest that cannot prove its own fixtures is fatal upstream, so it must exit 0 here")
expect(code).to_equal(0)
```

</details>

#### a real measurement reports a verdict that states what it measured

- a real measurement reports a verdict that states what it measured
- Run the detector for real against the committed budgets
- The verdict is never silent: it is PASS, SKIP or FAIL, and each names itself
   - Expected: named is true
- A PASS must be non-vacuous — it has to say how many commands it measured and with how many samples


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("a real measurement reports a verdict that states what it measured")
step("Run the detector for real against the committed budgets")
val (out, _code) = run_sh("sh " + CHECK + " 2>&1")
val v: text = verdict_of(out)

step("The verdict is never silent: it is PASS, SKIP or FAIL, and each names itself")
val named = v.starts_with("PASS —") or v.starts_with("SKIP —") or v.starts_with("FAIL —")
expect(named).to_equal(true)

step("A PASS must be non-vacuous — it has to say how many commands it measured and with how many samples")
if v.starts_with("PASS —"):
    expect(v).to_contain("lane(s) measured")
    expect(v).to_contain("N=")
```

</details>

#### an unrecognised argument fails closed rather than measuring nothing quietly

- an unrecognised argument fails closed rather than measuring nothing quietly
- Invoke the detector with an argument it does not recognise
- An unactionable invocation is absence of evidence — ERROR, never a pass
- and exit 2, so a caller cannot mistake it for a clean run
   - Expected: code equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("an unrecognised argument fails closed rather than measuring nothing quietly")
# The missing-budgets-file path is covered by the detector's own
# must-ERROR fixture (asserted in ex.1). The reachable-from-here
# fail-closed path is an unknown argument: the script deliberately has
# no flag that selects a different budgets file, so this is the only
# way a caller can hand it something it cannot act on.
step("Invoke the detector with an argument it does not recognise")
val (out, code) = run_sh("sh " + CHECK + " --not-a-real-flag 2>&1")
val v: text = verdict_of(out)

step("An unactionable invocation is absence of evidence — ERROR, never a pass")
expect(v).to_contain("ERROR — nothing was checked")

step("and exit 2, so a caller cannot mistake it for a clean run")
expect(code).to_equal(2)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/05_perf/startup/startup_perf_budget_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering startup perf budget lane.
- startup perf budget lane

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

- `REQ-SSPEC-PERF`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `2b9b4e721b8ede0b3de2a6b7cb4123da96a3ba8d32227a9cf5491bebe3dc29e7`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `2b9b4e721b8ede0b3de2a6b7cb4123da96a3ba8d32227a9cf5491bebe3dc29e7`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `2b9b4e721b8ede0b3de2a6b7cb4123da96a3ba8d32227a9cf5491bebe3dc29e7`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/05_perf/startup/startup_perf_budget_spec.spl
mirror: doc/06_spec/05_perf/startup/startup_perf_budget_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/05_perf/startup/startup_perf_budget_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/05_perf/startup/startup_perf_budget_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/05_perf/startup/startup_perf_budget_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/05_perf/startup/startup_perf_budget_spec.spl:60:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'the detector's own selftest still covers all four fixtures' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/05_perf/startup/startup_perf_budget_spec.spl:72:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'a real measurement reports a verdict that states what it measured' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/05_perf/startup/startup_perf_budget_spec.spl:88:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'an unrecognised argument fails closed rather than measuring nothing quietly' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
